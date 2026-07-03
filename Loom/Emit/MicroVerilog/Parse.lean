import Loom.Emit.MicroVerilog.Ast

/-!
# The µVerilog parser (task 2.3, parse half)

Reads the exact SSA text `Print` emits back into a `Module`, so the
round-trip check (`RoundTrip.lean`) puts the text file — not just the
AST — inside the emission theorem: no trusted pretty-printer.

Design notes:

* **Total, structural.** Line-oriented recursive descent over
  `List (List Char)`; every recursion is structural (on a line list, a
  char list, or a declaration list). No `partial`, no well-founded
  recursion, so the whole parser is kernel-reducible.
* **Restrictive by design.** It accepts exactly the printer's output
  shape (fixed indentation, fixed spacing, ascending init addresses,
  declaration-ordered always-block lines) and returns `none` on anything
  else. Rejecting valid-but-differently-formatted Verilog is a feature:
  only printer output needs to round-trip.
* **SSA pays off.** Because `Print` emits every expression node as its
  own wire, a right-hand side is always a *single* operator over
  identifiers/literals — the expression grammar is non-recursive, and
  expression trees are rebuilt by environment lookup (each generated wire
  is referenced exactly once, so sharing cannot conflate distinct nodes).
* **Widths.** Every wire declaration pins its width, so parsed
  subexpressions carry their widths; width-indexed constructors are
  rebuilt under explicit decidable width checks (`castW`).
* **Memory init.** The printed `initial` block lists all `2^addrWidth`
  words; the parser rebuilds `MemDef.init` as a lookup into that table
  (out-of-range addresses default to `0`, which the semantics never
  reads, since read addresses are `BitVec addrWidth`).
-/

namespace Loom.Emit.MicroVerilog.Parse

open Loom.Emit.MicroVerilog

/-! ## Character-level helpers -/

def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Strip an exact expected prefix. -/
def eat : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | _ :: _, [] => none
  | p :: ps, c :: cs => if c == p then eat ps cs else none

/-- Strip an exact expected prefix, given as a string literal. -/
def eatS (s : String) (cs : List Char) : Option (List Char) := eat s.toList cs

def digitsToNat (ds : List Char) : Nat :=
  ds.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0

/-- Parse a decimal numeral (at least one digit). -/
def pNat (cs : List Char) : Option (Nat × List Char) :=
  match cs.span (·.isDigit) with
  | ([], _) => none
  | (ds, rest) => some (digitsToNat ds, rest)

/-- Parse an identifier: `[A-Za-z_][A-Za-z0-9_]*`. -/
def pIdent (cs : List Char) : Option (String × List Char) :=
  match cs with
  | [] => none
  | c :: _ =>
    if isIdentStart c then
      match cs.span isIdentChar with
      | (ds, rest) => some (String.ofList ds, rest)
    else none

/-- Split into lines at `'\n'` (inverse of `String.intercalate "\n"`). -/
def splitLinesAux (acc : List Char) : List Char → List (List Char)
  | [] => [acc.reverse]
  | c :: cs =>
    if c == '\n' then acc.reverse :: splitLinesAux [] cs
    else splitLinesAux (c :: acc) cs

def splitLines (s : String) : List (List Char) := splitLinesAux [] s.toList

/-- Consume one exact expected line. -/
def expectLine (s : String) : List (List Char) → Option (List (List Char))
  | [] => none
  | l :: ls => if l == s.toList then some ls else none

/-! ## Parsing context -/

/-- A declared register (name and width), from the `reg [hi:0] r;` lines. -/
structure RegHdr where
  name  : String
  width : Nat
  deriving Repr, DecidableEq

/-- A declared memory, from the `reg [hi:0] m [0:sz];` lines. -/
structure MemHdr where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  deriving Repr, DecidableEq

/-- A declared register together with its parsed reset value. -/
structure RegInit where
  name  : String
  width : Nat
  init  : BitVec width

/-- Wire environment: generated wire name ↦ (width, rebuilt expression). -/
abbrev Env := List (String × Sigma Expr)

/-- Transport an expression along a width equality. -/
def castW {w w' : Nat} (h : w = w') (e : Expr w) : Expr w' := h ▸ e

/-- Resolve an identifier occurring as an operand: a generated wire (in the
environment) or a declared register. -/
def resolveAny (regs : List RegHdr) (env : Env) (x : String) : Option (Sigma Expr) :=
  match env.find? (fun p => p.1 == x) with
  | some p => some p.2
  | none =>
    match regs.find? (fun r => r.name == x) with
    | some r => some ⟨r.width, .reg r.width x⟩
    | none => none

/-- Resolve an identifier at a required width. -/
def resolve (regs : List RegHdr) (env : Env) (x : String) (w : Nat) : Option (Expr w) :=
  match resolveAny regs env x with
  | some ⟨wx, e⟩ => if h : wx = w then some (castW h e) else none
  | none => none

/-! ## Right-hand sides

One operator per line (SSA). Grammar of `wire [w-1:0] n = RHS;` bodies:

    RHS ::= W'dV                          (lit; W = declared width)
          | x                             (zext to declared width)
          | m[a]                          (memRead, m a declared memory)
          | x[hi:lo]                      (slice)
          | ~x                            (not)
          | x OP y                        (OP ∈ & | ^ + - << >> == <)
          | $signed(x) < $signed(y)       (slt)
          | c ? t : f                     (mux)
          | {{k{x[b]}}, x}                (sext, strictly widening)
-/

/-- Build a same-width binary operator. -/
def mkBinW (regs : List RegHdr) (env : Env) (w : Nat) (x y : String)
    (mk : Expr w → Expr w → Expr w) : Option (Expr w) := do
  let a ← resolve regs env x w
  let b ← resolve regs env y w
  pure (mk a b)

/-- Build a comparison (result width 1, operand widths equal). -/
def mkCmp (regs : List RegHdr) (env : Env) (w : Nat) (x y : String)
    (mk : {v : Nat} → Expr v → Expr v → Expr 1) : Option (Expr w) := do
  let ⟨wa, a⟩ ← resolveAny regs env x
  let b ← resolve regs env y wa
  if h : (1 : Nat) = w then pure (castW h (mk a b)) else none

/-- Parse the right-hand side of a wire definition of declared width `w`
(including the terminating `;`, which must end the line). -/
def pRhs (regs : List RegHdr) (mems : List MemHdr) (env : Env)
    (w : Nat) (cs : List Char) : Option (Expr w) :=
  match cs with
  | [] => none
  | c :: _ =>
    if c == '~' then do
      let cs ← eatS "~" cs
      let (x, cs) ← pIdent cs
      let cs ← eatS ";" cs
      guard cs.isEmpty
      let a ← resolve regs env x w
      pure (.not a)
    else if c == '$' then do
      let cs ← eatS "$signed(" cs
      let (x, cs) ← pIdent cs
      let cs ← eatS ") < $signed(" cs
      let (y, cs) ← pIdent cs
      let cs ← eatS ");" cs
      guard cs.isEmpty
      mkCmp regs env w x y (fun a b => .slt a b)
    else if c == '{' then do
      -- {{k{x[b]}}, x};  (sign extension, strictly widening)
      let cs ← eatS "{{" cs
      let (k, cs) ← pNat cs
      let cs ← eatS "{" cs
      let (x, cs) ← pIdent cs
      let cs ← eatS "[" cs
      let (b, cs) ← pNat cs
      let cs ← eatS "]}}, " cs
      let (x2, cs) ← pIdent cs
      let cs ← eatS "};" cs
      guard cs.isEmpty
      guard (x2 == x)
      let ⟨wx, a⟩ ← resolveAny regs env x
      guard (b + 1 == wx && wx + k == w && wx < w)
      pure (.sext a w)
    else if c.isDigit then do
      -- W'dV;
      let (wl, cs) ← pNat cs
      let cs ← eatS "'d" cs
      let (v, cs) ← pNat cs
      let cs ← eatS ";" cs
      guard cs.isEmpty
      guard (wl == w)
      pure (.lit (BitVec.ofNat w v))
    else do
      let (x, cs) ← pIdent cs
      match cs with
      | [';'] => do
        -- bare identifier: zero-extend/truncate to the declared width
        let ⟨_, a⟩ ← resolveAny regs env x
        pure (.zext a w)
      | '[' :: cs =>
        match cs with
        | [] => none
        | c2 :: _ =>
          if c2.isDigit then do
            -- x[hi:lo];  (slice)
            let (hi, cs) ← pNat cs
            let cs ← eatS ":" cs
            let (lo, cs) ← pNat cs
            let cs ← eatS "];" cs
            guard cs.isEmpty
            let ⟨_, a⟩ ← resolveAny regs env x
            guard (lo ≤ hi && hi + 1 - lo == w)
            pure (.slice a lo w)
          else do
            -- m[a];  (asynchronous memory read)
            let (adr, cs) ← pIdent cs
            let cs ← eatS "];" cs
            guard cs.isEmpty
            let mh ← mems.find? (fun m => m.name == x)
            let a ← resolve regs env adr mh.addrWidth
            if h : mh.dataWidth = w then
              pure (castW h (.memRead mh.dataWidth x a))
            else none
      | ' ' :: cs =>
        match cs.span (fun c => c != ' ') with
        | (op, cs) => do
          let cs ← eatS " " cs
          let (y, cs) ← pIdent cs
          if op == ['?'] then do
            -- c ? t : f;
            let cs ← eatS " : " cs
            let (z, cs) ← pIdent cs
            let cs ← eatS ";" cs
            guard cs.isEmpty
            let cnd ← resolve regs env x 1
            let t ← resolve regs env y w
            let f ← resolve regs env z w
            pure (.mux cnd t f)
          else do
            let cs ← eatS ";" cs
            guard cs.isEmpty
            match String.ofList op with
            | "&"  => mkBinW regs env w x y (fun a b => .and a b)
            | "|"  => mkBinW regs env w x y (fun a b => .or a b)
            | "^"  => mkBinW regs env w x y (fun a b => .xor a b)
            | "+"  => mkBinW regs env w x y (fun a b => .add a b)
            | "-"  => mkBinW regs env w x y (fun a b => .sub a b)
            | "<<" => mkBinW regs env w x y (fun a b => .shl a b)
            | ">>" => mkBinW regs env w x y (fun a b => .shr a b)
            | "==" => mkCmp regs env w x y (fun a b => .eq a b)
            | "<"  => mkCmp regs env w x y (fun a b => .ult a b)
            | _    => none
      | _ => none

/-! ## Module frame -/

/-- Output port lines: `  output wire [hi:0] name,` … last one without the
comma, then the closing `);` line. -/
def pOutPorts : List (List Char) → Option (List (String × Nat) × List (List Char))
  | [] => none
  | l :: ls => do
    let cs ← eatS "  output wire [" l
    let (hi, cs) ← pNat cs
    let cs ← eatS ":0] " cs
    let (nm, cs) ← pIdent cs
    match cs with
    | [','] => do
      let (rest, ls) ← pOutPorts ls
      pure ((nm, hi + 1) :: rest, ls)
    | [] => do
      let ls ← expectLine ");" ls
      pure ([(nm, hi + 1)], ls)
    | _ => none

/-- `module name(` / `  input wire clk,` / `  input wire rst[,]` / ports. -/
def pHeader : List (List Char) →
    Option (String × List (String × Nat) × List (List Char))
  | l1 :: l2 :: l3 :: ls => do
    let cs ← eatS "module " l1
    let (nm, cs) ← pIdent cs
    guard (cs == ['('])
    guard (l2 == "  input wire clk,".toList)
    if l3 == "  input wire rst".toList then do
      let ls ← expectLine ");" ls
      pure (nm, [], ls)
    else do
      guard (l3 == "  input wire rst,".toList)
      let (outs, ls) ← pOutPorts ls
      pure (nm, outs, ls)
  | _ => none

/-- Register and memory declarations (`  reg [hi:0] r;` and
`  reg [hi:0] m [0:sz];`), in printed order. Stops at the first
non-declaration line. -/
def pDecls (rs : List RegHdr) (ms : List MemHdr) :
    List (List Char) → Option (List RegHdr × List MemHdr × List (List Char))
  | [] => none
  | l :: ls =>
    match eatS "  reg [" l with
    | none => some (rs.reverse, ms.reverse, l :: ls)
    | some cs =>
      match (do
        let (hi, cs) ← pNat cs
        let cs ← eatS ":0] " cs
        let (nm, cs) ← pIdent cs
        pure (hi, nm, cs) : Option (Nat × String × List Char)) with
      | none => none
      | some (hi, nm, cs) =>
        match cs with
        | [';'] => pDecls (⟨nm, hi + 1⟩ :: rs) ms ls
        | _ =>
          match (do
            let cs ← eatS " [0:" cs
            let (sz, cs) ← pNat cs
            let cs ← eatS "];" cs
            guard cs.isEmpty
            let aw := Nat.log2 (sz + 1)
            guard (2 ^ aw == sz + 1)
            pure aw : Option Nat) with
          | none => none
          | some aw => pDecls rs (⟨nm, aw, hi + 1⟩ :: ms) ls

/-- Entries of one `initial` block: `    m[i] = dw'dV;` with ascending
addresses starting at `i`, up to the closing `  end` line (consumed). -/
def pInitEntries (nm : String) (dw : Nat) (i : Nat) (acc : List Nat) :
    List (List Char) → Option (List Nat × List (List Char))
  | [] => none
  | l :: ls =>
    if l == "  end".toList then some (acc.reverse, ls)
    else
      match (do
        let cs ← eatS "    " l
        let (x, cs) ← pIdent cs
        guard (x == nm)
        let cs ← eatS "[" cs
        let (a, cs) ← pNat cs
        guard (a == i)
        let cs ← eatS "] = " cs
        let (wl, cs) ← pNat cs
        guard (wl == dw)
        let cs ← eatS "'d" cs
        let (v, cs) ← pNat cs
        let cs ← eatS ";" cs
        guard cs.isEmpty
        pure v : Option Nat) with
      | none => none
      | some v => pInitEntries nm dw (i + 1) (v :: acc) ls

/-- One `initial begin … end` block per declared memory, in order; each
must list exactly `2^addrWidth` words. -/
def pInits : List MemHdr → List (List Char) →
    Option (List (MemHdr × List Nat) × List (List Char))
  | [], ls => some ([], ls)
  | m :: ms, ls => do
    let ls ← expectLine "  initial begin" ls
    let (tbl, ls) ← pInitEntries m.name m.dataWidth 0 [] ls
    guard (tbl.length == 2 ^ m.addrWidth)
    let (rest, ls) ← pInits ms ls
    pure ((m, tbl) :: rest, ls)

/-- SSA wire definitions `  wire [hi:0] n = RHS;`, extending the
environment; stops at the first non-wire line. -/
def pWires (regs : List RegHdr) (mems : List MemHdr) (env : Env) :
    List (List Char) → Option (Env × List (List Char))
  | [] => none
  | l :: ls =>
    match eatS "  wire [" l with
    | none => some (env, l :: ls)
    | some cs =>
      match (do
        let (hi, cs) ← pNat cs
        let cs ← eatS ":0] " cs
        let (nm, cs) ← pIdent cs
        let cs ← eatS " = " cs
        let e ← pRhs regs mems env (hi + 1) cs
        pure (nm, ⟨hi + 1, e⟩) : Option (String × Sigma Expr)) with
      | none => none
      | some ⟨nm, we⟩ => pWires regs mems ((nm, we) :: env) ls

/-- Reset branch: `      r <= w'dV;` per declared register, in order. -/
def pRegResets : List RegHdr → List (List Char) →
    Option (List RegInit × List (List Char))
  | [], ls => some ([], ls)
  | _ :: _, [] => none
  | r :: rs, l :: ls => do
    let cs ← eatS "      " l
    let (x, cs) ← pIdent cs
    guard (x == r.name)
    let cs ← eatS " <= " cs
    let (wl, cs) ← pNat cs
    guard (wl == r.width)
    let cs ← eatS "'d" cs
    let (v, cs) ← pNat cs
    let cs ← eatS ";" cs
    guard cs.isEmpty
    let (rest, ls) ← pRegResets rs ls
    pure (⟨r.name, r.width, BitVec.ofNat r.width v⟩ :: rest, ls)

/-- Update branch: `      r <= x;` per declared register, in order. -/
def pRegNexts (regs : List RegHdr) (env : Env) : List RegInit →
    List (List Char) → Option (List RegDef × List (List Char))
  | [], ls => some ([], ls)
  | _ :: _, [] => none
  | r :: rs, l :: ls => do
    let cs ← eatS "      " l
    let (x, cs) ← pIdent cs
    guard (x == r.name)
    let cs ← eatS " <= " cs
    let (nx, cs) ← pIdent cs
    let cs ← eatS ";" cs
    guard cs.isEmpty
    let e ← resolve regs env nx r.width
    let (rest, ls) ← pRegNexts regs env rs ls
    pure ({ name := r.name, width := r.width, init := r.init, next := e } :: rest, ls)

/-- One write port of memory `mname`: `      if (en) m[a] <= d;`. `none`
if the line is not a write to `mname` (the caller then moves on to the
next declared memory). -/
def pMemPortLine (regs : List RegHdr) (env : Env) (mname : String)
    (aw dw : Nat) (l : List Char) : Option (WritePort aw dw) := do
  let cs ← eatS "      if (" l
  let (en, cs) ← pIdent cs
  let cs ← eatS ") " cs
  let (x, cs) ← pIdent cs
  guard (x == mname)
  let cs ← eatS "[" cs
  let (adr, cs) ← pIdent cs
  let cs ← eatS "] <= " cs
  let (dt, cs) ← pIdent cs
  let cs ← eatS ";" cs
  guard cs.isEmpty
  let en ← resolve regs env en 1
  let addr ← resolve regs env adr aw
  let data ← resolve regs env dt dw
  pure { en := en, addr := addr, data := data }

/-- The (possibly empty) run of consecutive write-port lines targeting
memory `mname`, in printed = commit order. Stops (without consuming) at
the first line that is not a write to `mname`. -/
def pMemPorts (regs : List RegHdr) (env : Env) (mname : String)
    (aw dw : Nat) : List (List Char) →
    List (WritePort aw dw) × List (List Char)
  | [] => ([], [])
  | l :: ls =>
    match pMemPortLine regs env mname aw dw l with
    | none => ([], l :: ls)
    | some p =>
      let (rest, ls') := pMemPorts regs env mname aw dw ls
      (p :: rest, ls')

/-- Write ports: for each declared memory, in declaration order, its run
of guarded write lines (one per port, in port order; possibly none). -/
def pMemWrites (regs : List RegHdr) (env : Env) :
    List (MemHdr × List Nat) → List (List Char) →
    Option (List MemDef × List (List Char))
  | [], ls => some ([], ls)
  | (m, tbl) :: ms, ls => do
    let (ports, ls) := pMemPorts regs env m.name m.addrWidth m.dataWidth ls
    let (rest, ls) ← pMemWrites regs env ms ls
    pure ({ name := m.name, addrWidth := m.addrWidth, dataWidth := m.dataWidth,
            init := fun a => BitVec.ofNat m.dataWidth (tbl.getD a 0),
            wrPorts := ports } :: rest, ls)

/-- Output assigns: `  assign o = x;` per declared port, in order. -/
def pAssigns (regs : List RegHdr) (env : Env) : List (String × Nat) →
    List (List Char) → Option (List OutDef × List (List Char))
  | [], ls => some ([], ls)
  | _ :: _, [] => none
  | (o, w) :: os, l :: ls => do
    let cs ← eatS "  assign " l
    let (x, cs) ← pIdent cs
    guard (x == o)
    let cs ← eatS " = " cs
    let (v, cs) ← pIdent cs
    let cs ← eatS ";" cs
    guard cs.isEmpty
    let e ← resolve regs env v w
    let (rest, ls) ← pAssigns regs env os ls
    pure ({ name := o, width := w, val := e } :: rest, ls)

/-- Parse a whole printed module from its line list. -/
def parseLines (ls : List (List Char)) : Option Module := do
  let (nm, outs, ls) ← pHeader ls
  let (rhdrs, mhdrs, ls) ← pDecls [] [] ls
  let (minits, ls) ← pInits mhdrs ls
  let (env, ls) ← pWires rhdrs mhdrs [] ls
  let ls ← expectLine "  always @(posedge clk) begin" ls
  let ls ← expectLine "    if (rst) begin" ls
  let (rinits, ls) ← pRegResets rhdrs ls
  let ls ← expectLine "    end else begin" ls
  let (regs, ls) ← pRegNexts rhdrs env rinits ls
  let (mems, ls) ← pMemWrites rhdrs env minits ls
  let ls ← expectLine "    end" ls
  let ls ← expectLine "  end" ls
  let (outDefs, ls) ← pAssigns rhdrs env outs ls
  let ls ← expectLine "endmodule" ls
  guard ls.isEmpty
  pure { name := nm, regs := regs, mems := mems, outs := outDefs }

/-- The µVerilog parser: total inverse (on printer output) of
`Print.print`. Accepts exactly the printed SSA subset; anything else is
`none`. -/
def parse (s : String) : Option Module := parseLines (splitLines s)

end Loom.Emit.MicroVerilog.Parse
