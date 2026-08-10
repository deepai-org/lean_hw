-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Hw.FastEval
import Std.Data.HashMap
import Batteries.Data.List.Basic

/-!
# Certified DAG evaluator

This evaluator structurally interns resolved `FExpr`s across every action,
evaluates the resulting topological node array once per cycle, and lets
actions read node results by index. The lowering is an optimization only:
`checkCertificate` reconstructs a kernel proof that every DAG root denotes
its source tree, and `Verified.cycleOpen_eq` connects every accepted cycle to
`fastCycleOpen`. A hash-table or lowering bug therefore causes preparation to
fail rather than entering the semantic path.
-/

namespace Loom.Hw.DagEval

open Loom.Hw

inductive Node where
  | lit (v : Nat)
  | reg (i : Nat)
  | memRead (base a : Nat)
  | and (a b : Nat) | or (a b : Nat) | xor (a b : Nat)
  | not (mask a : Nat)
  | add (m a b : Nat) | sub (m a b : Nat) | mul (m a b : Nat)
  | shl (w m a b : Nat) | shr (w a b : Nat)
  | eq (a b : Nat) | ult (a b : Nat) | slt (h a b : Nat)
  | mux (c t f : Nat)
  | slice (lo m a : Nat) | zext (m a : Nat) | sext (h m d a : Nat)
  deriving Inhabited, Repr, DecidableEq

def Node.refs : Node → List Nat
  | .lit _ | .reg _ => []
  | .memRead _ a | .not _ a | .slice _ _ a | .zext _ a | .sext _ _ _ a => [a]
  | .and a b | .or a b | .xor a b | .add _ a b | .sub _ a b | .mul _ a b |
    .shl _ _ a b | .shr _ a b | .eq a b | .ult a b | .slt _ a b => [a, b]
  | .mux c t f => [c, t, f]

inductive Act where
  | skip
  | seq (a b : Act)
  | ite (c : Nat) (t e : Act)
  | write (i v : Nat)
  | memWrite (base addr data : Nat)
  deriving Inhabited, Repr

structure Build where
  nodes : Array Node := #[]
  seen : Std.HashMap FExpr Nat := {}

def intern (e : FExpr) (s : Build) : Nat × Build :=
  match s.seen.get? e with
  | some i => (i, s)
  | none =>
    let add (n : Node) (s : Build) : Nat × Build :=
      let i := s.nodes.size
      (i, { nodes := s.nodes.push n, seen := s.seen.insert e i })
    match e with
    | .lit v => add (.lit v) s
    | .reg i => add (.reg i) s
    | .memRead base a =>
        let (ia, s) := intern a s
        add (.memRead base ia) s
    | .and a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.and ia ib) s
    | .or a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.or ia ib) s
    | .xor a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.xor ia ib) s
    | .not mask a =>
        let (ia, s) := intern a s
        add (.not mask ia) s
    | .add m a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.add m ia ib) s
    | .sub m a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.sub m ia ib) s
    | .mul m a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.mul m ia ib) s
    | .shl w m a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.shl w m ia ib) s
    | .shr w a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.shr w ia ib) s
    | .eq a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.eq ia ib) s
    | .ult a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.ult ia ib) s
    | .slt h a b =>
        let (ia, s) := intern a s
        let (ib, s) := intern b s
        add (.slt h ia ib) s
    | .mux c t f =>
        let (ic, s) := intern c s
        let (it, s) := intern t s
        let (if_, s) := intern f s
        add (.mux ic it if_) s
    | .slice lo m a =>
        let (ia, s) := intern a s
        add (.slice lo m ia) s
    | .zext m a =>
        let (ia, s) := intern a s
        add (.zext m ia) s
    | .sext h m d a =>
        let (ia, s) := intern a s
        add (.sext h m d ia) s
def lowerAct (a : FAct) (s : Build) : Act × Build :=
  match a with
  | .skip => (.skip, s)
  | .seq a b =>
      let (a, s) := lowerAct a s
      let (b, s) := lowerAct b s
      (.seq a b, s)
  | .ite c t e =>
      let (c, s) := intern c s
      let (t, s) := lowerAct t s
      let (e, s) := lowerAct e s
      (.ite c t e, s)
  | .write i v =>
      let (v, s) := intern v s
      (.write i v, s)
  | .memWrite base addr data =>
      let (addr, s) := intern addr s
      let (data, s) := intern data s
      (.memWrite base addr data, s)

structure Design where
  nodes : Array Node
  acts : Array Act
  slots : List (Nat × String × Nat)
  deriving Inhabited

def lower (fd : FastDesign) : Design := Id.run do
  let mut s : Build := {}
  let mut acts := Array.mkEmpty fd.acts.size
  for a in fd.acts do
    let (a, s') := lowerAct a s
    s := s'
    acts := acts.push a
  return { nodes := s.nodes, acts, slots := fd.slots }

/-! ## Target-independent DAG structure

These counts describe the generated expression graph itself. They are exact
structural facts, not a technology calibration or a timing prediction. -/

def fexprTreeNodes : FExpr → Nat
  | .lit _ | .reg _ => 1
  | .memRead _ a | .not _ a | .slice _ _ a | .zext _ a | .sext _ _ _ a =>
      1 + fexprTreeNodes a
  | .and a b | .or a b | .xor a b | .add _ a b | .sub _ a b | .mul _ a b |
    .shl _ _ a b | .shr _ a b | .eq a b | .ult a b | .slt _ a b =>
      1 + fexprTreeNodes a + fexprTreeNodes b
  | .mux c t f => 1 + fexprTreeNodes c + fexprTreeNodes t + fexprTreeNodes f

def factExprTreeNodes : FAct → Nat
  | .skip => 0
  | .seq a b => factExprTreeNodes a + factExprTreeNodes b
  | .ite c t e => fexprTreeNodes c + factExprTreeNodes t + factExprTreeNodes e
  | .write _ v => fexprTreeNodes v
  | .memWrite _ a v => fexprTreeNodes a + fexprTreeNodes v

def Act.roots : Act → List Nat
  | .skip => []
  | .seq a b => a.roots ++ b.roots
  | .ite c t e => c :: (t.roots ++ e.roots)
  | .write _ v => [v]
  | .memWrite _ a v => [a, v]

private def bumpUse (uses : Array Nat) (i : Nat) : Array Nat :=
  uses.setIfInBounds i (uses.getD i 0 + 1)

def Design.useCounts (d : Design) : Array Nat :=
  let uses := Array.replicate d.nodes.size 0
  let uses := d.nodes.foldl
    (fun acc n => n.refs.foldl bumpUse acc) uses
  d.acts.foldl (fun acc a => a.roots.foldl bumpUse acc) uses

def Node.depth (depths : Array Nat) (n : Node) : Nat :=
  1 + n.refs.foldl (fun acc i => max acc (depths.getD i 0)) 0

def Design.depths (d : Design) : Array Nat :=
  d.nodes.foldl (fun acc n => acc.push (n.depth acc)) #[]

/-- Exact structural statistics for one lowered evaluator.

`treeNodes` counts every expression occurrence before sharing; `dagNodes`
counts unique nodes after hash-consing. `sharedNodes` have more than one
consumer, including action roots, and `maxUses` is the largest such consumer
count. -/
structure Stats where
  treeNodes : Nat
  dagNodes : Nat
  eliminatedNodes : Nat
  sharedNodes : Nat
  maxDepth : Nat
  maxUses : Nat
  deriving Repr, DecidableEq

def statsOf (fd : FastDesign) (d : Design) : Stats :=
  let treeNodes := fd.acts.foldl (fun n a => n + factExprTreeNodes a) 0
  let uses := d.useCounts
  let depths := d.depths
  { treeNodes
    dagNodes := d.nodes.size
    eliminatedNodes := treeNodes - d.nodes.size
    sharedNodes := uses.foldl (fun n u => if 1 < u then n + 1 else n) 0
    maxDepth := depths.foldl max 0
    maxUses := uses.foldl max 0 }

/-- Lower and report an evaluator's exact DAG structure. -/
def stats (fd : FastDesign) : Stats := statsOf fd (lower fd)

def Stats.render (s : Stats) : String :=
  s!"treeNodes={s.treeNodes} dagNodes={s.dagNodes} " ++
  s!"eliminated={s.eliminatedNodes} shared={s.sharedNodes} " ++
  s!"maxDepth={s.maxDepth} maxUses={s.maxUses}"

@[inline] def val (vs : Array Nat) (i : Nat) : Nat := vs.getD i 0

def Node.eval (pr pm vs : Array Nat) : Node → Nat
  | .lit v => v
  | .reg i => pr.getD i 0
  | .memRead base a => pm.getD (base + val vs a) 0
  | .and a b => val vs a &&& val vs b
  | .or a b => val vs a ||| val vs b
  | .xor a b => val vs a ^^^ val vs b
  | .not mask a => mask - val vs a
  | .add m a b => (val vs a + val vs b) % m
  | .sub m a b => (m - val vs b + val vs a) % m
  | .mul m a b => (val vs a * val vs b) % m
  | .shl w m a b => let s := val vs b; if s < w then (val vs a <<< s) % m else 0
  | .shr w a b => let s := val vs b; if s < w then val vs a >>> s else 0
  | .eq a b => if val vs a = val vs b then 1 else 0
  | .ult a b => if val vs a < val vs b then 1 else 0
  | .slt h a b =>
      let va := val vs a; let vb := val vs b
      if ((decide (h ≤ va) != decide (h ≤ vb)).xor (decide (va < vb))) then 1 else 0
  | .mux c t f => if val vs c = 1 then val vs t else val vs f
  | .slice lo m a => (val vs a >>> lo) % m
  | .zext m a => val vs a % m
  | .sext h m d a => let va := val vs a; va % m + (if h ≤ va then d else 0)

theorem Node.eval_congr (pr pm : Array Nat) (a b : Array Nat) (n : Node)
    (h : ∀ i ∈ n.refs, val a i = val b i) :
    n.eval pr pm a = n.eval pr pm b := by
  cases n <;> simp_all [Node.refs, Node.eval]

def evalList (pr pm : Array Nat) : List Node → Array Nat → Array Nat
  | [], vs => vs
  | n :: ns, vs => evalList pr pm ns (vs.push (n.eval pr pm vs))

def evalNodeArray (nodes : Array Node) (pr pm : Array Nat) : Array Nat :=
  nodes.foldl (fun vs n => vs.push (n.eval pr pm vs))
    (Array.mkEmpty nodes.size)

def evalNodes (d : Design) (fs : FastSt) : Array Nat :=
  evalNodeArray d.nodes fs.regs fs.mems

theorem evalList_size (pr pm : Array Nat) (ns : List Node) (vs : Array Nat) :
    (evalList pr pm ns vs).size = vs.size + ns.length := by
  induction ns generalizing vs with
  | nil => simp [evalList]
  | cons n ns ih => simp [evalList, ih]; omega

theorem evalList_eq_foldl (pr pm : Array Nat) (ns : List Node)
    (vs : Array Nat) :
    evalList pr pm ns vs =
      ns.foldl (fun values n => values.push (n.eval pr pm values)) vs := by
  induction ns generalizing vs with
  | nil => rfl
  | cons n ns ih => exact ih _

theorem evalNodeArray_eq_evalList (nodes : Array Node) (pr pm : Array Nat) :
    evalNodeArray nodes pr pm =
      evalList pr pm nodes.toList (Array.mkEmpty nodes.size) := by
  rw [evalList_eq_foldl]
  unfold evalNodeArray
  exact (Array.foldl_toList _).symm

theorem evalList_preserves (pr pm : Array Nat) (ns : List Node)
    (vs : Array Nat) (i : Nat) (hi : i < vs.size) :
    (evalList pr pm ns vs).getD i 0 = vs.getD i 0 := by
  induction ns generalizing vs with
  | nil => rfl
  | cons n ns ih =>
      rw [evalList, ih (vs.push (n.eval pr pm vs))]
      · have hne : i ≠ vs.size := Nat.ne_of_lt hi
        simp [Array.getElem?_push, hne]
      · simpa using Nat.lt_succ_of_lt hi

theorem evalList_append (pr pm : Array Nat) (xs ys : List Node)
    (vs : Array Nat) :
    evalList pr pm (xs ++ ys) vs = evalList pr pm ys (evalList pr pm xs vs) := by
  induction xs generalizing vs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, evalList]; exact ih _

theorem evalList_new (pr pm : Array Nat) (pre post : List Node)
    (n : Node) (vs : Array Nat) :
    let before := evalList pr pm pre vs
    (evalList pr pm (pre ++ n :: post) vs).getD before.size 0 =
      n.eval pr pm before := by
  dsimp
  rw [evalList_append, evalList]
  rw [evalList_preserves]
  · simp
  · simp

def NodesWF (nodes : Array Node) : Prop :=
  ∀ (i : Nat) (hi : i < nodes.size) (r : Nat),
    r ∈ (nodes[i]).refs → r < i

def nodesWFB (nodes : Array Node) : Bool :=
  (List.range nodes.size).all fun i =>
    (nodes.getD i default).refs.all fun r => r < i

theorem nodesWFB_sound {nodes : Array Node} (h : nodesWFB nodes = true) :
    NodesWF nodes := by
  intro i hi r hr
  have hiMem : i ∈ List.range nodes.size := List.mem_range.mpr hi
  have hall := (List.all_eq_true.mp h) i hiMem
  have hr' : r ∈ (nodes.getD i default).refs := by
    simpa [Array.getD_getElem?, hi] using hr
  exact of_decide_eq_true ((List.all_eq_true.mp hall) r hr')

inductive ExprMatch (nodes : Array Node) : Nat → FExpr → Prop where
  | lit {root v} (bound : root < nodes.size) (node : nodes[root] = .lit v) :
      ExprMatch nodes root (.lit v)
  | reg {root i} (bound : root < nodes.size) (node : nodes[root] = .reg i) :
      ExprMatch nodes root (.reg i)
  | memRead {root base a ea} (bound : root < nodes.size)
      (node : nodes[root] = .memRead base a) (before : a < root)
      (addr : ExprMatch nodes a ea) : ExprMatch nodes root (.memRead base ea)
  | and {root a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .and a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.and ea eb)
  | or {root a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .or a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.or ea eb)
  | xor {root a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .xor a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.xor ea eb)
  | not {root mask a ea} (bound : root < nodes.size)
      (node : nodes[root] = .not mask a) (before : a < root)
      (arg : ExprMatch nodes a ea) : ExprMatch nodes root (.not mask ea)
  | add {root m a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .add m a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.add m ea eb)
  | sub {root m a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .sub m a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.sub m ea eb)
  | mul {root m a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .mul m a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.mul m ea eb)
  | shl {root w m a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .shl w m a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.shl w m ea eb)
  | shr {root w a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .shr w a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.shr w ea eb)
  | eq {root a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .eq a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.eq ea eb)
  | ult {root a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .ult a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.ult ea eb)
  | slt {root h a b ea eb} (bound : root < nodes.size)
      (node : nodes[root] = .slt h a b) (ab : a < root ∧ b < root)
      (left : ExprMatch nodes a ea) (right : ExprMatch nodes b eb) :
      ExprMatch nodes root (.slt h ea eb)
  | mux {root c t f ec et ef} (bound : root < nodes.size)
      (node : nodes[root] = .mux c t f)
      (ctf : c < root ∧ t < root ∧ f < root)
      (cond : ExprMatch nodes c ec) (yes : ExprMatch nodes t et)
      (no : ExprMatch nodes f ef) : ExprMatch nodes root (.mux ec et ef)
  | slice {root lo m a ea} (bound : root < nodes.size)
      (node : nodes[root] = .slice lo m a) (before : a < root)
      (arg : ExprMatch nodes a ea) : ExprMatch nodes root (.slice lo m ea)
  | zext {root m a ea} (bound : root < nodes.size)
      (node : nodes[root] = .zext m a) (before : a < root)
      (arg : ExprMatch nodes a ea) : ExprMatch nodes root (.zext m ea)
  | sext {root h m d a ea} (bound : root < nodes.size)
      (node : nodes[root] = .sext h m d a) (before : a < root)
      (arg : ExprMatch nodes a ea) : ExprMatch nodes root (.sext h m d ea)

structure CheckedExpr (nodes : Array Node) (root : Nat) (e : FExpr) : Type where
  proof : ExprMatch nodes root e

def checkExpr (nodes : Array Node) (root : Nat) :
    (e : FExpr) → Option (CheckedExpr nodes root e)
  | .lit v => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .lit v' => if hv : v' = v then by subst v'; exact some ⟨.lit hr hn⟩ else none
      | _ => none else none
  | .reg i => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .reg i' => if hi : i' = i then by subst i'; exact some ⟨.reg hr hn⟩ else none
      | _ => none else none
  | .memRead base ea => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .memRead base' a => if hb : base' = base then by
          subst base'
          if ha : a < root then
            match checkExpr nodes a ea with
            | some pa => exact some ⟨.memRead hr hn ha pa.proof⟩
            | none => exact none
          else exact none
        else none
      | _ => none else none
  | .and ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .and a b => checkBin hr hn ea eb ExprMatch.and
      | _ => none else none
  | .or ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .or a b => checkBin hr hn ea eb ExprMatch.or
      | _ => none else none
  | .xor ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .xor a b => checkBin hr hn ea eb ExprMatch.xor
      | _ => none else none
  | .not mask ea => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .not mask' a => if hm : mask' = mask then by
          subst mask'; exact checkUnary hr hn ea ExprMatch.not
        else none
      | _ => none else none
  | .add m ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .add m' a b => if hm : m' = m then by
          subst m'; exact checkBin hr hn ea eb ExprMatch.add
        else none
      | _ => none else none
  | .sub m ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .sub m' a b => if hm : m' = m then by
          subst m'; exact checkBin hr hn ea eb ExprMatch.sub
        else none
      | _ => none else none
  | .mul m ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .mul m' a b => if hm : m' = m then by
          subst m'; exact checkBin hr hn ea eb ExprMatch.mul
        else none
      | _ => none else none
  | .shl w m ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .shl w' m' a b => if hw : w' = w then by
          subst w'; exact if hm : m' = m then by
            subst m'; exact checkBin hr hn ea eb ExprMatch.shl
          else none
        else none
      | _ => none else none
  | .shr w ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .shr w' a b => if hw : w' = w then by
          subst w'; exact checkBin hr hn ea eb ExprMatch.shr
        else none
      | _ => none else none
  | .eq ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .eq a b => checkBin hr hn ea eb ExprMatch.eq
      | _ => none else none
  | .ult ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .ult a b => checkBin hr hn ea eb ExprMatch.ult
      | _ => none else none
  | .slt h ea eb => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .slt h' a b => if hh : h' = h then by
          subst h'; exact checkBin hr hn ea eb ExprMatch.slt
        else none
      | _ => none else none
  | .mux ec et ef => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .mux c t f =>
          if hc : c < root then if ht : t < root then if hf : f < root then
            match checkExpr nodes c ec, checkExpr nodes t et, checkExpr nodes f ef with
            | some pc, some pt, some pf =>
                some ⟨.mux hr hn ⟨hc, ht, hf⟩ pc.proof pt.proof pf.proof⟩
            | _, _, _ => none
          else none else none else none
      | _ => none else none
  | .slice lo m ea => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .slice lo' m' a => if hlo : lo' = lo then by
          subst lo'; exact if hm : m' = m then by
            subst m'; exact checkUnary hr hn ea ExprMatch.slice
          else none
        else none
      | _ => none else none
  | .zext m ea => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .zext m' a => if hm : m' = m then by
          subst m'; exact checkUnary hr hn ea ExprMatch.zext
        else none
      | _ => none else none
  | .sext h m d ea => if hr : root < nodes.size then
      match hn : nodes[root] with
      | .sext h' m' d' a => if hh : h' = h then by
          subst h'; exact if hm : m' = m then by
            subst m'; exact if hd : d' = d then by
              subst d'; exact checkUnary hr hn ea ExprMatch.sext
            else none
          else none
        else none
      | _ => none else none
where
  checkUnary {root : Nat} {e : FExpr} (hr : root < nodes.size)
      {a : Nat} {n : Node} (hn : nodes[root] = n) (ea : FExpr)
      (mk : root < nodes.size → nodes[root] = n → a < root →
        ExprMatch nodes a ea → ExprMatch nodes root e) :
      Option (CheckedExpr nodes root e) :=
    if ha : a < root then
      match checkExpr nodes a ea with
      | some pa => some ⟨mk hr hn ha pa.proof⟩
      | none => none
    else none
  checkBin {root : Nat} {e : FExpr} (hr : root < nodes.size)
      {a b : Nat} {n : Node} (hn : nodes[root] = n) (ea eb : FExpr)
      (mk : root < nodes.size → nodes[root] = n → a < root ∧ b < root →
        ExprMatch nodes a ea → ExprMatch nodes b eb → ExprMatch nodes root e) :
      Option (CheckedExpr nodes root e) :=
    if ha : a < root then
      if hb : b < root then
        match checkExpr nodes a ea, checkExpr nodes b eb with
        | some pa, some pb => some ⟨mk hr hn ⟨ha, hb⟩ pa.proof pb.proof⟩
        | _, _ => none
      else none
    else none

theorem evalNodeArray_equation (nodes : Array Node) (pr pm : Array Nat)
    (hwf : NodesWF nodes) (i : Nat) (hi : i < nodes.size) :
    val (evalNodeArray nodes pr pm) i =
      (nodes[i]).eval pr pm (evalNodeArray nodes pr pm) := by
  let xs := nodes.toList
  let pre := xs.take i
  let post := xs.drop (i + 1)
  let node := nodes[i]
  let before := evalList pr pm pre (Array.mkEmpty nodes.size)
  have hix : i < xs.length := by simpa [xs] using hi
  have hnode : xs[i] = node := by simp [xs, node]
  have hsplit : xs = pre ++ node :: post := by
    calc
      xs = xs.take (i + 1) ++ xs.drop (i + 1) :=
        (List.take_append_drop (i + 1) xs).symm
      _ = (xs.take i ++ [xs[i]]) ++ xs.drop (i + 1) := by
        rw [List.take_succ_eq_append_getElem hix]
      _ = pre ++ node :: post := by simp [pre, post, hnode]
  have hprelen : pre.length = i := by
    simp [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hix)]
  have hbefore : before.size = i := by
    dsimp [before]
    rw [evalList_size]
    simp [hprelen]
  have hfull : evalNodeArray nodes pr pm =
      evalList pr pm (node :: post) before := by
    rw [evalNodeArray_eq_evalList]
    change evalList pr pm xs (Array.mkEmpty nodes.size) = _
    rw [hsplit, evalList_append]
  have hroot : val (evalNodeArray nodes pr pm) i =
      node.eval pr pm before := by
    rw [hfull]
    unfold evalList
    change (evalList pr pm post
      (before.push (node.eval pr pm before))).getD i 0 = _
    rw [evalList_preserves]
    · rw [← hbefore]
      simp
    · simp [hbefore]
  have hroot' : val (evalNodeArray nodes pr pm) i =
      (nodes[i]).eval pr pm before := by simpa [node] using hroot
  rw [hroot']
  apply Node.eval_congr
  intro r hr
  have hri : r < i := by
    apply hwf i hi r
    simpa [xs] using hr
  change before.getD r 0 = (evalNodeArray nodes pr pm).getD r 0
  rw [hfull]
  exact (evalList_preserves pr pm (node :: post) before r (by
    rw [hbefore]
    exact hri)).symm

theorem ExprMatch.eval {nodes : Array Node} {root : Nat} {e : FExpr}
    (hm : ExprMatch nodes root e) (pr pm : Array Nat) (hwf : NodesWF nodes) :
    val (evalNodeArray nodes pr pm) root = e.eval pr pm := by
  induction hm <;>
    rw [evalNodeArray_equation nodes pr pm hwf _ (by assumption)] <;>
    simp_all [Node.eval, FExpr.eval]

inductive ActMatch (nodes : Array Node) : Act → FAct → Prop where
  | skip : ActMatch nodes .skip .skip
  | seq {a b fa fb} (left : ActMatch nodes a fa)
      (right : ActMatch nodes b fb) : ActMatch nodes (.seq a b) (.seq fa fb)
  | ite {c t e ec ft fe} (cond : ExprMatch nodes c ec)
      (yes : ActMatch nodes t ft) (no : ActMatch nodes e fe) :
      ActMatch nodes (.ite c t e) (.ite ec ft fe)
  | write {i v ev} (value : ExprMatch nodes v ev) :
      ActMatch nodes (.write i v) (.write i ev)
  | memWrite {base a v ea ev} (addr : ExprMatch nodes a ea)
      (value : ExprMatch nodes v ev) :
      ActMatch nodes (.memWrite base a v) (.memWrite base ea ev)

structure CheckedAct (nodes : Array Node) (a : Act) (fa : FAct) : Type where
  proof : ActMatch nodes a fa

def checkAct (nodes : Array Node) :
    (a : Act) → (fa : FAct) → Option (CheckedAct nodes a fa)
  | .skip, .skip => some ⟨.skip⟩
  | .seq a b, .seq fa fb =>
      match checkAct nodes a fa, checkAct nodes b fb with
      | some pa, some pb => some ⟨.seq pa.proof pb.proof⟩
      | _, _ => none
  | .ite c t e, .ite ec ft fe =>
      match checkExpr nodes c ec, checkAct nodes t ft, checkAct nodes e fe with
      | some pc, some pt, some pe => some ⟨.ite pc.proof pt.proof pe.proof⟩
      | _, _, _ => none
  | .write i v, .write i' ev =>
      if hi : i' = i then by
        subst i'
        match checkExpr nodes v ev with
        | some pv => exact some ⟨.write pv.proof⟩
        | none => exact none
      else none
  | .memWrite base a v, .memWrite base' ea ev =>
      if hb : base' = base then by
        subst base'
        match checkExpr nodes a ea, checkExpr nodes v ev with
        | some pa, some pv => exact some ⟨.memWrite pa.proof pv.proof⟩
        | _, _ => exact none
      else none
  | _, _ => none

def ActsMatch (nodes : Array Node) (acts : List Act) (facts : List FAct) : Prop :=
  List.Forall₂ (ActMatch nodes) acts facts

structure CheckedActs (nodes : Array Node) (acts : List Act)
    (facts : List FAct) : Type where
  proof : ActsMatch nodes acts facts

def checkActs (nodes : Array Node) :
    (acts : List Act) → (facts : List FAct) → Option (CheckedActs nodes acts facts)
  | [], [] => some ⟨.nil⟩
  | a :: acts, fa :: facts =>
      match checkAct nodes a fa, checkActs nodes acts facts with
      | some pa, some ps => some ⟨.cons pa.proof ps.proof⟩
      | _, _ => none
  | _, _ => none

def Act.run (pr pm vs : Array Nat) : Act → FastSt → FastSt
  | .skip, acc => acc
  | .seq a b, acc => b.run pr pm vs (a.run pr pm vs acc)
  | .ite c t e, acc => if val vs c = 1 then t.run pr pm vs acc else e.run pr pm vs acc
  | .write i v, acc => { acc with regs := acc.regs.setIfInBounds i (val vs v) }
  | .memWrite base a v, acc =>
      { acc with mems := acc.mems.setIfInBounds (base + val vs a) (val vs v) }

theorem ActMatch.run_eq {nodes : Array Node} {a : Act} {fa : FAct}
    (hm : ActMatch nodes a fa) (pr pm : Array Nat) (acc : FastSt)
    (hwf : NodesWF nodes) :
    a.run pr pm (evalNodeArray nodes pr pm) acc = fa.run pr pm acc := by
  induction hm generalizing acc with
  | skip => rfl
  | seq left right ihl ihr => simp only [Act.run, FAct.run, ihl, ihr]
  | ite cond yes no ihy ihn =>
      simp only [Act.run, FAct.run, cond.eval pr pm hwf]
      split <;> simp [ihy, ihn]
  | write value => simp [Act.run, FAct.run, value.eval pr pm hwf]
  | memWrite addr value =>
      simp [Act.run, FAct.run, addr.eval pr pm hwf, value.eval pr pm hwf]

theorem ActsMatch.fold_eq {nodes : Array Node} {acts : List Act}
    {facts : List FAct} (hm : ActsMatch nodes acts facts)
    (pr pm : Array Nat) (acc : FastSt) (hwf : NodesWF nodes) :
    acts.foldl (fun s a => a.run pr pm (evalNodeArray nodes pr pm) s) acc =
      facts.foldl (fun s a => a.run pr pm s) acc := by
  induction hm generalizing acc with
  | nil => rfl
  | cons h _ ih =>
      simp only [List.foldl_cons]
      rw [h.run_eq pr pm acc hwf]
      exact ih _

def cycle (d : Design) (fs : FastSt) : FastSt :=
  let vs := evalNodes d fs
  d.acts.toList.foldl (fun acc a => a.run fs.regs fs.mems vs acc) fs

def setInputs (d : Design) (ι : InEnv) (fs : FastSt) : FastSt :=
  let regs := d.slots.foldl
    (fun r s => r.setIfInBounds s.1 ((ι s.2.1 s.2.2).toNat)) fs.regs
  { fs with regs := regs }

def cycleOpen (d : Design) (ι : InEnv) (fs : FastSt) : FastSt :=
  cycle d (setInputs d ι fs)

structure Certificate (fd : FastDesign) (d : Design) : Prop where
  nodes : NodesWF d.nodes
  acts : ActsMatch d.nodes d.acts.toList fd.acts.toList
  slots : d.slots = fd.slots

structure CheckedCertificate (fd : FastDesign) (d : Design) : Type where
  proof : Certificate fd d

def checkCertificate (fd : FastDesign) (d : Design) :
    Option (CheckedCertificate fd d) :=
  if hn : nodesWFB d.nodes = true then
    match checkActs d.nodes d.acts.toList fd.acts.toList with
    | some ha =>
        if hs : d.slots = fd.slots then
          some ⟨⟨nodesWFB_sound hn, ha.proof, hs⟩⟩
        else none
    | none => none
  else none

structure Verified (fd : FastDesign) where
  design : Design
  cert : Certificate fd design

def prepare? (fd : FastDesign) : Option (Verified fd) :=
  let d := lower fd
  match checkCertificate fd d with
  | some cert => some ⟨d, cert.proof⟩
  | none => none

namespace Verified

def cycle {fd : FastDesign} (sim : Verified fd) (fs : FastSt) : FastSt :=
  Loom.Hw.DagEval.cycle sim.design fs

def cycleOpen {fd : FastDesign} (sim : Verified fd) (ι : InEnv)
    (fs : FastSt) : FastSt := Loom.Hw.DagEval.cycleOpen sim.design ι fs

def run {fd : FastDesign} (sim : Verified fd) : Nat → FastSt → FastSt
  | 0, fs => fs
  | n + 1, fs => sim.run n (sim.cycle fs)

def runOpen {fd : FastDesign} (sim : Verified fd) (ιs : Nat → InEnv) :
    Nat → FastSt → FastSt
  | 0, fs => fs
  | n + 1, fs => sim.runOpen (fun k => ιs (k + 1)) n (sim.cycleOpen (ιs 0) fs)

end Verified

theorem Certificate.cycle_eq {fd : FastDesign} {d : Design}
    (cert : Certificate fd d) (fs : FastSt) : cycle d fs = fastCycle fd fs := by
  unfold cycle fastCycle evalNodes
  rw [cert.acts.fold_eq fs.regs fs.mems fs cert.nodes]
  simp only [Array.foldl_toList]

theorem Certificate.setInputs_eq {fd : FastDesign} {d : Design}
    (cert : Certificate fd d) (ι : InEnv) (fs : FastSt) :
    setInputs d ι fs = fastSetInputs fd ι fs := by
  simp [setInputs, fastSetInputs, cert.slots]

theorem Certificate.cycleOpen_eq {fd : FastDesign} {d : Design}
    (cert : Certificate fd d) (ι : InEnv) (fs : FastSt) :
    cycleOpen d ι fs = fastCycleOpen fd ι fs := by
  simp [cycleOpen, fastCycleOpen, cert.setInputs_eq, cert.cycle_eq]

namespace Verified

theorem cycle_eq {fd : FastDesign} (sim : Verified fd) (fs : FastSt) :
    sim.cycle fs = fastCycle fd fs := sim.cert.cycle_eq fs

theorem cycleOpen_eq {fd : FastDesign} (sim : Verified fd) (ι : InEnv)
    (fs : FastSt) : sim.cycleOpen ι fs = fastCycleOpen fd ι fs :=
  sim.cert.cycleOpen_eq ι fs

theorem run_eq {fd : FastDesign} (sim : Verified fd) (n : Nat) (fs : FastSt) :
    sim.run n fs = fastRun fd n fs := by
  induction n generalizing fs with
  | zero => rfl
  | succ n ih => simp only [run, fastRun, sim.cycle_eq, ih]

theorem runOpen_eq {fd : FastDesign} (sim : Verified fd) (ιs : Nat → InEnv)
    (n : Nat) (fs : FastSt) :
    sim.runOpen ιs n fs = fastRunOpen fd ιs n fs := by
  induction n generalizing ιs fs with
  | zero => rfl
  | succ n ih => simp only [runOpen, fastRunOpen, sim.cycleOpen_eq, ih]

end Verified

/-- A checked DAG evaluator packaged with the existing semantic proof for the
`Design` it came from. This is the W5 public object: the DAG certificate proves
equality to `fastCycleOpen`; the underlying `FastEval` certificate carries that
equality through to `Design.cycleOpen`. -/
structure VerifiedSimulator (d : Loom.Hw.Design) where
  base : FastEval.VerifiedSimulator d
  dag : Verified base.fast

def prepareSimulator? {d : Loom.Hw.Design} (base : FastEval.VerifiedSimulator d) :
    Option (VerifiedSimulator d) :=
  match prepare? base.fast with
  | some dag => some ⟨base, dag⟩
  | none => none

/-- IO-facing fail-closed preparation. Pure theorem witnesses can use
`prepareSimulator?`; executable acceptance paths use this adapter so a failed
certificate cannot silently fall back to the tree evaluator. -/
def prepareSimulator {d : Loom.Hw.Design} (base : FastEval.VerifiedSimulator d)
    (label : String := "generated design") : IO (VerifiedSimulator d) :=
  match prepareSimulator? base with
  | some dag => pure dag
  | none => throw <| IO.userError s!"{label} DAG simulator certificate failed"

namespace VerifiedSimulator

def reset {d : Loom.Hw.Design} (sim : VerifiedSimulator d) : FastSt :=
  sim.base.reset

def cycle {d : Loom.Hw.Design} (sim : VerifiedSimulator d) (fs : FastSt) : FastSt :=
  sim.dag.cycle fs

def cycleOpen {d : Loom.Hw.Design} (sim : VerifiedSimulator d) (ι : InEnv)
    (fs : FastSt) : FastSt := sim.dag.cycleOpen ι fs

/-- Execute `n` closed cycles through the certified DAG. -/
def run {d : Loom.Hw.Design} (sim : VerifiedSimulator d) (n : Nat)
    (fs : FastSt) : FastSt := sim.dag.run n fs

/-- Execute `n` open cycles through the certified DAG. -/
def runOpen {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (ιs : Nat → InEnv) (n : Nat) (fs : FastSt) : FastSt :=
  sim.dag.runOpen ιs n fs

theorem cycle_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.cycle fs) (d.cycle σ) := by
  unfold cycle
  rw [sim.dag.cycle_eq]
  exact sim.base.cycle_eq fs σ ha

theorem cycleOpen_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (ι : InEnv) (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.cycleOpen ι fs) (d.cycleOpen ι σ) := by
  unfold cycleOpen
  rw [sim.dag.cycleOpen_eq]
  exact sim.base.cycleOpen_eq ι fs σ ha

/-- A certified DAG run agrees with the reference closed-design run on every
declared coordinate. -/
theorem run_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d) (n : Nat)
    (fs : FastSt) (σ : St) (ha : Agree d fs σ) :
    Agree d (sim.run n fs) (d.run n σ) := by
  unfold run
  rw [sim.dag.run_eq]
  exact sim.base.run_eq n fs σ ha

/-- A certified DAG run agrees with the reference open-design run on every
declared coordinate. -/
theorem runOpen_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (n : Nat) (ιs : Nat → InEnv) (fs : FastSt) (σ : St)
    (ha : Agree d fs σ) :
    Agree d (sim.runOpen ιs n fs) (d.runOpen ιs n σ) := by
  unfold runOpen
  rw [sim.dag.runOpen_eq]
  exact sim.base.runOpen_eq n ιs fs σ ha

/-- Direct closed-run theorem from the design-derived reset state. -/
theorem runFromReset_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (n : Nat) : Agree d (sim.run n sim.reset) (d.run n d.reset) :=
  sim.run_eq n _ _ (FastEval.agree_fastReset d)

/-- Direct open-run theorem from the design-derived reset state. -/
theorem runOpenFromReset_eq {d : Loom.Hw.Design} (sim : VerifiedSimulator d)
    (n : Nat) (ιs : Nat → InEnv) :
    Agree d (sim.runOpen ιs n sim.reset) (d.runOpen ιs n d.reset) :=
  sim.runOpen_eq n ιs _ _ (FastEval.agree_fastReset d)

end VerifiedSimulator

end Loom.Hw.DagEval
