-- Copyright (c) 2026 Kevin Baragona
-- SPDX-License-Identifier: Apache-2.0
import Loom.Release.FlattenWF

/-!
# Injectivity of the flatten CSE keys

`flatten` hash-conses SSA nodes on `(width, rendered-key)` pairs. For the
semantic half of `toProgram_denotes`, a CSE hit must imply that the hit's
recorded `Rhs` is the *same structural node* as the one being emitted. That
is exactly injectivity of the rendered key — which is false for adversarial
operand strings (`.ident "a + b"` renders like `.bin .add "a" "b"`), so it is
proved here under an identifier discipline: every operand is a nonempty
`[A-Za-z_][A-Za-z0-9_]*` token (`identTokenB`), which every canonical wire
name `n<i>` satisfies (`identTokenB_wireName`).

The proof works at the `String.toList` character level. Identifier tokens
exclude every metacharacter the key shapes use, so the leftmost non-token
character of a key determines the node's shape (`firstSep`), and within a
shape the fixed separators cut the key uniquely into its operand tokens and
decimal fields (`sep_inj`).
-/

namespace Loom.Release.SSA

/-! ## Tokens -/

/-- Characters allowed inside an identifier token: `[A-Za-z0-9_]`. -/
def identCharB (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Characters allowed to start an identifier token: `[A-Za-z_]`. -/
def identStartB (c : Char) : Bool := c.isAlpha || c == '_'

/-- List-level identifier-token check. -/
def identTokenListB : List Char → Bool
  | [] => false
  | c :: cs => identStartB c && cs.all identCharB

/-- An identifier token: nonempty, first char in `[A-Za-z_]`, all chars in
`[A-Za-z0-9_]`. Kernel-reducible on concrete strings (see the tests below). -/
def identTokenB (s : String) : Bool := identTokenListB s.toList

example : identTokenB "n17" = true := by decide
example : identTokenB "a + b" = false := by decide
example : identTokenB "" = false := by decide
example : identTokenB "9lives" = false := by decide

theorem identCharB_of_start {c : Char} (h : identStartB c = true) :
    identCharB c = true := by
  simp only [identStartB, Bool.or_eq_true] at h
  simp only [identCharB, Char.isAlphanum, Bool.or_eq_true]
  rcases h with h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inr h

theorem identCharB_of_isDigit {c : Char} (h : c.isDigit = true) :
    identCharB c = true := by
  simp only [identCharB, Char.isAlphanum, Bool.or_eq_true]
  exact Or.inl (Or.inr h)

theorem identTokenListB_chars {l : List Char} (h : identTokenListB l = true) :
    ∀ c ∈ l, identCharB c = true := by
  match l with
  | [] => intro c hc; cases hc
  | c :: cs =>
    simp only [identTokenListB, Bool.and_eq_true, List.all_eq_true] at h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact identCharB_of_start h.1
    · exact h.2 a ha

/-- Every character of an identifier token is a token character. -/
theorem identTokenB_chars {s : String} (h : identTokenB s = true) :
    ∀ c ∈ s.toList, identCharB c = true :=
  identTokenListB_chars h

/-- Every character of a printed decimal number is a token character. -/
theorem digits_chars (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, identCharB c = true :=
  fun _ hc =>
    identCharB_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-! ## Decimal rendering -/

private theorem toString_nat_eq (n : Nat) :
    (toString n : String) = String.ofList (Nat.toDigits 10 n) := by
  show Nat.repr n = _
  rw [Nat.repr.eq_def]

private theorem toList_toString_nat (n : Nat) :
    (toString n : String).toList = Nat.toDigits 10 n := by
  rw [toString_nat_eq, String.toList_ofList]

private theorem toList_toString_string (s : String) :
    (toString s : String).toList = s.toList := rfl

private theorem toNat_digitChar {d : Nat} (h : d < 10) :
    (Nat.digitChar d).toNat - '0'.toNat = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => decide

private theorem foldl_digits :
    ∀ (n : Nat), ∀ (a : Nat),
      List.foldl (fun a c => a * 10 + (c.toNat - '0'.toNat)) a
          (Nat.toDigits 10 n) =
        a * 10 ^ (Nat.toDigits 10 n).length + n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a
    by_cases h : n < 10
    · rw [Nat.toDigits_of_lt_base h]
      simp only [List.foldl_cons, List.foldl_nil, List.length_cons,
        List.length_nil]
      rw [toNat_digitChar h, Nat.zero_add, Nat.pow_one]
    · have h10 : 0 < n / 10 := Nat.div_pos (by omega) (by omega)
      have hdec := Nat.toDigits_append_toDigits (b := 10) (n := n / 10)
        (d := n % 10) (by omega) h10 (by omega)
      have hn : 10 * (n / 10) + n % 10 = n := by omega
      rw [hn] at hdec
      rw [← hdec, List.foldl_append, ih (n / 10) (by omega) a,
        Nat.toDigits_of_lt_base (by omega : n % 10 < 10)]
      simp only [List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      rw [toNat_digitChar (by omega)]
      have hpow : 10 ^ ((Nat.toDigits 10 (n / 10)).length + (0 + 1)) =
          10 ^ (Nat.toDigits 10 (n / 10)).length * 10 := by
        rw [Nat.zero_add, Nat.pow_succ]
      rw [hpow]
      generalize (10 : Nat) ^ (Nat.toDigits 10 (n / 10)).length = X
      have hassoc : a * (X * 10) = a * X * 10 := by rw [Nat.mul_assoc]
      rw [hassoc]
      generalize a * X = Y
      omega

/-- Decimal rendering is injective. -/
private theorem toDigits_inj {m n : Nat}
    (h : Nat.toDigits 10 m = Nat.toDigits 10 n) : m = n := by
  have hm := foldl_digits m 0
  have hn := foldl_digits n 0
  rw [h] at hm
  omega

/-! ## The canonical wire name is a token -/

private theorem wireName_toList (m : Nat) :
    (Symbolic.wireName m).toList = 'n' :: Nat.toDigits 10 m := by
  rw [wireName_eq_append, String.toList_append, toList_toString_nat]
  rfl

theorem identTokenB_wireName (m : Nat) :
    identTokenB (Symbolic.wireName m) = true := by
  unfold identTokenB
  rw [wireName_toList]
  simp only [identTokenListB, Bool.and_eq_true, List.all_eq_true]
  exact ⟨by decide, fun c hc =>
    identCharB_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)⟩

/-! ## Separators -/

/-- Leftmost-separator uniqueness: a character list that splits as a token
prefix followed by a non-token separator splits that way uniquely. -/
theorem sep_inj : ∀ {P Q : List Char} {c d : Char} {R S : List Char},
    (∀ a ∈ P, identCharB a = true) → (∀ a ∈ Q, identCharB a = true) →
    identCharB c = false → identCharB d = false →
    P ++ c :: R = Q ++ d :: S → P = Q ∧ c = d ∧ R = S := by
  intro P
  induction P with
  | nil =>
    intro Q c d R S _ hQ hc hd h
    cases Q with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h.1, h.2⟩
    | cons q Q' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have hq := hQ q List.mem_cons_self
      rw [← h.1] at hq
      simp [hq] at hc
  | cons p P' ih =>
    intro Q c d R S hP hQ hc hd h
    cases Q with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      have hp := hP p List.mem_cons_self
      rw [h.1] at hp
      simp [hp] at hd
    | cons q Q' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨hPQ, hcd, hRS⟩ := ih
        (fun a ha => hP a (List.mem_cons_of_mem _ ha))
        (fun a ha => hQ a (List.mem_cons_of_mem _ ha)) hc hd h2
      exact ⟨by rw [hPQ], hcd, hRS⟩

/-- An all-token list contains no separator. -/
theorem no_sep_of_all_tok {X P R : List Char} {c : Char}
    (hX : ∀ a ∈ X, identCharB a = true) (hc : identCharB c = false)
    (h : X = P ++ c :: R) : False := by
  have hm : c ∈ X := by rw [h]; simp
  have := hX c hm
  simp [this] at hc

/-! ## The rendered keys -/

/-- The exact key string `flatten` passes to `freshWire` for each
constructor, copied verbatim from `flatten`'s interpolations (see the
`flatten_key_*` lemmas below, all of which hold by `rfl`). -/
def keyOf : Rhs → String
  | .lit w v => s!"{w}'d{v}"
  | .ident x => s!"{x}"
  | .memRead m a => s!"{m}[{a}]"
  | .slice x hi lo => s!"{x}[{hi}:{lo}]"
  | .not x => s!"~{x}"
  | .bin .and x y => s!"{x} & {y}"
  | .bin .or x y => s!"{x} | {y}"
  | .bin .xor x y => s!"{x} ^ {y}"
  | .bin .add x y => s!"{x} + {y}"
  | .bin .sub x y => s!"{x} - {y}"
  | .bin .mul x y => s!"{x} * {y}"
  | .bin .udiv x y => s!"{x} / {y}"
  | .bin .urem x y => s!"{x} % {y}"
  | .bin .shl x y => s!"{x} << {y}"
  | .bin .shr x y => s!"{x} >> {y}"
  | .bin .eq x y => s!"{x} == {y}"
  | .bin .ult x y => s!"{x} < {y}"
  | .slt x y => s!"$signed({x}) < $signed({y})"
  | .mux c t f => s!"{c} ? {t} : {f}"
  | .sext k x b =>
      "{" ++ ("{" ++ toString k ++ "{" ++ x ++ "[" ++ toString b ++ "]}}") ++
        ", " ++ x ++ "}"

/-- The characters of a binary operator's rendered token. -/
def BinOp.keyChars : BinOp → List Char
  | .and => ['&']
  | .or => ['|']
  | .xor => ['^']
  | .add => ['+']
  | .sub => ['-']
  | .mul => ['*']
  | .udiv => ['/']
  | .urem => ['%']
  | .shl => ['<', '<']
  | .shr => ['>', '>']
  | .eq => ['=', '=']
  | .ult => ['<']

/-- Every operand string of the node (and the memory name of `memRead`) is
an identifier token. -/
def rhsTokensOk : Rhs → Bool
  | .lit _ _ => true
  | .ident x => identTokenB x
  | .memRead m a => identTokenB m && identTokenB a
  | .slice x _ _ => identTokenB x
  | .not x => identTokenB x
  | .bin _ x y => identTokenB x && identTokenB y
  | .slt x y => identTokenB x && identTokenB y
  | .mux c t f => identTokenB c && identTokenB t && identTokenB f
  | .sext _ x _ => identTokenB x

/-! ### Character-level normal forms of the seventeen key shapes -/

private theorem toList_keyOf_lit (w v : Nat) :
    (keyOf (.lit w v)).toList =
      Nat.toDigits 10 w ++ '\'' :: 'd' :: Nat.toDigits 10 v := by
  simp only [keyOf, String.toList_append, toList_toString_nat, List.append_assoc]
  rfl

private theorem toList_keyOf_ident (x : String) :
    (keyOf (.ident x)).toList = x.toList := rfl

private theorem toList_keyOf_memRead (m a : String) :
    (keyOf (.memRead m a)).toList = m.toList ++ '[' :: (a.toList ++ [']']) := by
  simp only [keyOf, String.toList_append, toList_toString_string,
    List.append_assoc]
  rfl

private theorem toList_keyOf_slice (x : String) (hi lo : Nat) :
    (keyOf (.slice x hi lo)).toList =
      x.toList ++ '[' ::
        (Nat.toDigits 10 hi ++ ':' :: (Nat.toDigits 10 lo ++ [']'])) := by
  simp only [keyOf, String.toList_append, toList_toString_string,
    toList_toString_nat, List.append_assoc]
  rfl

private theorem toList_keyOf_not (x : String) :
    (keyOf (.not x)).toList = '~' :: x.toList := by
  simp only [keyOf, String.toList_append, toList_toString_string]
  rfl

private theorem toList_keyOf_bin (op : BinOp) (x y : String) :
    (keyOf (.bin op x y)).toList =
      x.toList ++ ' ' :: (op.keyChars ++ ' ' :: y.toList) := by
  cases op <;>
    · simp only [keyOf, BinOp.keyChars, String.toList_append,
        toList_toString_string, List.append_assoc]
      rfl

private theorem toList_keyOf_slt (x y : String) :
    (keyOf (.slt x y)).toList =
      '$' :: 's' :: 'i' :: 'g' :: 'n' :: 'e' :: 'd' :: '(' ::
        (x.toList ++ ')' :: ' ' :: '<' :: ' ' ::
          '$' :: 's' :: 'i' :: 'g' :: 'n' :: 'e' :: 'd' :: '(' ::
            (y.toList ++ [')'])) := by
  simp only [keyOf, String.toList_append, toList_toString_string,
    List.append_assoc]
  rfl

private theorem toList_keyOf_mux (c t f : String) :
    (keyOf (.mux c t f)).toList =
      c.toList ++ ' ' :: '?' :: ' ' ::
        (t.toList ++ ' ' :: ':' :: ' ' :: f.toList) := by
  simp only [keyOf, String.toList_append, toList_toString_string,
    List.append_assoc]
  rfl

private theorem toList_keyOf_sext (k : Nat) (x : String) (b : Nat) :
    (keyOf (.sext k x b)).toList =
      '{' :: '{' ::
        (Nat.toDigits 10 k ++ '{' ::
          (x.toList ++ '[' ::
            (Nat.toDigits 10 b ++ ']' :: '}' :: '}' :: ',' :: ' ' ::
              (x.toList ++ ['}'])))) := by
  simp only [keyOf, String.toList_append, toList_toString_nat,
    List.append_assoc]
  rfl

/-! ### Shape classification -/

/-- The leftmost non-token character of each key shape (`none` = the key is
one bare token). -/
def firstSep : Rhs → Option Char
  | .lit _ _ => some '\''
  | .ident _ => none
  | .memRead _ _ => some '['
  | .slice _ _ _ => some '['
  | .not _ => some '~'
  | .bin _ _ _ => some ' '
  | .slt _ _ => some '$'
  | .mux _ _ _ => some ' '
  | .sext _ _ _ => some '{'

/-- Every token-disciplined key decomposes at its shape's first separator. -/
private theorem key_decomp (r : Rhs) (ok : rhsTokensOk r = true) :
    (firstSep r = none ∧ ∀ c ∈ (keyOf r).toList, identCharB c = true) ∨
    ∃ P c R, firstSep r = some c ∧ (keyOf r).toList = P ++ c :: R ∧
      (∀ a ∈ P, identCharB a = true) ∧ identCharB c = false := by
  cases r with
  | lit w v =>
      exact .inr ⟨Nat.toDigits 10 w, '\'', 'd' :: Nat.toDigits 10 v, rfl,
        toList_keyOf_lit w v, digits_chars w, by decide⟩
  | ident x =>
      exact .inl ⟨rfl, by rw [toList_keyOf_ident]; exact identTokenB_chars ok⟩
  | memRead m a =>
      simp only [rhsTokensOk, Bool.and_eq_true] at ok
      exact .inr ⟨m.toList, '[', a.toList ++ [']'], rfl,
        toList_keyOf_memRead m a, identTokenB_chars ok.1, by decide⟩
  | slice x hi lo =>
      exact .inr ⟨x.toList, '[',
        Nat.toDigits 10 hi ++ ':' :: (Nat.toDigits 10 lo ++ [']']), rfl,
        toList_keyOf_slice x hi lo, identTokenB_chars ok, by decide⟩
  | not x =>
      refine .inr ⟨[], '~', x.toList, rfl, toList_keyOf_not x, ?_, by decide⟩
      intro a ha; exact nomatch ha
  | bin op x y =>
      simp only [rhsTokensOk, Bool.and_eq_true] at ok
      exact .inr ⟨x.toList, ' ', op.keyChars ++ ' ' :: y.toList, rfl,
        toList_keyOf_bin op x y, identTokenB_chars ok.1, by decide⟩
  | slt x y =>
      refine .inr ⟨[], '$',
        's' :: 'i' :: 'g' :: 'n' :: 'e' :: 'd' :: '(' ::
          (x.toList ++ ')' :: ' ' :: '<' :: ' ' ::
            '$' :: 's' :: 'i' :: 'g' :: 'n' :: 'e' :: 'd' :: '(' ::
              (y.toList ++ [')'])), rfl, toList_keyOf_slt x y, ?_, by decide⟩
      intro a ha; exact nomatch ha
  | mux c t f =>
      simp only [rhsTokensOk, Bool.and_eq_true] at ok
      exact .inr ⟨c.toList, ' ',
        '?' :: ' ' :: (t.toList ++ ' ' :: ':' :: ' ' :: f.toList), rfl,
        toList_keyOf_mux c t f, identTokenB_chars ok.1.1, by decide⟩
  | sext k x b =>
      refine .inr ⟨[], '{',
        '{' :: (Nat.toDigits 10 k ++ '{' ::
          (x.toList ++ '[' ::
            (Nat.toDigits 10 b ++ ']' :: '}' :: '}' :: ',' :: ' ' ::
              (x.toList ++ ['}'])))), rfl,
        toList_keyOf_sext k x b, ?_, by decide⟩
      intro a ha; exact nomatch ha

/-- Equal token-disciplined keys have equal shape classes. -/
private theorem firstSep_eq_of_key {r1 r2 : Rhs} (ok1 : rhsTokensOk r1 = true)
    (ok2 : rhsTokensOk r2 = true)
    (h : (keyOf r1).toList = (keyOf r2).toList) : firstSep r1 = firstSep r2 := by
  rcases key_decomp r1 ok1 with ⟨e1, tok1⟩ | ⟨P, c, R, e1, d1, hP, hc⟩
  · rcases key_decomp r2 ok2 with ⟨e2, -⟩ | ⟨Q, d, S, e2, d2, -, hd⟩
    · rw [e1, e2]
    · exact (no_sep_of_all_tok tok1 hd (h.trans d2)).elim
  · rcases key_decomp r2 ok2 with ⟨e2, tok2⟩ | ⟨Q, d, S, e2, d2, hQ, hd⟩
    · exact (no_sep_of_all_tok tok2 hc (h.symm.trans d1)).elim
    · rw [e1, e2, (sep_inj hP hQ hc hd (d1.symm.trans (h.trans d2))).2.1]

/-- Binary-operator tokens followed by a space separator disambiguate. -/
private theorem binop_sep {o1 o2 : BinOp} {y1 y2 : List Char}
    (h : BinOp.keyChars o1 ++ ' ' :: y1 = BinOp.keyChars o2 ++ ' ' :: y2) :
    o1 = o2 ∧ y1 = y2 := by
  cases o1 <;> cases o2 <;> simp_all [BinOp.keyChars]

/-! ## The injectivity theorem -/

/-- Under the identifier discipline, equal rendered keys imply equal
structural nodes. -/
theorem keyOf_injective {r1 r2 : Rhs}
    (ok1 : rhsTokensOk r1 = true) (ok2 : rhsTokensOk r2 = true)
    (keyEq : keyOf r1 = keyOf r2) : r1 = r2 := by
  have h : (keyOf r1).toList = (keyOf r2).toList := by rw [keyEq]
  cases r1 <;> cases r2 <;>
    try {
      have hs := firstSep_eq_of_key ok1 ok2 h
      simp only [firstSep] at hs
      exact absurd hs (by decide) }
  case lit.lit w v w' v' =>
    rw [toList_keyOf_lit, toList_keyOf_lit] at h
    obtain ⟨hw, -, hv⟩ := sep_inj (digits_chars w) (digits_chars w')
      (by decide) (by decide) h
    injection hv with _ hv
    rw [toDigits_inj hw, toDigits_inj hv]
  case ident.ident x x' =>
    rw [toList_keyOf_ident, toList_keyOf_ident] at h
    rw [String.toList_injective h]
  case memRead.memRead m a m' a' =>
    rw [toList_keyOf_memRead, toList_keyOf_memRead] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨hm, -, hrest⟩ := sep_inj (identTokenB_chars ok1.1)
      (identTokenB_chars ok2.1) (by decide) (by decide) h
    obtain ⟨ha, -, -⟩ := sep_inj (identTokenB_chars ok1.2)
      (identTokenB_chars ok2.2) (by decide) (by decide) hrest
    rw [String.toList_injective hm, String.toList_injective ha]
  case memRead.slice m a x hi lo =>
    rw [toList_keyOf_memRead, toList_keyOf_slice] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨-, -, hrest⟩ := sep_inj (identTokenB_chars ok1.1)
      (identTokenB_chars ok2) (by decide) (by decide) h
    obtain ⟨-, hcd, -⟩ := sep_inj (identTokenB_chars ok1.2)
      (digits_chars hi) (by decide) (by decide) hrest
    exact absurd hcd (by decide)
  case slice.memRead x hi lo m a =>
    rw [toList_keyOf_slice, toList_keyOf_memRead] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨-, -, hrest⟩ := sep_inj (identTokenB_chars ok1)
      (identTokenB_chars ok2.1) (by decide) (by decide) h
    obtain ⟨-, hcd, -⟩ := sep_inj (digits_chars hi)
      (identTokenB_chars ok2.2) (by decide) (by decide) hrest
    exact absurd hcd (by decide)
  case slice.slice x hi lo x' hi' lo' =>
    rw [toList_keyOf_slice, toList_keyOf_slice] at h
    obtain ⟨hx, -, h1⟩ := sep_inj (identTokenB_chars ok1)
      (identTokenB_chars ok2) (by decide) (by decide) h
    obtain ⟨hhi, -, h2⟩ := sep_inj (digits_chars hi) (digits_chars hi')
      (by decide) (by decide) h1
    obtain ⟨hlo, -, -⟩ := sep_inj (digits_chars lo) (digits_chars lo')
      (by decide) (by decide) h2
    rw [String.toList_injective hx, toDigits_inj hhi, toDigits_inj hlo]
  case not.not x x' =>
    rw [toList_keyOf_not, toList_keyOf_not] at h
    injection h with _ h
    rw [String.toList_injective h]
  case bin.bin op x y op' x' y' =>
    rw [toList_keyOf_bin, toList_keyOf_bin] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨hx, -, hrest⟩ := sep_inj (identTokenB_chars ok1.1)
      (identTokenB_chars ok2.1) (by decide) (by decide) h
    obtain ⟨hop, hy⟩ := binop_sep hrest
    rw [String.toList_injective hx, hop, String.toList_injective hy]
  case bin.mux op x y c t f =>
    rw [toList_keyOf_bin, toList_keyOf_mux] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨-, -, hrest⟩ := sep_inj (identTokenB_chars ok1.1)
      (identTokenB_chars ok2.1.1) (by decide) (by decide) h
    cases op <;>
      · simp only [BinOp.keyChars, List.cons_append, List.nil_append] at hrest
        injection hrest with h1 _
        exact absurd h1 (by decide)
  case mux.bin c t f op x y =>
    rw [toList_keyOf_mux, toList_keyOf_bin] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨-, -, hrest⟩ := sep_inj (identTokenB_chars ok1.1.1)
      (identTokenB_chars ok2.1) (by decide) (by decide) h
    cases op <;>
      · simp only [BinOp.keyChars, List.cons_append, List.nil_append] at hrest
        injection hrest with h1 _
        exact absurd h1 (by decide)
  case slt.slt x y x' y' =>
    rw [toList_keyOf_slt, toList_keyOf_slt] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    repeat injection h with _ h
    obtain ⟨hx, -, h1⟩ := sep_inj (identTokenB_chars ok1.1)
      (identTokenB_chars ok2.1) (by decide) (by decide) h
    repeat injection h1 with _ h1
    obtain ⟨hy, -, -⟩ := sep_inj (identTokenB_chars ok1.2)
      (identTokenB_chars ok2.2) (by decide) (by decide) h1
    rw [String.toList_injective hx, String.toList_injective hy]
  case mux.mux c t f c' t' f' =>
    rw [toList_keyOf_mux, toList_keyOf_mux] at h
    simp only [rhsTokensOk, Bool.and_eq_true] at ok1 ok2
    obtain ⟨hc, -, h1⟩ := sep_inj (identTokenB_chars ok1.1.1)
      (identTokenB_chars ok2.1.1) (by decide) (by decide) h
    injection h1 with _ h1
    injection h1 with _ h1
    obtain ⟨ht, -, h2⟩ := sep_inj (identTokenB_chars ok1.1.2)
      (identTokenB_chars ok2.1.2) (by decide) (by decide) h1
    injection h2 with _ h2
    injection h2 with _ h2
    rw [String.toList_injective hc, String.toList_injective ht,
      String.toList_injective h2]
  case sext.sext k x b k' x' b' =>
    rw [toList_keyOf_sext, toList_keyOf_sext] at h
    injection h with _ h
    injection h with _ h
    obtain ⟨hk, -, h1⟩ := sep_inj (digits_chars k) (digits_chars k')
      (by decide) (by decide) h
    obtain ⟨hx, -, h2⟩ := sep_inj (identTokenB_chars ok1)
      (identTokenB_chars ok2) (by decide) (by decide) h1
    obtain ⟨hb, -, -⟩ := sep_inj (digits_chars b) (digits_chars b')
      (by decide) (by decide) h2
    rw [toDigits_inj hk, String.toList_injective hx, toDigits_inj hb]

/-! ## Agreement with `flatten`'s call sites

Each `freshWire w key rhs` call in `flatten` passes `key = keyOf rhs`.
`keyOf` copies the interpolations verbatim, so every site is definitional;
the lemmas below record one equation per call-site shape (the `.lit` site
instantiates `v := v.toNat`, the `.slice` site `hi := lo + w' - 1`, the
sext-widening site `k := w' - w, b := w - 1`, and both the `.zext` site and
the width-preserving sext site are the `.ident` equation). -/

theorem flatten_key_lit (w v : Nat) : s!"{w}'d{v}" = keyOf (.lit w v) := rfl

theorem flatten_key_ident (x : String) : s!"{x}" = keyOf (.ident x) := rfl

theorem flatten_key_memRead (m a : String) :
    s!"{m}[{a}]" = keyOf (.memRead m a) := rfl

theorem flatten_key_and (x y : String) :
    s!"{x} & {y}" = keyOf (.bin .and x y) := rfl

theorem flatten_key_or (x y : String) :
    s!"{x} | {y}" = keyOf (.bin .or x y) := rfl

theorem flatten_key_xor (x y : String) :
    s!"{x} ^ {y}" = keyOf (.bin .xor x y) := rfl

theorem flatten_key_add (x y : String) :
    s!"{x} + {y}" = keyOf (.bin .add x y) := rfl

theorem flatten_key_sub (x y : String) :
    s!"{x} - {y}" = keyOf (.bin .sub x y) := rfl

theorem flatten_key_mul (x y : String) :
    s!"{x} * {y}" = keyOf (.bin .mul x y) := rfl

theorem flatten_key_udiv (x y : String) :
    s!"{x} / {y}" = keyOf (.bin .udiv x y) := rfl

theorem flatten_key_urem (x y : String) :
    s!"{x} % {y}" = keyOf (.bin .urem x y) := rfl

theorem flatten_key_shl (x y : String) :
    s!"{x} << {y}" = keyOf (.bin .shl x y) := rfl

theorem flatten_key_shr (x y : String) :
    s!"{x} >> {y}" = keyOf (.bin .shr x y) := rfl

theorem flatten_key_eq (x y : String) :
    s!"{x} == {y}" = keyOf (.bin .eq x y) := rfl

theorem flatten_key_ult (x y : String) :
    s!"{x} < {y}" = keyOf (.bin .ult x y) := rfl

theorem flatten_key_not (x : String) : s!"~{x}" = keyOf (.not x) := rfl

theorem flatten_key_slt (x y : String) :
    s!"$signed({x}) < $signed({y})" = keyOf (.slt x y) := rfl

theorem flatten_key_mux (c t f : String) :
    s!"{c} ? {t} : {f}" = keyOf (.mux c t f) := rfl

theorem flatten_key_slice (x : String) (hi lo : Nat) :
    s!"{x}[{hi}:{lo}]" = keyOf (.slice x hi lo) := rfl

/-- The sext-widening site, in `flatten`'s exact `let sb := ...` shape. -/
theorem flatten_key_sext_wide (k : Nat) (x : String) (b : Nat) :
    "{" ++ ("{" ++ toString k ++ "{" ++ x ++ "[" ++ toString b ++ "]}}") ++
        ", " ++ x ++ "}" =
      keyOf (.sext k x b) := rfl

/-- The sext-narrowing site: its literal `":0]"` fragment agrees with the
general slice key at `lo = 0`. -/
theorem flatten_key_sext_narrow (x : String) (w' : Nat) :
    s!"{x}[{w' - 1}:0]" = keyOf (.slice x (w' - 1) 0) := by
  apply String.toList_injective
  rw [toList_keyOf_slice]
  show (x ++ "[" ++ toString (w' - 1) ++ ":0]").toList = _
  simp only [String.toList_append, toList_toString_nat, List.append_assoc]
  rfl

/-! ## Concrete sanity checks -/

example : keyOf (.lit 8 255) = "8'd255" := rfl
example : keyOf (.ident "n3") = "n3" := rfl
example : keyOf (.memRead "mem0" "n1") = "mem0[n1]" := rfl
example : keyOf (.slice "n2" 7 4) = "n2[7:4]" := rfl
example : keyOf (.not "n2") = "~n2" := rfl
example : keyOf (.bin .mul "a" "b") = "a * b" := rfl
example : keyOf (.bin .shl "a" "b") = "a << b" := rfl
example : keyOf (.bin .ult "a" "b") = "a < b" := rfl
example : keyOf (.slt "a" "b") = "$signed(a) < $signed(b)" := rfl
example : keyOf (.mux "c" "t" "f") = "c ? t : f" := rfl
example : keyOf (.sext 24 "n5" 7) = "{{24{n5[7]}}, n5}" := rfl

/-! ## Axiom audit -/

#print axioms identTokenB
#print axioms identTokenB_wireName
#print axioms keyOf
#print axioms rhsTokensOk
#print axioms sep_inj
#print axioms keyOf_injective
#print axioms flatten_key_lit
#print axioms flatten_key_ident
#print axioms flatten_key_memRead
#print axioms flatten_key_and
#print axioms flatten_key_or
#print axioms flatten_key_xor
#print axioms flatten_key_add
#print axioms flatten_key_sub
#print axioms flatten_key_mul
#print axioms flatten_key_shl
#print axioms flatten_key_shr
#print axioms flatten_key_eq
#print axioms flatten_key_ult
#print axioms flatten_key_not
#print axioms flatten_key_slt
#print axioms flatten_key_mux
#print axioms flatten_key_slice
#print axioms flatten_key_sext_wide
#print axioms flatten_key_sext_narrow

end Loom.Release.SSA
