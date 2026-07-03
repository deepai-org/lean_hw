/-!
# Pointwise function update

The one combinator every table-as-function state representation needs
(decision D5). Kept in-house: the toolchain has no library dependencies.
-/

namespace Loom.Fun

/-- Update `f` at `a` to `b`. -/
def update {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem update_same {α β : Type} [DecidableEq α]
    (f : α → β) (a : α) (b : β) : update f a b a = b := by
  simp [update]

@[simp] theorem update_ne {α β : Type} [DecidableEq α]
    (f : α → β) (a x : α) (b : β) (h : x ≠ a) : update f a b x = f x := by
  simp [update, h]

end Loom.Fun
