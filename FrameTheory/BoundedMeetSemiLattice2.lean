import Mathlib.Algebra.Group.Defs

class BoundedMeetSemiLattice2 (α : Type u) extends AddCommMonoid α where
  add_idem : ∀ x : α, x + x = x

notation "⊤2" => (0)
infixl:70 " ⊓2 " => (· + ·)

example {α : Type u} [BoundedMeetSemiLattice2 α] (a b : α) : a ⊓2 b = b ⊓2 a := by
  exact add_comm a b
