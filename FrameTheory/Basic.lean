/-
Authors: Talitha Holcombe, Alexander Kurz
-/

import Mathlib.Data.Set.Operations

/-!
# Frames
-/

/-!
## Bounded meet semi-lattices
-/

class BoundedMeetSemiLattice (α : Type u) where
  meet : α → α → α
  top : α
  meet_assoc : ∀ a b c : α, meet (meet a b) c = meet a (meet b c)
  meet_comm : ∀ a b : α, meet a b = meet b a
  meet_idem : ∀ a : α, meet a a = a
  meet_top : ∀ a : α, meet a top = a

notation "⊤" => BoundedMeetSemiLattice.top
infixl:70 " ⊓ " => BoundedMeetSemiLattice.meet

open BoundedMeetSemiLattice

example {α : Type u} [BoundedMeetSemiLattice α] (a b : α) : a ⊓ b = b ⊓ a := by
  exact meet_comm a b

def BoundedMeetSemiLattice.leq {α : Type u} [BoundedMeetSemiLattice α] (x y : α) : Prop :=
  x ⊓ y = x

notation:50 x " ⊑ " y => BoundedMeetSemiLattice.leq x y

theorem BoundedMeetSemiLattice.leq_refl {α : Type u} [BoundedMeetSemiLattice α] (x : α) : x ⊑ x := by
  have h : x ⊓ x = x := meet_idem x
  exact h

theorem BoundedMeetSemiLattice.leq_antisymm {α : Type u} [BoundedMeetSemiLattice α] {x y : α} (h1 : x ⊑ y) (h2 : y ⊑ x) : x = y := by
  sorry

theorem BoundedMeetSemiLattice.leq_trans {α : Type u} [BoundedMeetSemiLattice α] {x y z : α} (h1 : x ⊑ y) (h2 : y ⊑ z) : x ⊑ z := by
  sorry

/-!
## Frames
-/

class Frame (α : Type u) extends BoundedMeetSemiLattice α where
  sup : Set α → α
  sup_insert : ∀ (a : α) (S : Set α), sup (Set.insert a S) = a ⊓ sup S
  dist : ∀ (x : α) (S : Set α),
    x ⊓ sup S = sup (Set.image (fun y => x ⊓ y) S)

open Frame
theorem Frame.sup_lub {α : Type u} [Frame α] (x : α) (S : Set α) (h : ∀ y ∈ S, y ⊑ x) : sup S ⊑ x := by
  sorry