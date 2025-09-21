
/-
Author: Tally Holcombe
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Lattice


class Frame (α : Type u) extends CompleteLattice α, DistribLattice α where
  inf_sup_le_sup_inf : ∀ (S: Set α) (a: α), a ⊓ sSup S = sSup { a ⊓ s | s ∈ S} -- infinite distributive law


open Frame

variable {α : Type u} [Frame α]

theorem Frame.sup_lub (x : α) (S : Set α) (h : ∀ y ∈ S, y ≤ x) : sSup S ≤ x := by
  have h2 := CompleteLattice.sSup_le S x h
  exact h2





lemma Frame.sup_refl (x : α) : x ⊔ x = x := by
  exact sup_idem x

lemma Frame.sup_associative ( x y z : α) : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  exact sup_assoc x y z

lemma Frame.sup_commutative (x y : α) : x ⊔ y = y ⊔ x := by
  exact sup_comm x y

lemma Frame.absorb_join (x y : α) : x ⊔ (x ⊓ y) = x := by
  exact sup_inf_self

lemma Frame.absorb_meet (x y : α) : x ⊓ (x ⊔ y) = x := by
  exact inf_sup_self

lemma Frame.left_meet_distributive (x y z : α) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
  exact inf_sup_left x y z
