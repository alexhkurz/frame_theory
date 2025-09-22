
/-
Author: Tally Holcombe
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder


-- class Frame (α : Type u) extends CompleteLattice α where
--   inf_sup_le_sup_inf : ∀ (S: Set α) (a: α), a ⊓ sSup S = sSup { a ⊓ s | s ∈ S} -- frame distributive law


-- open Frame

-- variable {α : Type u} [Frame α]

-- theorem Frame.sup_lub (x : α) (S : Set α) (h : ∀ y ∈ S, y ≤ x) : sSup S ≤ x := by
--   have h2 := CompleteLattice.sSup_le S x h
--   exact h2


-- lemma Frame.sup_refl (x : α) : x ⊔ x = x := by
--   exact sup_idem x

-- lemma Frame.sup_associative ( x y z : α) : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
--   exact sup_assoc x y z

-- lemma Frame.sup_commutative (x y : α) : x ⊔ y = y ⊔ x := by
--   exact sup_comm x y

-- lemma Frame.absorb_join (x y : α) : x ⊔ (x ⊓ y) = x := by
--   exact sup_inf_self

-- lemma Frame.absorb_meet (x y : α) : x ⊓ (x ⊔ y) = x := by
--   exact inf_sup_self

-- lemma Frame.left_meet_distributive (x y z : α) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) := by
--   exact inf_sup_left x y z



class Frame (α : Type u) extends CompleteSemilatticeSup α, SemilatticeInf α, BoundedOrder α, Lattice α where
  inf_sup_le_sup : ∀ (a : α) (S : Set α), inf a (sSup S) = sSup {inf a s | s ∈ S} -- = or ≤ ?
  protected leq_sup_inf : ∀ x y z : α, inf (sup x  y) (sup x  z) ≤ sup x (inf y z)     -- trait from DistribLattice
  protected leq_inf_sup : ∀ x y z : α, sup (inf x y) (inf x z) ≤ inf x (sup y z)

  protected sup_inf_leq : ∀ x y z : α, sup x (inf y z) ≤ inf (sup x y) (sup x z)
  protected inf_sup_leq : ∀ x y z : α, inf x (sup y z) ≤ sup (inf x y) (inf x z)


open Frame

variable {α : Type u} [Frame α]

theorem leq_sup_inf (x y z : α) : (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z) := by
  exact Frame.leq_sup_inf x y z

theorem leq_inf_sup (x y z : α) : (x ⊓ y) ⊔ (x ⊓ z) ≤ x ⊓ (y ⊔ z) := by
  exact Frame.leq_inf_sup x y z


theorem sup_inf_leq (x y z : α) : x ⊔ (y ⊓ z) ≤ (x ⊔ y) ⊓ (x ⊔ z) := by
  exact Frame.sup_inf_leq x y z

theorem inf_sup_leq (x y z : α) : x ⊓ (y ⊔ z) ≤ (x ⊓ y) ⊔ (x ⊓ z) := by
  exact Frame.inf_sup_leq x y z


-- join-distributive
theorem Frame.sup_inf_left (x y z : α) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
  le_antisymm (sup_inf_leq x y z) (leq_sup_inf x y z)

-- meet-distributive
theorem Frame.inf_sup_left (x y z : α) : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) :=
  le_antisymm (inf_sup_leq x y z) (leq_inf_sup x y z)

-- LUB
theorem Frame.sup_lub (x : α) (S : Set α) (h : ∀ y ∈ S, y ≤ x) : sSup S ≤ x := by
  exact CompleteSemilatticeSup.sSup_le S x h

-- axioms
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
