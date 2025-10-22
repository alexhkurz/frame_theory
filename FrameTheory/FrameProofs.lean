
import Mathlib.Order.Category.Frm
-- import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory Order Frm Set

-- #check CategoryTheory.Mono.right_cancellation
--
-- Frm mono-morphism

/-
playing around with Frm definitions, instances, etc.
-/
variable (C : Frame X)
variable (D : Set α)


#check C

/-
theorem Frame.distJoin {α : Type u} [Frame α] (x y z : α) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)  := by
  sorry

theorem Frame.sup_lub {α : Type u} [Frame α] (x : α) (S : Set α) (h : ∀ y ∈ S, y ⊑ x) : sup S ⊑ x := by
  sorry
-/

theorem sup_lub {α : Type u}  [Frame α] (F :  α ) (S : Set α ) (h : ∀ y ∈ S, y ≤  F) : sSup S ≤ F := by
  sorry
