
import Mathlib.Order.Category.Frm
-- import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Order.Hom.CompleteLattice
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

open CategoryTheory Order Frm Set

universe u

-- #check CategoryTheory.Mono.right_cancellation
--
-- Frm mono-morphism

/-
playing around with Frm definitions, instances, etc.
-/

variable (A B: Frm)
variable (C F: Frame X)
variable (D : Set α)





#check A.str.bot

#check FrameHom A B

variable (f : FrameHom A B)

#check f.cancel_left


/-
theorem Frame.distJoin {α : Type u} [Frame α] (x y z : α) : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)  := by
  sorry

theorem Frame.sup_lub {α : Type u} [Frame α] (x : α) (S : Set α) (h : ∀ y ∈ S, y ⊑ x) : sup S ⊑ x := by
  sorry
-/

/-
instance hasForgetToLat : HasForget₂ Frm Lat where
  forget₂.obj X := .of X
  forget₂.map f := Lat.ofHom f.hom
-/

#check Set
-- instance hasForgetToSet : HasForget₂ (Frm.{u}) (Set.{u}) where
--   sorry

-- instance hasForgetSetToSet : HasForget₂ Set Set where

#check CategoryTheory.forget₂ Frm Lat

#check CategoryTheory.forget Frm


universe v


/-
* Proof for Monotonicity in frame homomorphisms
-/

variable {L M : Type*} [Frame L] [Frame M]

-- `f : L → M` means: frame_hom L M
variable (f : L → M)

-- -- 1. A frame hom is monotone
theorem FrameHom.monotone (f : FrameHom A B) :
    Monotone f := by
  intro x y h
  -- we use x = x ⊓ y because x ≤ y in a frame
  have hx : x = x ⊓ y := by
    apply le_antisymm
    · simpa [inf_of_le_right h] using (le_inf_iff.mpr ⟨le_rfl, h⟩)
    · have : x ⊓ y ≤ x := inf_le_left; simp
  -- apply f to both sides
  have := congrArg f hx
  -- simplify with map_inf
  -- simpa using (this ▸ inf_le_right (f x) (f y))
  simpa using this

-- simpa checks if simplified result is the goal. if yes, closes goal
