
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




/-
* Proof for Monotonicity in frame homomorphisms
-/

-- variable {L M : Type*} [Frame L] [Frame M]

-- -- `f : L → M` means: frame_hom L M
-- variable (f : L → M)

-- A frame hom is monotone
-- FrameHom.monotone? or framehom_monotone(?) because not extending FrameHom
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
  simpa using this

-- simpa checks if simplified result is the goal. if yes, closes goal



-- A frame hom preserves ⊥
theorem frameHom_map_bot (f : FrameHom A B) : f ⊥ = (⊥ : B) := by
  simp

-- frame hom preserves finite meet
lemma frameHom_map_inf (a b : A) (f : FrameHom A B): f (a ⊓ b) = f a ⊓ f b := by
  simp
