import Mathbin.CategoryTheory.Derived
import Mathbin.CategoryTheory.Monoidal.Preadditive

/-!
# Tor, the left-derived functor of tensor product

We define `Tor C n : C ⥤ C ⥤ C`, by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`.

For now we have almost nothing to say about it!

It would be good to show that this is naturally isomorphic to the functor obtained
by left-deriving in the first factor, instead.
For now we define `Tor'` by left-deriving in the first factor,
but showing `Tor C n ≅ Tor' C n` will require a bit more theory!
Possibly it's best to axiomatize delta functors, and obtain a unique characterisation?

-/


noncomputable section

open CategoryTheory.Limits

open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {C : Type _} [category C] [monoidal_category C] [preadditive C] [monoidal_preadditive C] [has_zero_object C]
  [has_equalizers C] [has_cokernels C] [has_images C] [has_image_maps C] [has_projective_resolutions C]

variable (C)

/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def Tor (n : ℕ) : C ⥤ C ⥤ C where
  obj := fun X => functor.left_derived ((tensoring_left C).obj X) n
  map := fun X Y f => nat_trans.left_derived ((tensoring_left C).map f) n
  map_id' := fun X => by
    rw [(tensoring_left C).map_id, nat_trans.left_derived_id]
  map_comp' := fun X Y Z f g => by
    rw [(tensoring_left C).map_comp, nat_trans.left_derived_comp]

/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps]
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
  functor.flip
    { obj := fun X => functor.left_derived ((tensoring_right C).obj X) n,
      map := fun X Y f => nat_trans.left_derived ((tensoring_right C).map f) n,
      map_id' := fun X => by
        rw [(tensoring_right C).map_id, nat_trans.left_derived_id],
      map_comp' := fun X Y Z f g => by
        rw [(tensoring_right C).map_comp, nat_trans.left_derived_comp] }

open_locale ZeroObject

/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
def Tor_succ_of_projective (X Y : C) [projective Y] (n : ℕ) : ((Tor C (n + 1)).obj X).obj Y ≅ 0 :=
  ((tensoring_left C).obj X).leftDerivedObjProjectiveSucc n Y

/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
def Tor'_succ_of_projective (X Y : C) [projective X] (n : ℕ) : ((Tor' C (n + 1)).obj X).obj Y ≅ 0 := by
  dsimp only [Tor', functor.flip]
  exact ((tensoring_right C).obj Y).leftDerivedObjProjectiveSucc n X

end CategoryTheory

