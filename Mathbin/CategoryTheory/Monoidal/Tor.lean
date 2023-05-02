/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.tor
! leanprover-community/mathlib commit 09f981f72d43749f1fa072deade828d9c1e185bb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Functor.LeftDerived
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

variable {C : Type _} [Category C] [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C]
  [HasZeroObject C] [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C]
  [HasProjectiveResolutions C]

variable (C)

#print CategoryTheory.Tor /-
/-- We define `Tor C n : C ⥤ C ⥤ C` by left-deriving in the second factor of `(X, Y) ↦ X ⊗ Y`. -/
@[simps]
def Tor (n : ℕ) : C ⥤ C ⥤ C
    where
  obj X := Functor.leftDerived ((tensoringLeft C).obj X) n
  map X Y f := NatTrans.leftDerived ((tensoringLeft C).map f) n
  map_id' X := by rw [(tensoring_left C).map_id, nat_trans.left_derived_id]
  map_comp' X Y Z f g := by rw [(tensoring_left C).map_comp, nat_trans.left_derived_comp]
#align category_theory.Tor CategoryTheory.Tor
-/

#print CategoryTheory.Tor' /-
/-- An alternative definition of `Tor`, where we left-derive in the first factor instead. -/
@[simps]
def Tor' (n : ℕ) : C ⥤ C ⥤ C :=
  Functor.flip
    { obj := fun X => Functor.leftDerived ((tensoringRight C).obj X) n
      map := fun X Y f => NatTrans.leftDerived ((tensoringRight C).map f) n
      map_id' := fun X => by rw [(tensoring_right C).map_id, nat_trans.left_derived_id]
      map_comp' := fun X Y Z f g => by
        rw [(tensoring_right C).map_comp, nat_trans.left_derived_comp] }
#align category_theory.Tor' CategoryTheory.Tor'
-/

open ZeroObject

/- warning: category_theory.Tor_succ_of_projective -> CategoryTheory.torSuccOfProjective is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_4 : CategoryTheory.MonoidalPreadditive.{u1, u2} C _inst_1 _inst_3 _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasEqualizers.{u2, u1} C _inst_1] [_inst_7 : CategoryTheory.Limits.HasCokernels.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3)] [_inst_8 : CategoryTheory.Limits.HasImages.{u2, u1} C _inst_1] [_inst_9 : CategoryTheory.Limits.HasImageMaps.{u2, u1} C _inst_1 _inst_8] [_inst_10 : CategoryTheory.HasProjectiveResolutions.{u2, u1} C _inst_1 _inst_5 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3) _inst_6 _inst_8] (X : C) (Y : C) [_inst_11 : CategoryTheory.Projective.{u2, u1} C _inst_1 Y] (n : Nat), CategoryTheory.Iso.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u1, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Tor.{u1, u2} C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) X) Y) (OfNat.ofNat.{u1} C 0 (OfNat.mk.{u1} C 0 (Zero.zero.{u1} C (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u1} C _inst_1 _inst_5))))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_4 : CategoryTheory.MonoidalPreadditive.{u1, u2} C _inst_1 _inst_3 _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasEqualizers.{u2, u1} C _inst_1] [_inst_7 : CategoryTheory.Limits.HasCokernels.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3)] [_inst_8 : CategoryTheory.Limits.HasImages.{u2, u1} C _inst_1] [_inst_9 : CategoryTheory.Limits.HasImageMaps.{u2, u1} C _inst_1 _inst_8] [_inst_10 : CategoryTheory.HasProjectiveResolutions.{u2, u1} C _inst_1 _inst_5 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3) _inst_6 _inst_8] (X : C) (Y : C) [_inst_11 : CategoryTheory.Projective.{u2, u1} C _inst_1 Y] (n : Nat), CategoryTheory.Iso.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u1, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u1, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Tor.{u1, u2} C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) X)) Y) (OfNat.ofNat.{u1} C 0 (Zero.toOfNat0.{u1} C (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u1} C _inst_1 _inst_5)))
Case conversion may be inaccurate. Consider using '#align category_theory.Tor_succ_of_projective CategoryTheory.torSuccOfProjectiveₓ'. -/
/-- The higher `Tor` groups for `X` and `Y` are zero if `Y` is projective. -/
def torSuccOfProjective (X Y : C) [Projective Y] (n : ℕ) : ((Tor C (n + 1)).obj X).obj Y ≅ 0 :=
  ((tensoringLeft C).obj X).leftDerivedObjProjectiveSucc n Y
#align category_theory.Tor_succ_of_projective CategoryTheory.torSuccOfProjective

/- warning: category_theory.Tor'_succ_of_projective -> CategoryTheory.tor'SuccOfProjective is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_4 : CategoryTheory.MonoidalPreadditive.{u1, u2} C _inst_1 _inst_3 _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasEqualizers.{u2, u1} C _inst_1] [_inst_7 : CategoryTheory.Limits.HasCokernels.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3)] [_inst_8 : CategoryTheory.Limits.HasImages.{u2, u1} C _inst_1] [_inst_9 : CategoryTheory.Limits.HasImageMaps.{u2, u1} C _inst_1 _inst_8] [_inst_10 : CategoryTheory.HasProjectiveResolutions.{u2, u1} C _inst_1 _inst_5 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3) _inst_6 _inst_8] (X : C) (Y : C) [_inst_11 : CategoryTheory.Projective.{u2, u1} C _inst_1 X] (n : Nat), CategoryTheory.Iso.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u2, u2, u1, u1} C _inst_1 C _inst_1 (CategoryTheory.Functor.obj.{u2, max u1 u2, u1, max u2 u1} C _inst_1 (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Tor'.{u1, u2} C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) X) Y) (OfNat.ofNat.{u1} C 0 (OfNat.mk.{u1} C 0 (Zero.zero.{u1} C (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u1} C _inst_1 _inst_5))))
but is expected to have type
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] [_inst_3 : CategoryTheory.Preadditive.{u2, u1} C _inst_1] [_inst_4 : CategoryTheory.MonoidalPreadditive.{u1, u2} C _inst_1 _inst_3 _inst_2] [_inst_5 : CategoryTheory.Limits.HasZeroObject.{u2, u1} C _inst_1] [_inst_6 : CategoryTheory.Limits.HasEqualizers.{u2, u1} C _inst_1] [_inst_7 : CategoryTheory.Limits.HasCokernels.{u2, u1} C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3)] [_inst_8 : CategoryTheory.Limits.HasImages.{u2, u1} C _inst_1] [_inst_9 : CategoryTheory.Limits.HasImageMaps.{u2, u1} C _inst_1 _inst_8] [_inst_10 : CategoryTheory.HasProjectiveResolutions.{u2, u1} C _inst_1 _inst_5 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} C _inst_1 _inst_3) _inst_6 _inst_8] (X : C) (Y : C) [_inst_11 : CategoryTheory.Projective.{u2, u1} C _inst_1 X] (n : Nat), CategoryTheory.Iso.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u2, succ u2, u1, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u2, u2, u1, u1} C _inst_1 C _inst_1 (Prefunctor.obj.{succ u2, max (succ u1) (succ u2), u1, max u1 u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Category.toCategoryStruct.{max u1 u2, max u1 u2} (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1))) (CategoryTheory.Functor.toPrefunctor.{u2, max u1 u2, u1, max u1 u2} C _inst_1 (CategoryTheory.Functor.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Functor.category.{u2, u2, u1, u1} C _inst_1 C _inst_1) (CategoryTheory.Tor'.{u1, u2} C _inst_1 _inst_2 _inst_3 _inst_4 _inst_5 _inst_6 _inst_7 _inst_8 _inst_9 _inst_10 (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) X)) Y) (OfNat.ofNat.{u1} C 0 (Zero.toOfNat0.{u1} C (CategoryTheory.Limits.HasZeroObject.zero'.{u2, u1} C _inst_1 _inst_5)))
Case conversion may be inaccurate. Consider using '#align category_theory.Tor'_succ_of_projective CategoryTheory.tor'SuccOfProjectiveₓ'. -/
/-- The higher `Tor'` groups for `X` and `Y` are zero if `X` is projective. -/
def tor'SuccOfProjective (X Y : C) [Projective X] (n : ℕ) : ((Tor' C (n + 1)).obj X).obj Y ≅ 0 :=
  by
  -- This unfortunately needs a manual `dsimp`, to avoid a slow unification problem.
  dsimp only [Tor', functor.flip]
  exact ((tensoring_right C).obj Y).leftDerivedObjProjectiveSucc n X
#align category_theory.Tor'_succ_of_projective CategoryTheory.tor'SuccOfProjective

end CategoryTheory

assert_not_exists Module.abelian

