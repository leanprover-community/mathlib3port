/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Pullbacks
import Mathbin.AlgebraicGeometry.AffineScheme

#align_import algebraic_geometry.limits from "leanprover-community/mathlib"@"d0b1936853671209a866fa35b9e54949c81116e2"

/-!
# (Co)Limits of Schemes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct various limits and colimits in the category of schemes.

* The existence of fibred products was shown in `algebraic_geometry/pullbacks.lean`.
* `Spec ℤ` is the terminal object.
* The preceding two results imply that `Scheme` has all finite limits.
* The empty scheme is the (strict) initial object.

## Todo

* Coproducts exists (and the forgetful functors preserve them).

-/


universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

#print AlgebraicGeometry.specZIsTerminal /-
/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal (Scheme.Spec.obj (op <| CommRingCat.of ℤ)) :=
  @IsTerminal.isTerminalObj _ _ Scheme.Spec _ inferInstance
    (terminalOpOfInitial CommRingCat.zIsInitial)
#align algebraic_geometry.Spec_Z_is_terminal AlgebraicGeometry.specZIsTerminal
-/

instance : HasTerminal Scheme :=
  hasTerminal_of_hasTerminal_of_preservesLimit Scheme.Spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  isAffineOfIso (PreservesTerminal.iso Scheme.Spec).inv

instance : HasFiniteLimits Scheme :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

section Initial

#print AlgebraicGeometry.Scheme.emptyTo /-
/-- The map from the empty scheme. -/
@[simps]
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{  base := ⟨fun x => PEmpty.elim x, by continuity⟩
      c := { app := fun U => CommRingCat.punitIsTerminal.from _ } }, fun x => PEmpty.elim x⟩
#align algebraic_geometry.Scheme.empty_to AlgebraicGeometry.Scheme.emptyTo
-/

#print AlgebraicGeometry.Scheme.empty_ext /-
@[ext]
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g := by ext a; exact PEmpty.elim a
#align algebraic_geometry.Scheme.empty_ext AlgebraicGeometry.Scheme.empty_ext
-/

#print AlgebraicGeometry.Scheme.eq_emptyTo /-
theorem Scheme.eq_emptyTo {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)
#align algebraic_geometry.Scheme.eq_empty_to AlgebraicGeometry.Scheme.eq_emptyTo
-/

instance (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

#print AlgebraicGeometry.emptyIsInitial /-
/-- The empty scheme is the initial object in the category of schemes. -/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _
#align algebraic_geometry.empty_is_initial AlgebraicGeometry.emptyIsInitial
-/

#print AlgebraicGeometry.emptyIsInitial_to /-
@[simp]
theorem emptyIsInitial_to : emptyIsInitial.to = Scheme.emptyTo :=
  rfl
#align algebraic_geometry.empty_is_initial_to AlgebraicGeometry.emptyIsInitial_to
-/

instance : IsEmpty Scheme.empty.carrier :=
  show IsEmpty PEmpty by infer_instance

#print AlgebraicGeometry.spec_punit_isEmpty /-
instance spec_punit_isEmpty : IsEmpty (Scheme.Spec.obj (op <| CommRingCat.of PUnit)).carrier :=
  ⟨PrimeSpectrum.punit⟩
#align algebraic_geometry.Spec_punit_is_empty AlgebraicGeometry.spec_punit_isEmpty
-/

#print AlgebraicGeometry.isOpenImmersion_of_isEmpty /-
instance (priority := 100) isOpenImmersion_of_isEmpty {X Y : Scheme} (f : X ⟶ Y)
    [IsEmpty X.carrier] : IsOpenImmersionCat f :=
  by
  apply (config := { instances := false }) is_open_immersion.of_stalk_iso
  · apply openEmbedding_of_continuous_injective_open
    · continuity
    · rintro (i : X.carrier); exact isEmptyElim i
    · intro U hU; convert isOpen_empty; ext; apply (iff_false_iff _).mpr
      exact fun x => isEmptyElim (show X.carrier from x.some)
  · rintro (i : X.carrier); exact isEmptyElim i
#align algebraic_geometry.is_open_immersion_of_is_empty AlgebraicGeometry.isOpenImmersion_of_isEmpty
-/

#print AlgebraicGeometry.isIso_of_isEmpty /-
instance (priority := 100) isIso_of_isEmpty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y.carrier] :
    IsIso f :=
  by
  haveI : IsEmpty X.carrier := ⟨fun x => isEmptyElim (show Y.carrier from f.1.base x)⟩
  have : epi f.1.base := by rw [TopCat.epi_iff_surjective]; rintro (x : Y.carrier);
    exact isEmptyElim x
  apply is_open_immersion.to_iso
#align algebraic_geometry.is_iso_of_is_empty AlgebraicGeometry.isIso_of_isEmpty
-/

#print AlgebraicGeometry.isInitialOfIsEmpty /-
/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X.carrier] : IsInitial X :=
  emptyIsInitial.of_iso (asIso <| emptyIsInitial.to _)
#align algebraic_geometry.is_initial_of_is_empty AlgebraicGeometry.isInitialOfIsEmpty
-/

#print AlgebraicGeometry.specPunitIsInitial /-
/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial (Scheme.Spec.obj (op <| CommRingCat.of PUnit)) :=
  emptyIsInitial.of_iso (asIso <| emptyIsInitial.to _)
#align algebraic_geometry.Spec_punit_is_initial AlgebraicGeometry.specPunitIsInitial
-/

#print AlgebraicGeometry.isAffine_of_isEmpty /-
instance (priority := 100) isAffine_of_isEmpty {X : Scheme} [IsEmpty X.carrier] : IsAffine X :=
  isAffineOfIso
    (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Scheme.Spec.obj (op <| CommRingCat.of PUnit)))
#align algebraic_geometry.is_affine_of_is_empty AlgebraicGeometry.isAffine_of_isEmpty
-/

instance : HasInitial Scheme :=
  hasInitial_of_unique Scheme.empty

#print AlgebraicGeometry.initial_isEmpty /-
instance initial_isEmpty : IsEmpty (⊥_ Scheme).carrier :=
  ⟨fun x => ((initial.to Scheme.empty : _).1.base x).elim⟩
#align algebraic_geometry.initial_is_empty AlgebraicGeometry.initial_isEmpty
-/

#print AlgebraicGeometry.bot_isAffineOpen /-
theorem bot_isAffineOpen (X : Scheme) : IsAffineOpen (⊥ : Opens X.carrier) :=
  by
  convert range_is_affine_open_of_open_immersion (initial.to X)
  ext
  exact (false_iff_iff _).mpr fun x => isEmptyElim (show (⊥_ Scheme).carrier from x.some)
#align algebraic_geometry.bot_is_affine_open AlgebraicGeometry.bot_isAffineOpen
-/

instance : HasStrictInitialObjects Scheme :=
  hasStrictInitialObjects_of_initial_is_strict fun A f => by infer_instance

end Initial

end AlgebraicGeometry

