/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Pullbacks
import Mathbin.AlgebraicGeometry.AffineSchemeCat
import Mathbin.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathbin.CategoryTheory.Limits.Constructions.Equalizers

/-!
# (Co)Limits of Schemes

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

/-- `Spec ℤ` is the terminal object in the category of schemes. -/
noncomputable def specZIsTerminal : IsTerminal (SchemeCat.spec.obj (op <| CommRingCat.of ℤ)) :=
  @IsTerminal.isTerminalObj _ _ SchemeCat.spec _ inferInstance (terminalOpOfInitial CommRingCat.zIsInitial)

instance : HasTerminal SchemeCat :=
  has_terminal_of_has_terminal_of_preserves_limit SchemeCat.spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  isAffineOfIso (PreservesTerminal.iso SchemeCat.spec).inv

instance : HasFiniteLimits SchemeCat :=
  has_finite_limits_of_has_terminal_and_pullbacks

section Initial

/-- The map from the empty scheme. -/
@[simps]
def SchemeCat.emptyTo (X : SchemeCat.{u}) : ∅ ⟶ X :=
  ⟨{ base := ⟨fun x => PEmpty.elim x, by continuity⟩, c := { app := fun U => CommRingCat.punitIsTerminal.from _ } },
    fun x => PEmpty.elim x⟩

@[ext]
theorem SchemeCat.empty_ext {X : SchemeCat.{u}} (f g : ∅ ⟶ X) : f = g := by
  ext a
  exact PEmpty.elim a

theorem SchemeCat.eq_empty_to {X : SchemeCat.{u}} (f : ∅ ⟶ X) : f = SchemeCat.emptyTo X :=
  SchemeCat.empty_ext f (SchemeCat.emptyTo X)

instance (X : SchemeCat.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨SchemeCat.emptyTo _⟩, fun _ => SchemeCat.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
def emptyIsInitial : IsInitial (∅ : SchemeCat.{u}) :=
  IsInitial.ofUnique _

@[simp]
theorem empty_is_initial_to : emptyIsInitial.to = Scheme.empty_to :=
  rfl

instance : IsEmpty SchemeCat.empty.Carrier :=
  show IsEmpty PEmpty by infer_instance

instance Spec_punit_is_empty : IsEmpty (SchemeCat.spec.obj (op <| CommRingCat.of PUnit)).Carrier :=
  ⟨PrimeSpectrum.punit⟩

instance (priority := 100) is_open_immersion_of_is_empty {X Y : SchemeCat} (f : X ⟶ Y) [IsEmpty X.Carrier] :
    IsOpenImmersion f := by
  apply (config := { instances := false }) is_open_immersion.of_stalk_iso
  · apply open_embedding_of_continuous_injective_open
    · continuity
      
    · rintro (i : X.carrier)
      exact isEmptyElim i
      
    · intro U hU
      convert is_open_empty
      ext
      apply (iff_false_iff _).mpr
      exact fun x => isEmptyElim (show X.carrier from x.some)
      
    
  · rintro (i : X.carrier)
    exact isEmptyElim i
    

instance (priority := 100) is_iso_of_is_empty {X Y : SchemeCat} (f : X ⟶ Y) [IsEmpty Y.Carrier] : IsIso f := by
  haveI : IsEmpty X.carrier := ⟨fun x => isEmptyElim (show Y.carrier from f.1.base x)⟩
  have : epi f.1.base := by
    rw [TopCat.epi_iff_surjective]
    rintro (x : Y.carrier)
    exact isEmptyElim x
  apply is_open_immersion.to_iso

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : SchemeCat} [IsEmpty X.Carrier] : IsInitial X :=
  emptyIsInitial.of_iso (as_iso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial (SchemeCat.spec.obj (op <| CommRingCat.of PUnit)) :=
  emptyIsInitial.of_iso (as_iso <| emptyIsInitial.to _)

instance (priority := 100) isAffineOfIsEmpty {X : SchemeCat} [IsEmpty X.Carrier] : IsAffine X :=
  isAffineOfIso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (SchemeCat.spec.obj (op <| CommRingCat.of PUnit)))

instance : HasInitial SchemeCat :=
  has_initial_of_unique SchemeCat.empty

instance initial_is_empty : IsEmpty (⊥_ Scheme).Carrier :=
  ⟨fun x => ((initial.to SchemeCat.empty : _).1.base x).elim⟩

theorem bot_is_affine_open (X : SchemeCat) : IsAffineOpen (⊥ : Opens X.Carrier) := by
  convert range_is_affine_open_of_open_immersion (initial.to X)
  ext
  exact (false_iff_iff _).mpr fun x => isEmptyElim (show (⊥_ Scheme).Carrier from x.some)

instance : HasStrictInitialObjects SchemeCat :=
  has_strict_initial_objects_of_initial_is_strict fun A f => by infer_instance

end Initial

end AlgebraicGeometry

