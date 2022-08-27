/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.AlgebraicGeometry.Pullbacks
import Mathbin.AlgebraicGeometry.AffineScheme
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
noncomputable def specZIsTerminal : IsTerminal (Scheme.spec.obj (op <| CommRingₓₓ.of ℤ)) :=
  @IsTerminal.isTerminalObj _ _ Scheme.spec _ inferInstance (terminalOpOfInitial CommRingₓₓ.zIsInitial)

instance : HasTerminal Scheme :=
  has_terminal_of_has_terminal_of_preserves_limit Scheme.spec

instance : IsAffine (⊤_ Scheme.{u}) :=
  is_affine_of_iso (PreservesTerminal.iso Scheme.spec).inv

instance : HasFiniteLimits Scheme :=
  has_finite_limits_of_has_terminal_and_pullbacks

section Initial

/-- The map from the empty scheme. -/
@[simps]
def Scheme.emptyTo (X : Scheme.{u}) : ∅ ⟶ X :=
  ⟨{ base :=
        ⟨fun x => Pempty.elimₓ x, by
          continuity⟩,
      c := { app := fun U => CommRingₓₓ.punitIsTerminal.from _ } },
    fun x => Pempty.elimₓ x⟩

@[ext]
theorem Scheme.empty_ext {X : Scheme.{u}} (f g : ∅ ⟶ X) : f = g := by
  ext a
  exact Pempty.elimₓ a

theorem Scheme.eq_empty_to {X : Scheme.{u}} (f : ∅ ⟶ X) : f = Scheme.emptyTo X :=
  Scheme.empty_ext f (Scheme.emptyTo X)

instance (X : Scheme.{u}) : Unique (∅ ⟶ X) :=
  ⟨⟨Scheme.emptyTo _⟩, fun _ => Scheme.empty_ext _ _⟩

/-- The empty scheme is the initial object in the category of schemes. -/
def emptyIsInitial : IsInitial (∅ : Scheme.{u}) :=
  IsInitial.ofUnique _

@[simp]
theorem empty_is_initial_to : emptyIsInitial.to = Scheme.empty_to :=
  rfl

instance : IsEmpty Scheme.empty.Carrier :=
  show IsEmpty Pempty by
    infer_instance

instance Spec_punit_is_empty : IsEmpty (Scheme.spec.obj (op <| CommRingₓₓ.of PUnit)).Carrier :=
  ⟨PrimeSpectrum.punit⟩

instance (priority := 100) is_open_immersion_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty X.Carrier] :
    IsOpenImmersion f := by
  apply is_open_immersion.of_stalk_iso with { instances := false }
  · apply open_embedding_of_continuous_injective_open
    · continuity
      
    · rintro (i : X.carrier)
      exact isEmptyElim i
      
    · intro U hU
      convert is_open_empty
      ext
      apply (iff_falseₓ _).mpr
      exact fun x => isEmptyElim (show X.carrier from x.some)
      
    
  · rintro (i : X.carrier)
    exact isEmptyElim i
    

instance (priority := 100) is_iso_of_is_empty {X Y : Scheme} (f : X ⟶ Y) [IsEmpty Y.Carrier] : IsIso f := by
  haveI : IsEmpty X.carrier := ⟨fun x => isEmptyElim (show Y.carrier from f.1.base x)⟩
  have : epi f.1.base := by
    rw [Top.epi_iff_surjective]
    rintro (x : Y.carrier)
    exact isEmptyElim x
  apply is_open_immersion.to_iso

/-- A scheme is initial if its underlying space is empty . -/
noncomputable def isInitialOfIsEmpty {X : Scheme} [IsEmpty X.Carrier] : IsInitial X :=
  emptyIsInitial.of_iso (as_iso <| emptyIsInitial.to _)

/-- `Spec 0` is the initial object in the category of schemes. -/
noncomputable def specPunitIsInitial : IsInitial (Scheme.spec.obj (op <| CommRingₓₓ.of PUnit)) :=
  emptyIsInitial.of_iso (as_iso <| emptyIsInitial.to _)

instance (priority := 100) is_affine_of_is_empty {X : Scheme} [IsEmpty X.Carrier] : IsAffine X :=
  is_affine_of_iso (inv (emptyIsInitial.to X) ≫ emptyIsInitial.to (Scheme.spec.obj (op <| CommRingₓₓ.of PUnit)))

instance : HasInitial Scheme :=
  has_initial_of_unique Scheme.empty

instance initial_is_empty : IsEmpty (⊥_ Scheme).Carrier :=
  ⟨fun x => ((initial.to Scheme.empty : _).1.base x).elim⟩

theorem bot_is_affine_open (X : Scheme) : IsAffineOpen (⊥ : Opens X.Carrier) := by
  convert range_is_affine_open_of_open_immersion (initial.to X)
  ext
  exact (false_iffₓ _).mpr fun x => isEmptyElim (show (⊥_ Scheme).Carrier from x.some)

instance : HasStrictInitialObjects Scheme :=
  has_strict_initial_objects_of_initial_is_strict fun A f => by
    infer_instance

end Initial

end AlgebraicGeometry

