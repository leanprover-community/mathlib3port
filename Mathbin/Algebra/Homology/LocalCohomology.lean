/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Scott Morrison, Jake Levinson, Sam van Gool
-/
import RingTheory.Ideal.Basic
import Algebra.Category.ModuleCat.Colimits
import Algebra.Category.ModuleCat.Projective
import CategoryTheory.Abelian.Ext
import CategoryTheory.Limits.Final
import RingTheory.Noetherian

#align_import algebra.homology.local_cohomology from "leanprover-community/mathlib"@"893964fc28cefbcffc7cb784ed00a2895b4e65cf"

/-!
# Local cohomology.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Establish long exact sequence(s) in local cohomology
-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

noncomputable section

universe u v v'

namespace localCohomology

-- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`.
section

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]

#print localCohomology.ringModIdeals /-
/-- The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I`  -/
def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R
    where
  obj t := ModuleCat.of R <| R ⧸ I.obj t
  map s t w := Submodule.mapQ _ _ LinearMap.id (I.map w).down.down
#align local_cohomology.ring_mod_ideals localCohomology.ringModIdeals
-/

#print localCohomology.moduleCat_enoughProjectives' /-
-- TODO:  Once this file is ported, move this file to the right location.
instance moduleCat_enoughProjectives' : EnoughProjectives (ModuleCat.{u} R) :=
  ModuleCat.moduleCat_enoughProjectives.{u}
#align local_cohomology.Module_enough_projectives' localCohomology.moduleCat_enoughProjectives'
-/

#print localCohomology.diagram /-
/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
def diagram (I : D ⥤ Ideal R) (i : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i
#align local_cohomology.diagram localCohomology.diagram
-/

end

section

-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

#print localCohomology.ofDiagram /-
/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent definitions of the usual local cohomology with support
in an ideal `J`, `local_cohomology` and `local_cohomology.of_self_le_radical`.

 -/
/-- `local_cohomology.of_diagram I i` is the the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  colimit (diagram.{max u v, v} I i)
#align local_cohomology.of_diagram localCohomology.ofDiagram
-/

end

section

variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]

variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)

#print localCohomology.diagramComp /-
/-- Local cohomology along a composition of diagrams. -/
def diagramComp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _
#align local_cohomology.diagram_comp localCohomology.diagramComp
-/

#print localCohomology.isoOfFinal /-
/-- Local cohomology agrees along precomposition with a cofinal diagram. -/
def isoOfFinal [Functor.Initial I'] (i : ℕ) :
    ofDiagram.{max u v, v'} (I' ⋙ I) i ≅ ofDiagram.{max u v', v} I i :=
  HasColimit.isoOfNatIso (diagramComp _ _ _) ≪≫ Functor.Final.colimitIso _ _
#align local_cohomology.iso_of_final localCohomology.isoOfFinal
-/

end

section Diagrams

variable {R : Type u} [CommRing R]

#print localCohomology.idealPowersDiagram /-
/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
def idealPowersDiagram (J : Ideal R) : ℕᵒᵖ ⥤ Ideal R
    where
  obj t := J ^ unop t
  map s t w := ⟨⟨Ideal.pow_le_pow w.unop.down.down⟩⟩
#align local_cohomology.ideal_powers_diagram localCohomology.idealPowersDiagram
-/

#print localCohomology.SelfLERadical /-
/-- The full subcategory of all ideals with radical containing `J` -/
def SelfLERadical (J : Ideal R) : Type u :=
  FullSubcategory fun J' : Ideal R => J ≤ J'.radical
deriving Category
#align local_cohomology.self_le_radical localCohomology.SelfLERadical
-/

#print localCohomology.SelfLERadical.inhabited /-
instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J)
    where default := ⟨J, Ideal.le_radical⟩
#align local_cohomology.self_le_radical.inhabited localCohomology.SelfLERadical.inhabited
-/

#print localCohomology.selfLERadicalDiagram /-
/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  fullSubcategoryInclusion _
#align local_cohomology.self_le_radical_diagram localCohomology.selfLERadicalDiagram
-/

end Diagrams

end localCohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`local_cohomology`), then in terms of *all* ideals with radical
containing `J` (`local_cohomology.of_self_le_radical`). -/


section ModelsForLocalCohomology

open localCohomology

variable {R : Type u} [CommRing R]

#print localCohomology /-
/-- `local_cohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`. -/
def localCohomology (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram (idealPowersDiagram J) i
#align local_cohomology localCohomology
-/

#print localCohomology.ofSelfLERadical /-
/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
def localCohomology.ofSelfLERadical (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i
#align local_cohomology.of_self_le_radical localCohomology.ofSelfLERadical
-/

end ModelsForLocalCohomology

namespace localCohomology

/-!
Showing equivalence of different definitions of local cohomology.
  * `local_cohomology.iso_self_le_radical` gives the isomorphism
      `local_cohomology J i ≅ local_cohomology.of_self_le_radical J i`
  * `local_cohomology.iso_of_same_radical` gives the isomorphism
      `local_cohomology J i ≅ local_cohomology K i` when `J.radical = K.radical`.
-/


section LocalCohomologyEquiv

variable {R : Type u} [CommRing R]

#print localCohomology.idealPowersToSelfLERadical /-
/-- Lifting `ideal_powers_diagram J` from a diagram valued in `ideals R` to a diagram
valued in `self_le_radical J`. -/
def idealPowersToSelfLERadical (J : Ideal R) : ℕᵒᵖ ⥤ SelfLERadical J :=
  FullSubcategory.lift _ (idealPowersDiagram J) fun k =>
    by
    change _ ≤ (J ^ unop k).radical
    cases unop k
    · simp only [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow _ n.succ_pos, Ideal.le_radical]
#align local_cohomology.ideal_powers_to_self_le_radical localCohomology.idealPowersToSelfLERadical
-/

variable {I J K : Ideal R}

#print localCohomology.Ideal.exists_pow_le_of_le_radical_of_fG /-
/-- PORTING NOTE: This lemma should probably be moved to `ring_theory/finiteness.lean`
to be near `ideal.exists_radical_pow_le_of_fg`, which it generalizes.
-/
theorem Ideal.exists_pow_le_of_le_radical_of_fG (hIJ : I ≤ J.radical) (hJ : J.radical.FG) :
    ∃ k : ℕ, I ^ k ≤ J :=
  by
  obtain ⟨k, hk⟩ := J.exists_radical_pow_le_of_fg hJ
  use k
  calc
    I ^ k ≤ J.radical ^ k := Ideal.pow_mono hIJ _
    _ ≤ J := hk
#align local_cohomology.ideal.exists_pow_le_of_le_radical_of_fg localCohomology.Ideal.exists_pow_le_of_le_radical_of_fG
-/

#print localCohomology.ideal_powers_initial /-
/-- The diagram of powers of `J` is initial in the diagram of all ideals with
radical containing `J`. This uses noetherianness. -/
instance ideal_powers_initial [hR : IsNoetherian R R] :
    Functor.Initial (idealPowersToSelfLERadical J)
    where out J' := by
    apply @zigzag_is_connected _ _ _
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      cases' le_total (unop j1.left) (unop j2.left) with h
      right; exact ⟨costructured_arrow.hom_mk (hom_of_le h).op (AsTrue.get trivial)⟩
      left; exact ⟨costructured_arrow.hom_mk (hom_of_le h).op (AsTrue.get trivial)⟩
    · obtain ⟨k, hk⟩ := ideal.exists_pow_le_of_le_radical_of_fg J'.2 (is_noetherian_def.mp hR _)
      exact ⟨costructured_arrow.mk (⟨⟨hk⟩⟩ : (ideal_powers_to_self_le_radical J).obj (op k) ⟶ J')⟩
#align local_cohomology.ideal_powers_initial localCohomology.ideal_powers_initial
-/

#print localCohomology.isoSelfLERadical /-
/-- Local cohomology (defined in terms of powers of `J`) agrees with local
cohomology computed over all ideals with radical containing `J`. -/
def isoSelfLERadical (J : Ideal R) [IsNoetherian R R] (i : ℕ) :
    localCohomology.ofSelfLERadical J i ≅ localCohomology J i :=
  (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical J) (selfLERadicalDiagram J)
        i).symm ≪≫
    HasColimit.isoOfNatIso (Iso.refl _)
#align local_cohomology.iso_self_le_radical localCohomology.isoSelfLERadical
-/

#print localCohomology.SelfLERadical.cast /-
/-- Casting from the full subcategory of ideals with radical containing `J` to the full
subcategory of ideals with radical containing `K`. -/
def SelfLERadical.cast (hJK : J.radical = K.radical) : SelfLERadical J ⥤ SelfLERadical K :=
  FullSubcategory.map fun L hL =>
    by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL
#align local_cohomology.self_le_radical.cast localCohomology.SelfLERadical.cast
-/

#print localCohomology.SelfLERadical.castIsEquivalence /-
-- TODO generalize this to the equivalence of full categories for any `iff`.
instance SelfLERadical.castIsEquivalence (hJK : J.radical = K.radical) :
    CategoryTheory.Functor.IsEquivalence (SelfLERadical.cast hJK)
    where
  inverse := SelfLERadical.cast hJK.symm
  unitIso := by tidy
  counitIso := by tidy
#align local_cohomology.self_le_radical.cast_is_equivalence localCohomology.SelfLERadical.castIsEquivalence
-/

#print localCohomology.SelfLERadical.isoOfSameRadical /-
/-- The natural isomorphism between local cohomology defined using the `of_self_le_radical`
diagram, assuming `J.radical = K.radical`. -/
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : ℕ) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm
#align local_cohomology.self_le_radical.iso_of_same_radical localCohomology.SelfLERadical.isoOfSameRadical
-/

#print localCohomology.isoOfSameRadical /-
/-- Local cohomology agrees on ideals with the same radical. -/
def isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : ℕ) :
    localCohomology J i ≅ localCohomology K i :=
  (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i
#align local_cohomology.iso_of_same_radical localCohomology.isoOfSameRadical
-/

end LocalCohomologyEquiv

end localCohomology

