/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.sheaves.sheaf_condition.opens_le_cover
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sheaves.SheafCondition.Sites

/-!
# Another version of the sheaf condition.

Given a family of open sets `U : ι → opens X` we can form the subcategory
`{ V : opens X // ∃ i, V ≤ U i }`, which has `supr U` as a cocone.

The sheaf condition on a presheaf `F` is equivalent to
`F` sending the opposite of this cocone to a limit cone in `C`, for every `U`.

This condition is particularly nice when checking the sheaf condition
because we don't need to do any case bashing
(depending on whether we're looking at single or double intersections,
or equivalently whether we're looking at the first or second object in an equalizer diagram).

## Main statement

`Top.presheaf.is_sheaf_iff_is_sheaf_opens_le_cover`: for a presheaf on a topological space,
the sheaf condition in terms of Grothendieck topology is equivalent to the `opens_le_cover`
sheaf condition. This result will be used to further connect to other sheaf conditions on spaces,
like `pairwise_intersections` and `equalizer_products`.

## References
* This is the definition Lurie uses in [Spectral Algebraic Geometry][LurieSAG].
-/


universe w v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopologicalSpace.Opens Opposite

namespace TopCat

variable {C : Type u} [Category.{v} C]

variable {X : TopCat.{w}} (F : Presheaf C X) {ι : Type w} (U : ι → Opens X)

namespace Presheaf

namespace SheafCondition

/-- The category of open sets contained in some element of the cover.
-/
def OpensLeCover : Type w :=
  FullSubcategory fun V : Opens X => ∃ i, V ≤ U i deriving Category
#align Top.presheaf.sheaf_condition.opens_le_cover TopCat.Presheaf.SheafCondition.OpensLeCover

instance [Inhabited ι] : Inhabited (OpensLeCover U) :=
  ⟨⟨⊥, default, bot_le⟩⟩

namespace OpensLeCover

variable {U}

/-- An arbitrarily chosen index such that `V ≤ U i`.
-/
def index (V : OpensLeCover U) : ι :=
  V.property.some
#align Top.presheaf.sheaf_condition.opens_le_cover.index TopCat.Presheaf.SheafCondition.OpensLeCover.index

/-- The morphism from `V` to `U i` for some `i`.
-/
def homToIndex (V : OpensLeCover U) : V.obj ⟶ U (index V) :=
  V.property.some_spec.Hom
#align Top.presheaf.sheaf_condition.opens_le_cover.hom_to_index TopCat.Presheaf.SheafCondition.OpensLeCover.homToIndex

end OpensLeCover

/-- `supr U` as a cocone over the opens sets contained in some element of the cover.

(In fact this is a colimit cocone.)
-/
def opensLeCoverCocone : Cocone (fullSubcategoryInclusion _ : OpensLeCover U ⥤ Opens X)
    where
  x := supᵢ U
  ι := { app := fun V : OpensLeCover U => V.homToIndex ≫ Opens.leSupr U _ }
#align Top.presheaf.sheaf_condition.opens_le_cover_cocone TopCat.Presheaf.SheafCondition.opensLeCoverCocone

end SheafCondition

open SheafCondition

/-- An equivalent formulation of the sheaf condition
(which we prove equivalent to the usual one below as
`is_sheaf_iff_is_sheaf_opens_le_cover`).

A presheaf is a sheaf if `F` sends the cone `(opens_le_cover_cocone U).op` to a limit cone.
(Recall `opens_le_cover_cocone U`, has cone point `supr U`,
mapping down to any `V` which is contained in some `U i`.)
-/
def IsSheafOpensLeCover : Prop :=
  ∀ ⦃ι : Type w⦄ (U : ι → Opens X), Nonempty (IsLimit (F.mapCone (opensLeCoverCocone U).op))
#align Top.presheaf.is_sheaf_opens_le_cover TopCat.Presheaf.IsSheafOpensLeCover

section

variable {Y : Opens X} (hY : Y = supᵢ U)

/-- Given a family of opens `U` and an open `Y` equal to the union of opens in `U`, we may
    take the presieve on `Y` associated to `U` and the sieve generated by it, and form the
    full subcategory (subposet) of opens contained in `Y` (`over Y`) consisting of arrows
    in the sieve. This full subcategory is equivalent to `opens_le_cover U`, the (poset)
    category of opens contained in some `U i`. -/
@[simps]
def generateEquivalenceOpensLe :
    (FullSubcategory fun f : Over Y => (Sieve.generate (presieveOfCoveringAux U Y)).arrows f.Hom) ≌
      OpensLeCover U
    where
  Functor :=
    { obj := fun f =>
        ⟨f.1.left,
          let ⟨_, h, _, ⟨i, hY⟩, _⟩ := f.2
          ⟨i, hY ▸ h.le⟩⟩
      map := fun _ _ g => g.left }
  inverse :=
    { obj := fun V =>
        ⟨Over.mk
            (hY.substr
                (let ⟨i, h⟩ := V.2
                h.trans (le_supᵢ U i))).Hom,
          let ⟨i, h⟩ := V.2
          ⟨U i, h.Hom, (hY.substr (le_supᵢ U i)).Hom, ⟨i, rfl⟩, rfl⟩⟩
      map := fun _ _ g => Over.homMk g }
  unitIso :=
    eq_to_iso <|
      CategoryTheory.Functor.ext
        (by
          rintro ⟨⟨_, _⟩, _⟩
          dsimp
          congr <;> ext)
        (by
          intros
          ext)
  counitIso :=
    eq_to_iso <|
      CategoryTheory.Functor.hext
        (by
          intro
          ext
          rfl)
        (by
          intros
          rfl)
#align Top.presheaf.generate_equivalence_opens_le TopCat.Presheaf.generateEquivalenceOpensLe

/-- Given a family of opens `opens_le_cover_cocone U` is essentially the natural cocone
    associated to the sieve generated by the presieve associated to `U` with indexing
    category changed using the above equivalence. -/
@[simps]
def whiskerIsoMapGenerateCocone :
    (F.mapCone (opensLeCoverCocone U).op).whisker (generateEquivalenceOpensLe U hY).op.Functor ≅
      F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.Cocone.op
    where
  Hom :=
    { Hom := F.map (eqToHom (congr_arg op hY.symm))
      w' := fun j => by
        erw [← F.map_comp]
        congr }
  inv :=
    { Hom := F.map (eqToHom (congr_arg op hY))
      w' := fun j => by
        erw [← F.map_comp]
        congr }
  hom_inv_id' := by
    ext
    simp [eq_to_hom_map]
  inv_hom_id' := by
    ext
    simp [eq_to_hom_map]
#align Top.presheaf.whisker_iso_map_generate_cocone TopCat.Presheaf.whiskerIsoMapGenerateCocone

/-- Given a presheaf `F` on the topological space `X` and a family of opens `U` of `X`,
    the natural cone associated to `F` and `U` used in the definition of
    `F.is_sheaf_opens_le_cover` is a limit cone iff the natural cone associated to `F`
    and the sieve generated by the presieve associated to `U` is a limit cone. -/
def isLimitOpensLeEquivGenerate₁ :
    IsLimit (F.mapCone (opensLeCoverCocone U).op) ≃
      IsLimit (F.mapCone (Sieve.generate (presieveOfCoveringAux U Y)).arrows.Cocone.op) :=
  (IsLimit.whiskerEquivalenceEquiv (generateEquivalenceOpensLe U hY).op).trans
    (IsLimit.equivIsoLimit (whiskerIsoMapGenerateCocone F U hY))
#align Top.presheaf.is_limit_opens_le_equiv_generate₁ TopCat.Presheaf.isLimitOpensLeEquivGenerate₁

/-- Given a presheaf `F` on the topological space `X` and a presieve `R` whose generated sieve
    is covering for the associated Grothendieck topology (equivalently, the presieve is covering
    for the associated pretopology), the natural cone associated to `F` and the family of opens
    associated to `R` is a limit cone iff the natural cone associated to `F` and the generated
    sieve is a limit cone.
    Since only the existence of a 1-1 correspondence will be used, the exact definition does
    not matter, so tactics are used liberally. -/
def isLimitOpensLeEquivGenerate₂ (R : Presieve Y)
    (hR : Sieve.generate R ∈ Opens.grothendieckTopology X Y) :
    IsLimit (F.mapCone (opensLeCoverCocone (coveringOfPresieve Y R)).op) ≃
      IsLimit (F.mapCone (Sieve.generate R).arrows.Cocone.op) :=
  by
  convert
      is_limit_opens_le_equiv_generate₁ F (covering_of_presieve Y R)
        (covering_of_presieve.supr_eq_of_mem_grothendieck Y R hR).symm using
      2 <;>
    rw [covering_presieve_eq_self R]
#align Top.presheaf.is_limit_opens_le_equiv_generate₂ TopCat.Presheaf.isLimitOpensLeEquivGenerate₂

/-- A presheaf `(opens X)ᵒᵖ ⥤ C` on a topological space `X` is a sheaf on the site `opens X` iff
    it satisfies the `is_sheaf_opens_le_cover` sheaf condition. The latter is not the
    official definition of sheaves on spaces, but has the advantage that it does not
    require `has_products C`. -/
theorem isSheaf_iff_isSheafOpensLeCover : F.IsSheaf ↔ F.IsSheafOpensLeCover :=
  by
  refine' (presheaf.is_sheaf_iff_is_limit _ _).trans _
  constructor
  · intro h ι U
    rw [(is_limit_opens_le_equiv_generate₁ F U rfl).nonempty_congr]
    apply h
    apply presieve_of_covering.mem_grothendieck_topology
  · intro h Y S
    rw [← sieve.generate_sieve S]
    intro hS
    rw [← (is_limit_opens_le_equiv_generate₂ F S hS).nonempty_congr]
    apply h
#align Top.presheaf.is_sheaf_iff_is_sheaf_opens_le_cover TopCat.Presheaf.isSheaf_iff_isSheafOpensLeCover

end

end Presheaf

end TopCat

