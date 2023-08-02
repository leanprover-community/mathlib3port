/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Equivalence

#align_import algebraic_topology.dold_kan.compatibility from "leanprover-community/mathlib"@"18ee599842a5d17f189fe572f0ed8cb1d064d772"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 Tools for compatibilities between Dold-Kan equivalences

The purpose of this file is to introduce tools which will enable the
construction of the Dold-Kan equivalence `simplicial_object C ≌ chain_complex C ℕ`
for a pseudoabelian category `C` from the equivalence
`karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)` and the two
equivalences `simplicial_object C ≅ karoubi (simplicial_object C)` and
`chain_complex C ℕ ≅ karoubi (chain_complex C ℕ)`.

It is certainly possible to get an equivalence `simplicial_object C ≌ chain_complex C ℕ`
using a compositions of the three equivalences above, but then neither the functor
nor the inverse would have good definitional properties. For example, it would be better
if the inverse functor of the equivalence was exactly the functor
`Γ₀ : simplicial_object C ⥤ chain_complex C ℕ` which was constructed in `functor_gamma.lean`.

In this file, given four categories `A`, `A'`, `B`, `B'`, equivalences `eA : A ≅ A'`,
`eB : B ≅ B'`, `e' : A' ≅ B'`, functors `F : A ⥤ B'`, `G : B ⥤ A` equipped with certain
compatibilities, we construct successive equivalences:
- `equivalence₀` from `A` to `B'`, which is the composition of `eA` and `e'`.
- `equivalence₁` from `A` to `B'`, with the same inverse functor as `equivalence₀`,
but whose functor is `F`.
- `equivalence₂` from `A` to `B`, which is the composition of `equivalence₁` and the
inverse of `eB`:
- `equivalence` from `A` to `B`, which has the same functor `F ⋙ eB.inverse` as `equivalence₂`,
but whose inverse functor is `G`.

When extra assumptions are given, we shall also provide simplification lemmas for the
unit and counit isomorphisms of `equivalence`. (TODO)

-/


open CategoryTheory CategoryTheory.Category

namespace AlgebraicTopology

namespace DoldKan

namespace Compatibility

variable {A A' B B' : Type _} [Category A] [Category A'] [Category B] [Category B'] (eA : A ≌ A')
  (eB : B ≌ B') (e' : A' ≌ B') {F : A ⥤ B'} (hF : eA.Functor ⋙ e'.Functor ≅ F) {G : B ⥤ A}
  (hG : eB.Functor ⋙ e'.inverse ≅ G ⋙ eA.Functor)

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₀ /-
/-- A basic equivalence `A ≅ B'` obtained by composing `eA : A ≅ A'` and `e' : A' ≅ B'`. -/
@[simps Functor inverse unit_iso_hom_app]
def equivalence₀ : A ≌ B' :=
  eA.trans e'
#align algebraic_topology.dold_kan.compatibility.equivalence₀ AlgebraicTopology.DoldKan.Compatibility.equivalence₀
-/

variable {eA} {e'}

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁ /-
/-- An intermediate equivalence `A ≅ B'` whose functor is `F` and whose inverse is
`e'.inverse ⋙ eA.inverse`. -/
@[simps Functor]
def equivalence₁ : A ≌ B' :=
  letI : is_equivalence F :=
    is_equivalence.of_iso hF (is_equivalence.of_equivalence (equivalence₀ eA e'))
  F.as_equivalence
#align algebraic_topology.dold_kan.compatibility.equivalence₁ AlgebraicTopology.DoldKan.Compatibility.equivalence₁
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁_inverse /-
theorem equivalence₁_inverse : (equivalence₁ hF).inverse = e'.inverse ⋙ eA.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence₁_inverse AlgebraicTopology.DoldKan.Compatibility.equivalence₁_inverse
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso /-
/-- The counit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁CounitIso : (e'.inverse ⋙ eA.inverse) ⋙ F ≅ 𝟭 B' :=
  calc
    (e'.inverse ⋙ eA.inverse) ⋙ F ≅ (e'.inverse ⋙ eA.inverse) ⋙ eA.Functor ⋙ e'.Functor :=
      isoWhiskerLeft _ hF.symm
    _ ≅ e'.inverse ⋙ (eA.inverse ⋙ eA.Functor) ⋙ e'.Functor := (Iso.refl _)
    _ ≅ e'.inverse ⋙ 𝟭 _ ⋙ e'.Functor := (isoWhiskerLeft _ (isoWhiskerRight eA.counitIso _))
    _ ≅ e'.inverse ⋙ e'.Functor := (Iso.refl _)
    _ ≅ 𝟭 B' := e'.counitIso
#align algebraic_topology.dold_kan.compatibility.equivalence₁_counit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso_eq /-
theorem equivalence₁CounitIso_eq : (equivalence₁ hF).counitIso = equivalence₁CounitIso hF :=
  by
  ext Y
  dsimp [equivalence₀, equivalence₁, is_equivalence.inverse, is_equivalence.of_equivalence]
  simp only [equivalence₁_counit_iso_hom_app, CategoryTheory.Functor.map_id, comp_id]
#align algebraic_topology.dold_kan.compatibility.equivalence₁_counit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₁CounitIso_eq
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso /-
/-- The unit isomorphism of the equivalence `equivalence₁` between `A` and `B'`. -/
@[simps]
def equivalence₁UnitIso : 𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ eA.Functor ⋙ eA.inverse := eA.unitIso
    _ ≅ eA.Functor ⋙ 𝟭 A' ⋙ eA.inverse := (Iso.refl _)
    _ ≅ eA.Functor ⋙ (e'.Functor ⋙ e'.inverse) ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight e'.unitIso _))
    _ ≅ (eA.Functor ⋙ e'.Functor) ⋙ e'.inverse ⋙ eA.inverse := (Iso.refl _)
    _ ≅ F ⋙ e'.inverse ⋙ eA.inverse := isoWhiskerRight hF _
#align algebraic_topology.dold_kan.compatibility.equivalence₁_unit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso_eq /-
theorem equivalence₁UnitIso_eq : (equivalence₁ hF).unitIso = equivalence₁UnitIso hF :=
  by
  ext X
  dsimp [equivalence₀, equivalence₁, nat_iso.hcomp, is_equivalence.of_equivalence]
  simp only [id_comp, assoc, equivalence₁_unit_iso_hom_app]
#align algebraic_topology.dold_kan.compatibility.equivalence₁_unit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₁UnitIso_eq
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂ /-
/-- An intermediate equivalence `A ≅ B` obtained as the composition of `equivalence₁` and
the inverse of `eB : B ≌ B'`. -/
@[simps Functor]
def equivalence₂ : A ≌ B :=
  (equivalence₁ hF).trans eB.symm
#align algebraic_topology.dold_kan.compatibility.equivalence₂ AlgebraicTopology.DoldKan.Compatibility.equivalence₂
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂_inverse /-
theorem equivalence₂_inverse :
    (equivalence₂ eB hF).inverse = eB.Functor ⋙ e'.inverse ⋙ eA.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence₂_inverse AlgebraicTopology.DoldKan.Compatibility.equivalence₂_inverse
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso /-
/-- The counit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂CounitIso : (eB.Functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    (eB.Functor ⋙ e'.inverse ⋙ eA.inverse) ⋙ F ⋙ eB.inverse ≅
        eB.Functor ⋙ (e'.inverse ⋙ eA.inverse ⋙ F) ⋙ eB.inverse :=
      Iso.refl _
    _ ≅ eB.Functor ⋙ 𝟭 _ ⋙ eB.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight (equivalence₁CounitIso hF) _))
    _ ≅ eB.Functor ⋙ eB.inverse := (Iso.refl _)
    _ ≅ 𝟭 B := eB.unitIso.symm
#align algebraic_topology.dold_kan.compatibility.equivalence₂_counit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso_eq /-
theorem equivalence₂CounitIso_eq : (equivalence₂ eB hF).counitIso = equivalence₂CounitIso eB hF :=
  by
  ext Y'
  dsimp [equivalence₂, iso.refl]
  simp only [equivalence₁_counit_iso_eq, equivalence₂_counit_iso_hom_app,
    equivalence₁_counit_iso_hom_app, functor.map_comp, assoc]
#align algebraic_topology.dold_kan.compatibility.equivalence₂_counit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₂CounitIso_eq
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso /-
/-- The unit isomorphism of the equivalence `equivalence₂` between `A` and `B`. -/
@[simps]
def equivalence₂UnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ eB.Functor ⋙ e'.inverse ⋙ eA.inverse :=
  calc
    𝟭 A ≅ F ⋙ e'.inverse ⋙ eA.inverse := equivalence₁UnitIso hF
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := (Iso.refl _)
    _ ≅ F ⋙ (eB.inverse ⋙ eB.Functor) ⋙ e'.inverse ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _))
    _ ≅ (F ⋙ eB.inverse) ⋙ eB.Functor ⋙ e'.inverse ⋙ eA.inverse := Iso.refl _
#align algebraic_topology.dold_kan.compatibility.equivalence₂_unit_iso AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso_eq /-
theorem equivalence₂UnitIso_eq : (equivalence₂ eB hF).unitIso = equivalence₂UnitIso eB hF :=
  by
  ext X
  dsimp [equivalence₂]
  simpa only [equivalence₂_unit_iso_hom_app, equivalence₁_unit_iso_eq,
    equivalence₁_unit_iso_hom_app, assoc, nat_iso.cancel_nat_iso_hom_left]
#align algebraic_topology.dold_kan.compatibility.equivalence₂_unit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalence₂UnitIso_eq
-/

variable {eB}

#print AlgebraicTopology.DoldKan.Compatibility.equivalence /-
/-- The equivalence `A ≅ B` whose functor is `F ⋙ eB.inverse` and
whose inverse is `G : B ≅ A`. -/
@[simps inverse]
def equivalence : A ≌ B :=
  letI : is_equivalence G :=
    by
    refine' is_equivalence.of_iso _ (is_equivalence.of_equivalence (equivalence₂ eB hF).symm)
    calc
      eB.functor ⋙ e'.inverse ⋙ eA.inverse ≅ (eB.functor ⋙ e'.inverse) ⋙ eA.inverse := iso.refl _
      _ ≅ (G ⋙ eA.functor) ⋙ eA.inverse := (iso_whisker_right hG _)
      _ ≅ G ⋙ 𝟭 A := (iso_whisker_left _ eA.unit_iso.symm)
      _ ≅ G := functor.right_unitor G
  G.as_equivalence.symm
#align algebraic_topology.dold_kan.compatibility.equivalence AlgebraicTopology.DoldKan.Compatibility.equivalence
-/

#print AlgebraicTopology.DoldKan.Compatibility.equivalence_functor /-
theorem equivalence_functor : (equivalence hF hG).Functor = F ⋙ eB.inverse :=
  rfl
#align algebraic_topology.dold_kan.compatibility.equivalence_functor AlgebraicTopology.DoldKan.Compatibility.equivalence_functor
-/

#print AlgebraicTopology.DoldKan.Compatibility.τ₀ /-
/-- The isomorphism `eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor` deduced
from the counit isomorphism of `e'`. -/
@[simps hom_app]
def τ₀ : eB.Functor ⋙ e'.inverse ⋙ e'.Functor ≅ eB.Functor :=
  calc
    eB.Functor ⋙ e'.inverse ⋙ e'.Functor ≅ eB.Functor ⋙ 𝟭 _ := isoWhiskerLeft _ e'.counitIso
    _ ≅ eB.Functor := Functor.rightUnitor _
#align algebraic_topology.dold_kan.compatibility.τ₀ AlgebraicTopology.DoldKan.Compatibility.τ₀
-/

#print AlgebraicTopology.DoldKan.Compatibility.τ₁ /-
/-- The isomorphism `eB.functor ⋙ e'.inverse ⋙ e'.functor ≅ eB.functor` deduced
from the isomorphisms `hF : eA.functor ⋙ e'.functor ≅ F`,
`hG : eB.functor ⋙ e'.inverse ≅ G ⋙ eA.functor` and the datum of
an isomorphism `η : G ⋙ F ≅ eB.functor`. -/
@[simps hom_app]
def τ₁ (η : G ⋙ F ≅ eB.Functor) : eB.Functor ⋙ e'.inverse ⋙ e'.Functor ≅ eB.Functor :=
  calc
    eB.Functor ⋙ e'.inverse ⋙ e'.Functor ≅ (eB.Functor ⋙ e'.inverse) ⋙ e'.Functor := Iso.refl _
    _ ≅ (G ⋙ eA.Functor) ⋙ e'.Functor := (isoWhiskerRight hG _)
    _ ≅ G ⋙ eA.Functor ⋙ e'.Functor := by rfl
    _ ≅ G ⋙ F := (isoWhiskerLeft _ hF)
    _ ≅ eB.Functor := η
#align algebraic_topology.dold_kan.compatibility.τ₁ AlgebraicTopology.DoldKan.Compatibility.τ₁
-/

variable (η : G ⋙ F ≅ eB.Functor) (hη : τ₀ = τ₁ hF hG η)

#print AlgebraicTopology.DoldKan.Compatibility.equivalenceCounitIso /-
/-- The counit isomorphism of `equivalence`. -/
@[simps]
def equivalenceCounitIso : G ⋙ F ⋙ eB.inverse ≅ 𝟭 B :=
  calc
    G ⋙ F ⋙ eB.inverse ≅ (G ⋙ F) ⋙ eB.inverse := Iso.refl _
    _ ≅ eB.Functor ⋙ eB.inverse := (isoWhiskerRight η _)
    _ ≅ 𝟭 B := eB.unitIso.symm
#align algebraic_topology.dold_kan.compatibility.equivalence_counit_iso AlgebraicTopology.DoldKan.Compatibility.equivalenceCounitIso
-/

variable {η hF hG}

#print AlgebraicTopology.DoldKan.Compatibility.equivalenceCounitIso_eq /-
theorem equivalenceCounitIso_eq : (equivalence hF hG).counitIso = equivalenceCounitIso η :=
  by
  ext1; apply nat_trans.ext; ext Y
  dsimp [Equivalence, equivalence_counit_iso, is_equivalence.of_equivalence]
  simp only [equivalence₂_counit_iso_eq eB hF]
  erw [nat_trans.id_app, nat_trans.id_app]
  dsimp [equivalence₂, equivalence₁]
  simp only [assoc, comp_id, F.map_id, id_comp, equivalence₂_counit_iso_hom_app, ←
    eB.inverse.map_comp_assoc, ← τ₀_hom_app, hη, τ₁_hom_app]
  erw [hF.inv.naturality_assoc]
  congr 2
  dsimp
  simp only [assoc, ← e'.functor.map_comp_assoc, eA.functor.map_comp, equivalence.fun_inv_map,
    iso.inv_hom_id_app_assoc, hG.inv_hom_id_app]
  dsimp
  rw [comp_id, eA.functor_unit_iso_comp, e'.functor.map_id, id_comp, hF.inv_hom_id_app_assoc]
#align algebraic_topology.dold_kan.compatibility.equivalence_counit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalenceCounitIso_eq
-/

variable (hF)

#print AlgebraicTopology.DoldKan.Compatibility.υ /-
/-- The isomorphism `eA.functor ≅ F ⋙ e'.inverse` deduced from the
unit isomorphism of `e'` and the isomorphism `hF : eA.functor ⋙ e'.functor ≅ F`. -/
@[simps]
def υ : eA.Functor ≅ F ⋙ e'.inverse :=
  calc
    eA.Functor ≅ eA.Functor ⋙ 𝟭 A' := (Functor.leftUnitor _).symm
    _ ≅ eA.Functor ⋙ e'.Functor ⋙ e'.inverse := (isoWhiskerLeft _ e'.unitIso)
    _ ≅ (eA.Functor ⋙ e'.Functor) ⋙ e'.inverse := (Iso.refl _)
    _ ≅ F ⋙ e'.inverse := isoWhiskerRight hF _
#align algebraic_topology.dold_kan.compatibility.υ AlgebraicTopology.DoldKan.Compatibility.υ
-/

variable (ε : eA.Functor ≅ F ⋙ e'.inverse) (hε : υ hF = ε)

variable (hG)

#print AlgebraicTopology.DoldKan.Compatibility.equivalenceUnitIso /-
/-- The unit isomorphism of `equivalence`. -/
@[simps]
def equivalenceUnitIso : 𝟭 A ≅ (F ⋙ eB.inverse) ⋙ G :=
  calc
    𝟭 A ≅ eA.Functor ⋙ eA.inverse := eA.unitIso
    _ ≅ (F ⋙ e'.inverse) ⋙ eA.inverse := (isoWhiskerRight ε _)
    _ ≅ F ⋙ 𝟭 B' ⋙ e'.inverse ⋙ eA.inverse := (Iso.refl _)
    _ ≅ F ⋙ (eB.inverse ⋙ eB.Functor) ⋙ e'.inverse ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight eB.counitIso.symm _))
    _ ≅ (F ⋙ eB.inverse) ⋙ (eB.Functor ⋙ e'.inverse) ⋙ eA.inverse := (Iso.refl _)
    _ ≅ (F ⋙ eB.inverse) ⋙ (G ⋙ eA.Functor) ⋙ eA.inverse :=
      (isoWhiskerLeft _ (isoWhiskerRight hG _))
    _ ≅ (F ⋙ eB.inverse ⋙ G) ⋙ eA.Functor ⋙ eA.inverse := (Iso.refl _)
    _ ≅ (F ⋙ eB.inverse ⋙ G) ⋙ 𝟭 A := (isoWhiskerLeft _ eA.unitIso.symm)
    _ ≅ (F ⋙ eB.inverse) ⋙ G := Iso.refl _
#align algebraic_topology.dold_kan.compatibility.equivalence_unit_iso AlgebraicTopology.DoldKan.Compatibility.equivalenceUnitIso
-/

variable {ε hF hG}

#print AlgebraicTopology.DoldKan.Compatibility.equivalenceUnitIso_eq /-
theorem equivalenceUnitIso_eq : (equivalence hF hG).unitIso = equivalenceUnitIso hG ε :=
  by
  ext1; apply nat_trans.ext; ext X
  dsimp [Equivalence, iso.refl, nat_iso.hcomp, is_equivalence.inverse,
    is_equivalence.of_equivalence]
  erw [nat_trans.id_app, id_comp, G.map_id, comp_id, comp_id]
  simp only [equivalence₂_unit_iso_eq eB hF, equivalence₂_unit_iso_hom_app]
  dsimp [equivalence₂, equivalence₁]
  simp only [assoc, equivalence_unit_iso_hom_app, nat_iso.cancel_nat_iso_hom_left, ←
    eA.inverse.map_comp_assoc, ← hε, υ_hom_app]
#align algebraic_topology.dold_kan.compatibility.equivalence_unit_iso_eq AlgebraicTopology.DoldKan.Compatibility.equivalenceUnitIso_eq
-/

end Compatibility

end DoldKan

end AlgebraicTopology

