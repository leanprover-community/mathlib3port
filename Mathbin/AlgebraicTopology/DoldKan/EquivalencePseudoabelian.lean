/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.AlgebraicTopology.DoldKan.EquivalenceAdditive
import Mathbin.AlgebraicTopology.DoldKan.Compatibility
import Mathbin.CategoryTheory.Idempotents.SimplicialObject

#align_import algebraic_topology.dold_kan.equivalence_pseudoabelian from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!

# The Dold-Kan correspondence for pseudoabelian categories

In this file, for any idempotent complete additive category `C`,
the Dold-Kan equivalence
`idempotents.dold_kan.equivalence C : simplicial_object C ≌ chain_complex C ℕ`
is obtained. It is deduced from the equivalence
`preadditive.dold_kan.equivalence` between the respective idempotent
completions of these categories using the fact that when `C` is idempotent complete,
then both `simplicial_object C` and `chain_complex C ℕ` are idempotent complete.

The construction of `idempotents.dold_kan.equivalence` uses the tools
introduced in the file `compatibility.lean`. Doing so, the functor
`idempotents.dold_kan.N` of the equivalence is
the composition of `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
(defined in `functor_n.lean`) and the inverse of the equivalence
`chain_complex C ℕ ≌ karoubi (chain_complex C ℕ)`. The functor
`idempotents.dold_kan.Γ` of the equivalence is by definition the functor
`Γ₀` introduced in `functor_gamma.lean`.

(See `equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents

variable {C : Type _} [Category C] [Preadditive C] [IsIdempotentComplete C] [HasFiniteCoproducts C]

namespace CategoryTheory

namespace Idempotents

namespace DoldKan

open AlgebraicTopology.DoldKan

#print CategoryTheory.Idempotents.DoldKan.N /-
/-- The functor `N` for the equivalence is obtained by composing
`N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)` and the inverse
of the equivalence `chain_complex C ℕ ≌ karoubi (chain_complex C ℕ)`. -/
@[simps, nolint unused_arguments]
def N : SimplicialObject C ⥤ ChainComplex C ℕ :=
  N₁ ⋙ (toKaroubi_equivalence _).inverse
#align category_theory.idempotents.dold_kan.N CategoryTheory.Idempotents.DoldKan.N
-/

#print CategoryTheory.Idempotents.DoldKan.Γ /-
/-- The functor `Γ` for the equivalence is `Γ'`. -/
@[simps, nolint unused_arguments]
def Γ : ChainComplex C ℕ ⥤ SimplicialObject C :=
  Γ₀
#align category_theory.idempotents.dold_kan.Γ CategoryTheory.Idempotents.DoldKan.Γ
-/

#print CategoryTheory.Idempotents.DoldKan.hN₁ /-
theorem hN₁ :
    (toKaroubi_equivalence (SimplicialObject C)).Functor ⋙ Preadditive.DoldKan.equivalence.Functor =
      N₁ :=
  Functor.congr_obj (functorExtension₁_comp_whiskeringLeft_toKaroubi _ _) N₁
#align category_theory.idempotents.dold_kan.hN₁ CategoryTheory.Idempotents.DoldKan.hN₁
-/

#print CategoryTheory.Idempotents.DoldKan.hΓ₀ /-
theorem hΓ₀ :
    (toKaroubi_equivalence (ChainComplex C ℕ)).Functor ⋙ Preadditive.DoldKan.equivalence.inverse =
      Γ ⋙ (toKaroubi_equivalence _).Functor :=
  Functor.congr_obj (functorExtension₂_comp_whiskeringLeft_toKaroubi _ _) Γ₀
#align category_theory.idempotents.dold_kan.hΓ₀ CategoryTheory.Idempotents.DoldKan.hΓ₀
-/

#print CategoryTheory.Idempotents.DoldKan.equivalence /-
/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`compatibility.lean` to the equivalence `preadditive.dold_kan.equivalence`. -/
def equivalence : SimplicialObject C ≌ ChainComplex C ℕ :=
  Compatibility.equivalence (eqToIso hN₁) (eqToIso hΓ₀)
#align category_theory.idempotents.dold_kan.equivalence CategoryTheory.Idempotents.DoldKan.equivalence
-/

#print CategoryTheory.Idempotents.DoldKan.equivalence_functor /-
theorem equivalence_functor : (equivalence : SimplicialObject C ≌ _).Functor = N :=
  rfl
#align category_theory.idempotents.dold_kan.equivalence_functor CategoryTheory.Idempotents.DoldKan.equivalence_functor
-/

#print CategoryTheory.Idempotents.DoldKan.equivalence_inverse /-
theorem equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ :=
  rfl
#align category_theory.idempotents.dold_kan.equivalence_inverse CategoryTheory.Idempotents.DoldKan.equivalence_inverse
-/

#print CategoryTheory.Idempotents.DoldKan.hη /-
/-- The natural isomorphism `NΓ' satisfies the compatibility that is needed
for the construction of our counit isomorphism `η` -/
theorem hη :
    Compatibility.τ₀ =
      Compatibility.τ₁ (eqToIso hN₁) (eqToIso hΓ₀)
        (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubi_equivalence (ChainComplex C ℕ)).Functor) :=
  by
  ext K : 3
  simpa only [compatibility.τ₀_hom_app, compatibility.τ₁_hom_app, eq_to_iso.hom,
    preadditive.dold_kan.equivalence_counit_iso, N₂Γ₂_to_karoubi_iso_hom, eq_to_hom_map,
    eq_to_hom_trans_assoc, eq_to_hom_app] using N₂Γ₂_compatible_with_N₁Γ₀ K
#align category_theory.idempotents.dold_kan.hη CategoryTheory.Idempotents.DoldKan.hη
-/

#print CategoryTheory.Idempotents.DoldKan.η /-
/-- The counit isomorphism induced by `N₁Γ₀` -/
@[simps]
def η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ) :=
  Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C ℕ ⥤ _) ⋙ N₁ ≅ (toKaroubi_equivalence _).Functor)
#align category_theory.idempotents.dold_kan.η CategoryTheory.Idempotents.DoldKan.η
-/

#print CategoryTheory.Idempotents.DoldKan.equivalence_counitIso /-
theorem equivalence_counitIso :
    DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (ChainComplex C ℕ)) :=
  Compatibility.equivalenceCounitIso_eq hη
#align category_theory.idempotents.dold_kan.equivalence_counit_iso CategoryTheory.Idempotents.DoldKan.equivalence_counitIso
-/

#print CategoryTheory.Idempotents.DoldKan.hε /-
theorem hε :
    Compatibility.υ (eqToIso hN₁) =
      (Γ₂N₁ :
        (toKaroubi_equivalence _).Functor ≅
          (N₁ : SimplicialObject C ⥤ _) ⋙ Preadditive.DoldKan.equivalence.inverse) :=
  by
  ext X : 4
  erw [nat_trans.comp_app, compatibility_Γ₂N₁_Γ₂N₂_nat_trans]
  simp only [compatibility.υ_hom_app, compatibility_Γ₂N₁_Γ₂N₂,
    preadditive.dold_kan.equivalence_unit_iso, Γ₂N₂, iso.symm_hom, as_iso_inv, assoc]
  erw [← nat_trans.comp_app_assoc, is_iso.hom_inv_id]
  dsimp
  simpa only [id_comp, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans]
#align category_theory.idempotents.dold_kan.hε CategoryTheory.Idempotents.DoldKan.hε
-/

#print CategoryTheory.Idempotents.DoldKan.ε /-
/-- The unit isomorphism induced by `Γ₂N₁`. -/
def ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ :=
  Compatibility.equivalenceUnitIso (eqToIso hΓ₀) Γ₂N₁
#align category_theory.idempotents.dold_kan.ε CategoryTheory.Idempotents.DoldKan.ε
-/

#print CategoryTheory.Idempotents.DoldKan.equivalence_unitIso /-
theorem equivalence_unitIso : DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ) :=
  Compatibility.equivalenceUnitIso_eq hε
#align category_theory.idempotents.dold_kan.equivalence_unit_iso CategoryTheory.Idempotents.DoldKan.equivalence_unitIso
-/

end DoldKan

end Idempotents

end CategoryTheory

