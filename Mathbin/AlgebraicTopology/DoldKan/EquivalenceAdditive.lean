/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import AlgebraicTopology.DoldKan.NCompGamma

#align_import algebraic_topology.dold_kan.equivalence_additive from "leanprover-community/mathlib"@"32a7e535287f9c73f2e4d2aef306a39190f0b504"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 The Dold-Kan equivalence for additive categories.

This file defines `preadditive.dold_kan.equivalence` which is the equivalence
of categories `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`.

(See `equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/


noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents
  AlgebraicTopology.DoldKan

variable {C : Type _} [Category C] [Preadditive C]

namespace CategoryTheory

namespace Preadditive

namespace DoldKan

#print CategoryTheory.Preadditive.DoldKan.N /-
/-- The functor `karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def N : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  N₂
#align category_theory.preadditive.dold_kan.N CategoryTheory.Preadditive.DoldKan.N
-/

variable [HasFiniteCoproducts C]

#print CategoryTheory.Preadditive.DoldKan.Γ /-
/-- The inverse functor `karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` of
the Dold-Kan equivalence for additive categories. -/
@[simps]
def Γ : Karoubi (ChainComplex C ℕ) ⥤ Karoubi (SimplicialObject C) :=
  Γ₂
#align category_theory.preadditive.dold_kan.Γ CategoryTheory.Preadditive.DoldKan.Γ
-/

#print CategoryTheory.Preadditive.DoldKan.equivalence /-
/-- The Dold-Kan equivalence `karoubi (simplicial_object C) ≌ karoubi (chain_complex C ℕ)`
for additive categories. -/
@[simps]
def equivalence : Karoubi (SimplicialObject C) ≌ Karoubi (ChainComplex C ℕ)
    where
  Functor := N
  inverse := Γ
  unitIso := Γ₂N₂
  counitIso := N₂Γ₂
  functor_unitIso_comp' P := by
    let α := N.map_iso (Γ₂N₂.app P)
    let β := N₂Γ₂.app (N.obj P)
    symm
    change 𝟙 _ = α.hom ≫ β.hom
    rw [← iso.inv_comp_eq, comp_id, ← comp_id β.hom, ← iso.inv_comp_eq]
    exact AlgebraicTopology.DoldKan.identity_N₂_objectwise P
#align category_theory.preadditive.dold_kan.equivalence CategoryTheory.Preadditive.DoldKan.equivalence
-/

end DoldKan

end Preadditive

end CategoryTheory

