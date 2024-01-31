/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import Topology.Category.Top.Limits.Basic

#align_import topology.category.Top.limits.cofiltered from "leanprover-community/mathlib"@"dbdf71cee7bb20367cb7e37279c08b0c218cf967"

/-!
# Cofiltered limits in Top.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/


open TopologicalSpace

open CategoryTheory

open CategoryTheory.Limits

universe u v w

noncomputable section

namespace TopCat

section CofilteredLimit

variable {J : Type v} [SmallCategory J] [IsCofiltered J] (F : J ⥤ TopCat.{max v u}) (C : Cone F)
  (hC : IsLimit C)

#print TopCat.isTopologicalBasis_cofiltered_limit /-
/-- Given a *compatible* collection of topological bases for the factors in a cofiltered limit
which contain `set.univ` and are closed under intersections, the induced *naive* collection
of sets in the limit is, in fact, a topological basis.
-/
theorem isTopologicalBasis_cofiltered_limit (T : ∀ j, Set (Set (F.obj j)))
    (hT : ∀ j, IsTopologicalBasis (T j)) (univ : ∀ i : J, Set.univ ∈ T i)
    (inter : ∀ (i) (U1 U2 : Set (F.obj i)), U1 ∈ T i → U2 ∈ T i → U1 ∩ U2 ∈ T i)
    (compat : ∀ (i j : J) (f : i ⟶ j) (V : Set (F.obj j)) (hV : V ∈ T j), F.map f ⁻¹' V ∈ T i) :
    IsTopologicalBasis
      {U : Set C.pt | ∃ (j : _) (V : Set (F.obj j)), V ∈ T j ∧ U = C.π.app j ⁻¹' V} :=
  by classical
#align Top.is_topological_basis_cofiltered_limit TopCat.isTopologicalBasis_cofiltered_limit
-/

-- The limit cone for `F` whose topology is defined as an infimum.
-- The isomorphism between the cone point of `C` and the cone point of `D`.
-- Reduce to the assertion of the theorem with `D` instead of `C`.
-- Using `D`, we can apply the characterization of the topological basis of a
-- topology defined as an infimum...
-- An intermediate claim used to apply induction along `G : finset J` later on.
-- use the intermediate claim to finish off the goal using `univ` and `inter`.
-- conclude...
end CofilteredLimit

end TopCat

