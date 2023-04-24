/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module algebraic_topology.dold_kan.homotopy_equivalence
! leanprover-community/mathlib commit f951e201d416fb50cc7826171d80aa510ec20747
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.DoldKan.Normalized

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/


open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive

open Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type _} [Category C] [Preadditive C] (X : SimplicialObject C)

#print AlgebraicTopology.DoldKan.homotopyPToId /-
/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 =>
    by
    refine'
      Homotopy.trans (Homotopy.ofEq _)
        (Homotopy.trans
          (Homotopy.add (homotopy_P_to_id q) (Homotopy.compLeft (homotopy_Hσ_to_zero q) (P q)))
          (Homotopy.ofEq _))
    · unfold P
      simp only [comp_add, comp_id]
    · simp only [add_zero, comp_zero]
#align algebraic_topology.dold_kan.homotopy_P_to_id AlgebraicTopology.DoldKan.homotopyPToId
-/

#print AlgebraicTopology.DoldKan.homotopyQToZero /-
/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
def homotopyQToZero (q : ℕ) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm
#align algebraic_topology.dold_kan.homotopy_Q_to_zero AlgebraicTopology.DoldKan.homotopyQToZero
-/

#print AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant /-
theorem homotopyPToId_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).Hom n (n + 1) : X _[n] ⟶ X _[n + 1]) =
      (homotopyPToId X q).Hom n (n + 1) :=
  by
  unfold homotopy_P_to_id
  simp only [homotopy_Hσ_to_zero, hσ'_eq_zero hqn (c_mk (n + 1) n rfl), Homotopy.trans_hom,
    Pi.add_apply, Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, eq_self_iff_true, dite_eq_ite, if_true,
    comp_zero, add_zero, zero_add]
#align algebraic_topology.dold_kan.homotopy_P_to_id_eventually_constant AlgebraicTopology.DoldKan.homotopyPToId_eventually_constant
-/

variable (X)

#print AlgebraicTopology.DoldKan.homotopyPInftyToId /-
/-- Construction of the homotopy from `P_infty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
def homotopyPInftyToId : Homotopy (PInfty : K[X] ⟶ _) (𝟙 _)
    where
  Hom i j := (homotopyPToId X (j + 1)).Hom i j
  zero' i j hij := Homotopy.zero _ i j hij
  comm n := by
    cases n
    ·
      simpa only [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, P_f_0_eq, zero_add,
        HomologicalComplex.id_f, P_infty_f] using (homotopy_P_to_id X 2).comm 0
    ·
      simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        HomologicalComplex.id_f, P_infty_f, ← P_is_eventually_constant (rfl.le : n + 1 ≤ n + 1),
        homotopy_P_to_id_eventually_constant X (lt_add_one (n + 1))] using
        (homotopy_P_to_id X (n + 2)).comm (n + 1)
#align algebraic_topology.dold_kan.homotopy_P_infty_to_id AlgebraicTopology.DoldKan.homotopyPInftyToId
-/

/- warning: algebraic_topology.dold_kan.homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex -> AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_3 : CategoryTheory.Category.{u2, u1} A] [_inst_4 : CategoryTheory.Abelian.{u2, u1} A _inst_3] {Y : CategoryTheory.SimplicialObject.{u2, u1} A _inst_3}, HomotopyEquiv.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (CategoryTheory.Functor.obj.{u2, u2, max u2 u1, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.SimplicialObject.category.{u2, u1} A _inst_3) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (HomologicalComplex.CategoryTheory.category.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne)) (AlgebraicTopology.normalizedMooreComplex.{u1, u2} A _inst_3 _inst_4) Y) (CategoryTheory.Functor.obj.{u2, u2, max u2 u1, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.SimplicialObject.category.{u2, u1} A _inst_3) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (HomologicalComplex.CategoryTheory.category.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne)) (AlgebraicTopology.alternatingFaceMapComplex.{u1, u2} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Y)
but is expected to have type
  forall {A : Type.{u1}} [_inst_3 : CategoryTheory.Category.{u2, u1} A] [_inst_4 : CategoryTheory.Abelian.{u2, u1} A _inst_3] {Y : CategoryTheory.SimplicialObject.{u2, u1} A _inst_3}, HomotopyEquiv.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (Prefunctor.obj.{succ u2, succ u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.instCategorySimplicialObject.{u2, u1} A _inst_3))) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))))) (CategoryTheory.Functor.toPrefunctor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.instCategorySimplicialObject.{u2, u1} A _inst_3) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))) (AlgebraicTopology.normalizedMooreComplex.{u1, u2} A _inst_3 _inst_4)) Y) (Prefunctor.obj.{succ u2, succ u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.instCategorySimplicialObject.{u2, u1} A _inst_3))) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.CategoryStruct.toQuiver.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (CategoryTheory.Category.toCategoryStruct.{u2, max u1 u2} (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))))) (CategoryTheory.Functor.toPrefunctor.{u2, u2, max u1 u2, max u1 u2} (CategoryTheory.SimplicialObject.{u2, u1} A _inst_3) (CategoryTheory.instCategorySimplicialObject.{u2, u1} A _inst_3) (ChainComplex.{u2, u1, 0} A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring)) (HomologicalComplex.instCategoryHomologicalComplex.{u2, u1, 0} Nat A _inst_3 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u2, u1} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4)) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (CanonicallyOrderedCommSemiring.toOne.{0} Nat Nat.canonicallyOrderedCommSemiring))) (AlgebraicTopology.alternatingFaceMapComplex.{u1, u2} A _inst_3 (CategoryTheory.Abelian.toPreadditive.{u2, u1} A _inst_3 _inst_4))) Y)
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplexₓ'. -/
/-- The inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type _} [Category A]
    [Abelian A] {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y)
    where
  Hom := inclusionOfMooreComplexMap Y
  inv := PInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId :=
    Homotopy.trans
      (Homotopy.ofEq (PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap Y))
      (homotopyPInftyToId Y)
#align algebraic_topology.dold_kan.homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex

end DoldKan

end AlgebraicTopology

