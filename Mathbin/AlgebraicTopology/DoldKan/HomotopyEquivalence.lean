/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
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

/- warning: algebraic_topology.dold_kan.homotopy_P_to_id -> AlgebraicTopology.DoldKan.homotopyPToId is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u_1}} [_inst_1 : CategoryTheory.Category.{u_2 u_1} C] [_inst_2 : CategoryTheory.Preadditive.{u_2 u_1} C _inst_1] (X : CategoryTheory.SimplicialObject.{u_2 u_1} C _inst_1) (q : Nat), Homotopy.{u_2 u_1 0} Nat C _inst_1 _inst_2 (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toCancelAddMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u_1 u_2} C _inst_1 _inst_2 X) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u_1 u_2} C _inst_1 _inst_2 X) (AlgebraicTopology.DoldKan.p.{u_1 u_2} C _inst_1 _inst_2 X q) (CategoryTheory.CategoryStruct.id.{u_2 (max u_1 u_2)} (HomologicalComplex.{u_2 u_1 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u_2 u_1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toCancelAddMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne)) (CategoryTheory.Category.toCategoryStruct.{u_2 (max u_1 u_2)} (HomologicalComplex.{u_2 u_1 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u_2 u_1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toCancelAddMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne)) (HomologicalComplex.CategoryTheory.category.{u_2 u_1 0} Nat C _inst_1 (CategoryTheory.Preadditive.preadditiveHasZeroMorphisms.{u_2 u_1} C _inst_1 _inst_2) (ComplexShape.down.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toCancelAddMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) Nat.hasOne))) (AlgebraicTopology.AlternatingFaceMapComplex.obj.{u_1 u_2} C _inst_1 _inst_2 X))
but is expected to have type
  PUnit.{(max (succ (succ u_1)) (succ (succ u_2)))}
Case conversion may be inaccurate. Consider using '#align algebraic_topology.dold_kan.homotopy_P_to_id AlgebraicTopology.DoldKan.homotopyPToIdₓ'. -/
/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (p q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 => by
    refine'
      Homotopy.trans (Homotopy.ofEq _)
        (Homotopy.trans (Homotopy.add (homotopy_P_to_id q) (Homotopy.compLeft (homotopy_Hσ_to_zero q) (P q)))
          (Homotopy.ofEq _))
    · unfold P
      simp only [comp_add, comp_id]
      
    · simp only [add_zero, comp_zero]
      

/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
def homotopyQToZero (q : ℕ) : Homotopy (q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

theorem homotopy_P_to_id_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).Hom n (n + 1) : X _[n] ⟶ X _[n + 1]) = (homotopyPToId X q).Hom n (n + 1) := by
  unfold homotopy_P_to_id
  simp only [homotopy_Hσ_to_zero, hσ'_eq_zero hqn (c_mk (n + 1) n rfl), Homotopy.trans_hom, Pi.add_apply,
    Homotopy.of_eq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.comp_left_hom, Homotopy.null_homotopy'_hom,
    ComplexShape.down_rel, eq_self_iff_true, dite_eq_ite, if_true, comp_zero, add_zero, zero_add]

variable (X)

/-- Construction of the homotopy from `P_infty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
def homotopyPInftyToId : Homotopy (pInfty : K[X] ⟶ _) (𝟙 _) where
  Hom i j := (homotopyPToId X (j + 1)).Hom i j
  zero' i j hij := Homotopy.zero _ i j hij
  comm n := by
    cases n
    · simpa only [Homotopy.d_next_zero_chain_complex, Homotopy.prev_d_chain_complex, P_f_0_eq, zero_add,
        HomologicalComplex.id_f, P_infty_f] using (homotopy_P_to_id X 2).comm 0
      
    · simpa only [Homotopy.d_next_succ_chain_complex, Homotopy.prev_d_chain_complex, HomologicalComplex.id_f, P_infty_f,
        ← P_is_eventually_constant (rfl.le : n + 1 ≤ n + 1),
        homotopy_P_to_id_eventually_constant X (lt_add_one (n + 1))] using (homotopy_P_to_id X (n + 2)).comm (n + 1)
      

/-- The inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex {A : Type _} [Category A] [Abelian A]
    {Y : SimplicialObject A} :
    HomotopyEquiv ((normalizedMooreComplex A).obj Y) ((alternatingFaceMapComplex A).obj Y) where
  Hom := inclusionOfMooreComplexMap Y
  inv := pInftyToNormalizedMooreComplex Y
  homotopyHomInvId := Homotopy.ofEq (splitMonoInclusionOfMooreComplexMap Y).id
  homotopyInvHomId :=
    Homotopy.trans (Homotopy.ofEq (P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map Y))
      (homotopyPInftyToId Y)

end DoldKan

end AlgebraicTopology

