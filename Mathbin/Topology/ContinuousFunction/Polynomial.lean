/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module topology.continuous_function.polynomial
! leanprover-community/mathlib commit bd15ff41b70f5e2cc210f26f25a8d5c53b20d3de
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Polynomial
import Mathbin.Topology.ContinuousFunction.Algebra
import Mathbin.Topology.UnitInterval

/-!
# Constructions relating polynomial functions and continuous functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `polynomial.to_continuous_map_on p X`: for `X : set R`, interprets a polynomial `p`
  as a bundled continuous function in `C(X, R)`.
* `polynomial.to_continuous_map_on_alg_hom`: the same, as an `R`-algebra homomorphism.
* `polynomial_functions (X : set R) : subalgebra R C(X, R)`: polynomial functions as a subalgebra.
* `polynomial_functions_separates_points (X : set R) : (polynomial_functions X).separates_points`:
  the polynomial functions separate points.

-/


variable {R : Type _}

open Polynomial

namespace Polynomial

section

variable [Semiring R] [TopologicalSpace R] [TopologicalSemiring R]

#print Polynomial.toContinuousMap /-
/--
Every polynomial with coefficients in a topological semiring gives a (bundled) continuous function.
-/
@[simps]
def toContinuousMap (p : R[X]) : C(R, R) :=
  ⟨fun x : R => p.eval x, by continuity⟩
#align polynomial.to_continuous_map Polynomial.toContinuousMap
-/

#print Polynomial.toContinuousMapOn /-
/-- A polynomial as a continuous function,
with domain restricted to some subset of the semiring of coefficients.

(This is particularly useful when restricting to compact sets, e.g. `[0,1]`.)
-/
@[simps]
def toContinuousMapOn (p : R[X]) (X : Set R) : C(X, R) :=
  ⟨fun x : X => p.toContinuousMap x, by continuity⟩
#align polynomial.to_continuous_map_on Polynomial.toContinuousMapOn
-/

-- TODO some lemmas about when `to_continuous_map_on` is injective?
end

section

variable {α : Type _} [TopologicalSpace α] [CommSemiring R] [TopologicalSpace R]
  [TopologicalSemiring R]

/- warning: polynomial.aeval_continuous_map_apply -> Polynomial.aeval_continuousMap_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial.aeval_continuous_map_apply Polynomial.aeval_continuousMap_applyₓ'. -/
@[simp]
theorem aeval_continuousMap_apply (g : R[X]) (f : C(α, R)) (x : α) :
    ((Polynomial.aeval f) g) x = g.eval (f x) :=
  by
  apply Polynomial.induction_on' g
  · intro p q hp hq
    simp [hp, hq]
  · intro n a
    simp [Pi.pow_apply]
#align polynomial.aeval_continuous_map_apply Polynomial.aeval_continuousMap_apply

end

section

noncomputable section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/- warning: polynomial.to_continuous_map_alg_hom -> Polynomial.toContinuousMapAlgHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))], AlgHom.{u1, u1, u1} R (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.{u1, u1} R R _inst_2 _inst_2) _inst_1 (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.semiring.{u1, u1} R R _inst_2 _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (ContinuousMap.algebra.{u1, u1, u1} R _inst_2 R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))], AlgHom.{u1, u1, u1} R (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.{u1, u1} R R _inst_2 _inst_2) _inst_1 (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.instSemiringContinuousMap.{u1, u1} R R _inst_2 _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (ContinuousMap.algebra.{u1, u1, u1} R _inst_2 R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
Case conversion may be inaccurate. Consider using '#align polynomial.to_continuous_map_alg_hom Polynomial.toContinuousMapAlgHomₓ'. -/
/-- The algebra map from `R[X]` to continuous functions `C(R, R)`.
-/
@[simps]
def toContinuousMapAlgHom : R[X] →ₐ[R] C(R, R)
    where
  toFun p := p.toContinuousMap
  map_zero' := by
    ext
    simp
  map_add' := by
    intros
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := by
    intros
    ext
    simp
  commutes' := by
    intros
    ext
    simp [Algebra.algebraMap_eq_smul_one]
#align polynomial.to_continuous_map_alg_hom Polynomial.toContinuousMapAlgHom

/- warning: polynomial.to_continuous_map_on_alg_hom -> Polynomial.toContinuousMapOnAlgHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))] (X : Set.{u1} R), AlgHom.{u1, u1, u1} R (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) R (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) _inst_2) _inst_1 (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.semiring.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) R (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (ContinuousMap.algebra.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))] (X : Set.{u1} R), AlgHom.{u1, u1, u1} R (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.{u1, u1} (Set.Elem.{u1} R X) R (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) _inst_2) _inst_1 (Polynomial.semiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)) (ContinuousMap.instSemiringContinuousMap.{u1, u1} (Set.Elem.{u1} R X) R (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (Polynomial.algebraOfAlgebra.{u1, u1} R R _inst_1 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1)) (ContinuousMap.algebra.{u1, u1, u1} (Set.Elem.{u1} R X) (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
Case conversion may be inaccurate. Consider using '#align polynomial.to_continuous_map_on_alg_hom Polynomial.toContinuousMapOnAlgHomₓ'. -/
/-- The algebra map from `R[X]` to continuous functions `C(X, R)`, for any subset `X` of `R`.
-/
@[simps]
def toContinuousMapOnAlgHom (X : Set R) : R[X] →ₐ[R] C(X, R)
    where
  toFun p := p.toContinuousMapOn X
  map_zero' := by
    ext
    simp
  map_add' := by
    intros
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' := by
    intros
    ext
    simp
  commutes' := by
    intros
    ext
    simp [Algebra.algebraMap_eq_smul_one]
#align polynomial.to_continuous_map_on_alg_hom Polynomial.toContinuousMapOnAlgHom

end

end Polynomial

section

variable [CommSemiring R] [TopologicalSpace R] [TopologicalSemiring R]

/- warning: polynomial_functions -> polynomialFunctions is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))] (X : Set.{u1} R), Subalgebra.{u1, u1} R (ContinuousMap.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) R (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) _inst_2) _inst_1 (ContinuousMap.semiring.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) R (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (ContinuousMap.algebra.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} R) Type.{u1} (Set.hasCoeToSort.{u1} R) X) (Subtype.topologicalSpace.{u1} R (fun (x : R) => Membership.Mem.{u1, u1} R (Set.{u1} R) (Set.hasMem.{u1} R) x X) _inst_2) R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommSemiring.{u1} R] [_inst_2 : TopologicalSpace.{u1} R] [_inst_3 : TopologicalSemiring.{u1} R _inst_2 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))] (X : Set.{u1} R), Subalgebra.{u1, u1} R (ContinuousMap.{u1, u1} (Set.Elem.{u1} R X) R (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) _inst_2) _inst_1 (ContinuousMap.instSemiringContinuousMap.{u1, u1} (Set.Elem.{u1} R X) R (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) _inst_3) (ContinuousMap.algebra.{u1, u1, u1} (Set.Elem.{u1} R X) (instTopologicalSpaceSubtype.{u1} R (fun (x : R) => Membership.mem.{u1, u1} R (Set.{u1} R) (Set.instMembershipSet.{u1} R) x X) _inst_2) R _inst_1 R _inst_2 (CommSemiring.toSemiring.{u1} R _inst_1) (Algebra.id.{u1} R _inst_1) _inst_3)
Case conversion may be inaccurate. Consider using '#align polynomial_functions polynomialFunctionsₓ'. -/
/--
The subalgebra of polynomial functions in `C(X, R)`, for `X` a subset of some topological semiring
`R`.
-/
def polynomialFunctions (X : Set R) : Subalgebra R C(X, R) :=
  (⊤ : Subalgebra R R[X]).map (Polynomial.toContinuousMapOnAlgHom X)
#align polynomial_functions polynomialFunctions

/- warning: polynomial_functions_coe -> polynomialFunctions_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_functions_coe polynomialFunctions_coeₓ'. -/
@[simp]
theorem polynomialFunctions_coe (X : Set R) :
    (polynomialFunctions X : Set C(X, R)) = Set.range (Polynomial.toContinuousMapOnAlgHom X) :=
  by
  ext
  simp [polynomialFunctions]
#align polynomial_functions_coe polynomialFunctions_coe

#print polynomialFunctions_separatesPoints /-
-- TODO:
-- if `f : R → R` is an affine equivalence, then pulling back along `f`
-- induces a normed algebra isomorphism between `polynomial_functions X` and
-- `polynomial_functions (f ⁻¹' X)`, intertwining the pullback along `f` of `C(R, R)` to itself.
theorem polynomialFunctions_separatesPoints (X : Set R) : (polynomialFunctions X).SeparatesPoints :=
  fun x y h =>
  by
  -- We use `polynomial.X`, then clean up.
  refine' ⟨_, ⟨⟨_, ⟨⟨Polynomial.X, ⟨Algebra.mem_top, rfl⟩⟩, rfl⟩⟩, _⟩⟩
  dsimp; simp only [Polynomial.eval_X]
  exact fun h' => h (Subtype.ext h')
#align polynomial_functions_separates_points polynomialFunctions_separatesPoints
-/

open unitInterval

open ContinuousMap

/- warning: polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I -> polynomialFunctions.comap_compRightAlgHom_iccHomeoI is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I polynomialFunctions.comap_compRightAlgHom_iccHomeoIₓ'. -/
/-- The preimage of polynomials on `[0,1]` under the pullback map by `x ↦ (b-a) * x + a`
is the polynomials on `[a,b]`. -/
theorem polynomialFunctions.comap_compRightAlgHom_iccHomeoI (a b : ℝ) (h : a < b) :
    (polynomialFunctions I).comap (compRightAlgHom ℝ ℝ (iccHomeoI a b h).symm.toContinuousMap) =
      polynomialFunctions (Set.Icc a b) :=
  by
  ext f
  fconstructor
  · rintro ⟨p, ⟨-, w⟩⟩
    rw [FunLike.ext_iff] at w
    dsimp at w
    let q := p.comp ((b - a)⁻¹ • Polynomial.X + Polynomial.C (-a * (b - a)⁻¹))
    refine' ⟨q, ⟨_, _⟩⟩
    · simp
    · ext x
      simp only [neg_mul, RingHom.map_neg, RingHom.map_mul, AlgHom.coe_toRingHom, Polynomial.eval_X,
        Polynomial.eval_neg, Polynomial.eval_C, Polynomial.eval_smul, smul_eq_mul,
        Polynomial.eval_mul, Polynomial.eval_add, Polynomial.coe_aeval_eq_eval,
        Polynomial.eval_comp, Polynomial.toContinuousMapOnAlgHom_apply,
        Polynomial.toContinuousMapOn_apply, Polynomial.toContinuousMap_apply]
      convert w ⟨_, _⟩ <;> clear w
      · -- why does `comm_ring.add` appear here!?
        change x = (iccHomeoI a b h).symm ⟨_ + _, _⟩
        ext
        simp only [iccHomeoI_symm_apply_coe, Subtype.coe_mk]
        replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.ne.symm
        simp only [mul_add]
        field_simp
        ring
      · change _ + _ ∈ I
        rw [mul_comm (b - a)⁻¹, ← neg_mul, ← add_mul, ← sub_eq_add_neg]
        have w₁ : 0 < (b - a)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
        have w₂ : 0 ≤ (x : ℝ) - a := sub_nonneg.mpr x.2.1
        have w₃ : (x : ℝ) - a ≤ b - a := sub_le_sub_right x.2.2 a
        fconstructor
        · exact mul_nonneg w₂ (le_of_lt w₁)
        · rw [← div_eq_mul_inv, div_le_one (sub_pos.mpr h)]
          exact w₃
  · rintro ⟨p, ⟨-, rfl⟩⟩
    let q := p.comp ((b - a) • Polynomial.X + Polynomial.C a)
    refine' ⟨q, ⟨_, _⟩⟩
    · simp
    · ext x
      simp [mul_comm]
#align polynomial_functions.comap_comp_right_alg_hom_Icc_homeo_I polynomialFunctions.comap_compRightAlgHom_iccHomeoI

end

