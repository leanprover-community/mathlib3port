/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

! This file was ported from Lean 3 source module analysis.normed_space.bounded_linear_maps
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Multilinear
import Mathbin.Analysis.NormedSpace.Units
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# Bounded linear maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition (because the space
is normed) that `‖f x‖` is bounded by a multiple of `‖x‖`. Hence the "bounded" in the name refers to
`‖f x‖/‖x‖` rather than `‖f x‖` itself.

## Main definitions

* `is_bounded_linear_map`: Class stating that a map `f : E → F` is linear and has `‖f x‖` bounded
  by a multiple of `‖x‖`.
* `is_bounded_bilinear_map`: Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `‖f (x, y)‖` is bounded by a multiple of
  `‖x‖ * ‖y‖`
* `is_bounded_bilinear_map.linear_deriv`: Derivative of a continuous bilinear map as a linear map.
* `is_bounded_bilinear_map.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `is_bounded_bilinear_map.has_fderiv_at` in
  `analysis.calculus.fderiv`.

## Main theorems

* `is_bounded_bilinear_map.continuous`: A bounded bilinear map is continuous.
* `continuous_linear_equiv.is_open`: The continuous linear equivalences are an open subset of the
  set of continuous linear maps between a pair of Banach spaces.  Placed in this file because its
  proof uses `is_bounded_bilinear_map.continuous`.

## Notes

The main use of this file is `is_bounded_bilinear_map`. The file `analysis.normed_space.multilinear`
already expounds the theory of multilinear maps, but the `2`-variables case is sufficiently simpler
to currently deserve its own treatment.

`is_bounded_linear_map` is effectively an unbundled version of `continuous_linear_map` (defined
in `topology.algebra.module.basic`, theory over normed spaces developed in
`analysis.normed_space.operator_norm`), albeit the name disparity. A bundled
`continuous_linear_map` is to be preferred over a `is_bounded_linear_map` hypothesis. Historical
artifact, really.
-/


noncomputable section

open BigOperators Topology

open Filter (Tendsto)

open Metric ContinuousLinearMap

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type _}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

#print IsBoundedLinearMap /-
/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `‖f x‖ ≤ M * ‖x‖` for some positive constant `M`. -/
structure IsBoundedLinearMap (𝕜 : Type _) [NormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : E → F) extends
  IsLinearMap 𝕜 f : Prop where
  bound : ∃ M, 0 < M ∧ ∀ x : E, ‖f x‖ ≤ M * ‖x‖
#align is_bounded_linear_map IsBoundedLinearMap
-/

/- warning: is_linear_map.with_bound -> IsLinearMap.with_bound is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsLinearMap.{u1, u2, u3} 𝕜 E F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) f) -> (forall (M : Real), (forall (x : E), LE.le.{0} Real Real.hasLe (Norm.norm.{u3} F (NormedAddCommGroup.toHasNorm.{u3} F _inst_4) (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) M (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x))) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsLinearMap.{u3, u2, u1} 𝕜 E F (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) f) -> (forall (M : Real), (forall (x : E), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (f x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) M (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x))) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f))
Case conversion may be inaccurate. Consider using '#align is_linear_map.with_bound IsLinearMap.with_boundₓ'. -/
theorem IsLinearMap.with_bound {f : E → F} (hf : IsLinearMap 𝕜 f) (M : ℝ)
    (h : ∀ x : E, ‖f x‖ ≤ M * ‖x‖) : IsBoundedLinearMap 𝕜 f :=
  ⟨hf,
    by_cases
      (fun this : M ≤ 0 =>
        ⟨1, zero_lt_one, fun x =>
          (h x).trans <| mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
      fun this : ¬M ≤ 0 => ⟨M, lt_of_not_ge this, h⟩⟩
#align is_linear_map.with_bound IsLinearMap.with_bound

/- warning: continuous_linear_map.is_bounded_linear_map -> ContinuousLinearMap.isBoundedLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.is_bounded_linear_map ContinuousLinearMap.isBoundedLinearMapₓ'. -/
/-- A continuous linear map satisfies `is_bounded_linear_map` -/
theorem ContinuousLinearMap.isBoundedLinearMap (f : E →L[𝕜] F) : IsBoundedLinearMap 𝕜 f :=
  { f.toLinearMap.isLinear with bound := f.bound }
#align continuous_linear_map.is_bounded_linear_map ContinuousLinearMap.isBoundedLinearMap

namespace IsBoundedLinearMap

#print IsBoundedLinearMap.toLinearMap /-
/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def toLinearMap (f : E → F) (h : IsBoundedLinearMap 𝕜 f) : E →ₗ[𝕜] F :=
  IsLinearMap.mk' _ h.to_isLinearMap
#align is_bounded_linear_map.to_linear_map IsBoundedLinearMap.toLinearMap
-/

#print IsBoundedLinearMap.toContinuousLinearMap /-
/-- Construct a continuous linear map from is_bounded_linear_map -/
def toContinuousLinearMap {f : E → F} (hf : IsBoundedLinearMap 𝕜 f) : E →L[𝕜] F :=
  { toLinearMap f hf with
    cont :=
      let ⟨C, Cpos, hC⟩ := hf.bound
      AddMonoidHomClass.continuous_of_bound (toLinearMap f hf) C hC }
#align is_bounded_linear_map.to_continuous_linear_map IsBoundedLinearMap.toContinuousLinearMap
-/

/- warning: is_bounded_linear_map.zero -> IsBoundedLinearMap.zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => OfNat.ofNat.{u3} F 0 (OfNat.mk.{u3} F 0 (Zero.zero.{u3} F (AddZeroClass.toHasZero.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)], IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (x : E) => OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.zero IsBoundedLinearMap.zeroₓ'. -/
theorem zero : IsBoundedLinearMap 𝕜 fun x : E => (0 : F) :=
  (0 : E →ₗ[𝕜] F).isLinear.with_bound 0 <| by simp [le_refl]
#align is_bounded_linear_map.zero IsBoundedLinearMap.zero

/- warning: is_bounded_linear_map.id -> IsBoundedLinearMap.id is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)], IsBoundedLinearMap.{u1, u2, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 E _inst_2 _inst_3 (fun (x : E) => x)
but is expected to have type
  forall {𝕜 : Type.{u2}} [_inst_1 : NontriviallyNormedField.{u2} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u2, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)], IsBoundedLinearMap.{u2, u1, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u2} 𝕜 _inst_1) E _inst_2 _inst_3 E _inst_2 _inst_3 (fun (x : E) => x)
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.id IsBoundedLinearMap.idₓ'. -/
theorem id : IsBoundedLinearMap 𝕜 fun x : E => x :=
  LinearMap.id.isLinear.with_bound 1 <| by simp [le_refl]
#align is_bounded_linear_map.id IsBoundedLinearMap.id

/- warning: is_bounded_linear_map.fst -> IsBoundedLinearMap.fst is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], IsBoundedLinearMap.{u1, max u2 u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) E _inst_2 _inst_3 (fun (x : Prod.{u2, u3} E F) => Prod.fst.{u2, u3} E F x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)], IsBoundedLinearMap.{u3, max u2 u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) E _inst_2 _inst_3 (fun (x : Prod.{u2, u1} E F) => Prod.fst.{u2, u1} E F x)
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.fst IsBoundedLinearMap.fstₓ'. -/
theorem fst : IsBoundedLinearMap 𝕜 fun x : E × F => x.1 :=
  by
  refine' (LinearMap.fst 𝕜 E F).isLinear.with_bound 1 fun x => _
  rw [one_mul]
  exact le_max_left _ _
#align is_bounded_linear_map.fst IsBoundedLinearMap.fst

/- warning: is_bounded_linear_map.snd -> IsBoundedLinearMap.snd is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)], IsBoundedLinearMap.{u1, max u2 u3, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (Prod.{u2, u3} E F) (Prod.normedAddCommGroup.{u2, u3} E F _inst_2 _inst_4) (Prod.normedSpace.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5) F _inst_4 _inst_5 (fun (x : Prod.{u2, u3} E F) => Prod.snd.{u2, u3} E F x)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)], IsBoundedLinearMap.{u3, max u2 u1, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (Prod.{u2, u1} E F) (Prod.normedAddCommGroup.{u2, u1} E F _inst_2 _inst_4) (Prod.normedSpace.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3 F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5) F _inst_4 _inst_5 (fun (x : Prod.{u2, u1} E F) => Prod.snd.{u2, u1} E F x)
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.snd IsBoundedLinearMap.sndₓ'. -/
theorem snd : IsBoundedLinearMap 𝕜 fun x : E × F => x.2 :=
  by
  refine' (LinearMap.snd 𝕜 E F).isLinear.with_bound 1 fun x => _
  rw [one_mul]
  exact le_max_right _ _
#align is_bounded_linear_map.snd IsBoundedLinearMap.snd

variable {f g : E → F}

/- warning: is_bounded_linear_map.smul -> IsBoundedLinearMap.smul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (c : 𝕜), (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (SMul.smul.{u1, max u2 u3} 𝕜 (E -> F) (Function.hasSMul.{u2, u1, u3} E 𝕜 F (SMulZeroClass.toHasSmul.{u1, u3} 𝕜 F (AddZeroClass.toHasZero.{u3} F (AddMonoid.toAddZeroClass.{u3} F (AddCommMonoid.toAddMonoid.{u3} F (AddCommGroup.toAddCommMonoid.{u3} F (SeminormedAddCommGroup.toAddCommGroup.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{u1, u3} 𝕜 F (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))))) (AddZeroClass.toHasZero.{u3} F (AddMonoid.toAddZeroClass.{u3} F (AddCommMonoid.toAddMonoid.{u3} F (AddCommGroup.toAddCommMonoid.{u3} F (SeminormedAddCommGroup.toAddCommGroup.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u1, u3} 𝕜 F (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))) (AddZeroClass.toHasZero.{u3} F (AddMonoid.toAddZeroClass.{u3} F (AddCommMonoid.toAddMonoid.{u3} F (AddCommGroup.toAddCommMonoid.{u3} F (SeminormedAddCommGroup.toAddCommGroup.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))))) (Module.toMulActionWithZero.{u1, u3} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u3} F (SeminormedAddCommGroup.toAddCommGroup.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4))) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)))))) c f))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (c : 𝕜), (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (HSMul.hSMul.{u3, max u2 u1, max u2 u1} 𝕜 (E -> F) (E -> F) (instHSMul.{u3, max u2 u1} 𝕜 (E -> F) (Pi.instSMul.{u2, u1, u3} E 𝕜 (fun (a._@.Mathlib.Analysis.NormedSpace.BoundedLinearMaps._hyg.875 : E) => F) (fun (i : E) => SMulZeroClass.toSMul.{u3, u1} 𝕜 F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{u3, u1} 𝕜 F (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1)))))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{u3, u1} 𝕜 F (Semiring.toMonoidWithZero.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1)))))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{u3, u1} 𝕜 F (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) _inst_5))))))) c f))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.smul IsBoundedLinearMap.smulₓ'. -/
theorem smul (c : 𝕜) (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 (c • f) :=
  let ⟨hlf, M, hMp, hM⟩ := hf
  (c • hlf.mk' f).isLinear.with_bound (‖c‖ * M) fun x =>
    calc
      ‖c • f x‖ = ‖c‖ * ‖f x‖ := norm_smul c (f x)
      _ ≤ ‖c‖ * (M * ‖x‖) := (mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _))
      _ = ‖c‖ * M * ‖x‖ := (mul_assoc _ _ _).symm
      
#align is_bounded_linear_map.smul IsBoundedLinearMap.smul

/- warning: is_bounded_linear_map.neg -> IsBoundedLinearMap.neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => Neg.neg.{u3} F (SubNegMonoid.toHasNeg.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))) (f e)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (f e)))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.neg IsBoundedLinearMap.negₓ'. -/
theorem neg (hf : IsBoundedLinearMap 𝕜 f) : IsBoundedLinearMap 𝕜 fun e => -f e :=
  by
  rw [show (fun e => -f e) = fun e => (-1 : 𝕜) • f e by funext; simp]
  exact smul (-1) hf
#align is_bounded_linear_map.neg IsBoundedLinearMap.neg

/- warning: is_bounded_linear_map.add -> IsBoundedLinearMap.add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => HAdd.hAdd.{u3, u3, u3} F F F (instHAdd.{u3} F (AddZeroClass.toHasAdd.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))))) (f e) (g e)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) (f e) (g e)))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.add IsBoundedLinearMap.addₓ'. -/
theorem add (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e + g e :=
  let ⟨hlf, Mf, hMfp, hMf⟩ := hf
  let ⟨hlg, Mg, hMgp, hMg⟩ := hg
  (hlf.mk' _ + hlg.mk' _).isLinear.with_bound (Mf + Mg) fun x =>
    calc
      ‖f x + g x‖ ≤ Mf * ‖x‖ + Mg * ‖x‖ := norm_add_le_of_le (hMf x) (hMg x)
      _ ≤ (Mf + Mg) * ‖x‖ := by rw [add_mul]
      
#align is_bounded_linear_map.add IsBoundedLinearMap.add

/- warning: is_bounded_linear_map.sub -> IsBoundedLinearMap.sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} {g : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) (f e) (g e)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} {g : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 g) -> (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 (fun (e : E) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) (f e) (g e)))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.sub IsBoundedLinearMap.subₓ'. -/
theorem sub (hf : IsBoundedLinearMap 𝕜 f) (hg : IsBoundedLinearMap 𝕜 g) :
    IsBoundedLinearMap 𝕜 fun e => f e - g e := by simpa [sub_eq_add_neg] using add hf (neg hg)
#align is_bounded_linear_map.sub IsBoundedLinearMap.sub

/- warning: is_bounded_linear_map.comp -> IsBoundedLinearMap.comp is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : E -> F} {g : F -> G}, (IsBoundedLinearMap.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 g) -> (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u1, u2, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 G _inst_6 _inst_7 (Function.comp.{succ u2, succ u3, succ u4} E F G g f))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u1}} [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : NormedSpace.{u4, u1} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u4, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u2}} [_inst_6 : NormedAddCommGroup.{u2} G] [_inst_7 : NormedSpace.{u4, u2} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} G _inst_6)] {f : E -> F} {g : F -> G}, (IsBoundedLinearMap.{u4, u3, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 g) -> (IsBoundedLinearMap.{u4, u1, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (IsBoundedLinearMap.{u4, u1, u2} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) E _inst_2 _inst_3 G _inst_6 _inst_7 (Function.comp.{succ u1, succ u3, succ u2} E F G g f))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.comp IsBoundedLinearMap.compₓ'. -/
theorem comp {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) (hf : IsBoundedLinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 (g ∘ f) :=
  (hg.toContinuousLinearMap.comp hf.toContinuousLinearMap).IsBoundedLinearMap
#align is_bounded_linear_map.comp IsBoundedLinearMap.comp

/- warning: is_bounded_linear_map.tendsto -> IsBoundedLinearMap.tendsto is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F} (x : E), (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Filter.Tendsto.{u2, u3} E F f (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) x) (nhds.{u3} F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (f x)))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F} (x : E), (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Filter.Tendsto.{u2, u1} E F f (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) x) (nhds.{u1} F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (f x)))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.tendsto IsBoundedLinearMap.tendstoₓ'. -/
protected theorem tendsto (x : E) (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 x) (𝓝 (f x)) :=
  let ⟨hf, M, hMp, hM⟩ := hf
  tendsto_iff_norm_tendsto_zero.2 <|
    squeeze_zero (fun e => norm_nonneg _)
      (fun e =>
        calc
          ‖f e - f x‖ = ‖hf.mk' f (e - x)‖ := by rw [(hf.mk' _).map_sub e x] <;> rfl
          _ ≤ M * ‖e - x‖ := hM (e - x)
          )
      (suffices Tendsto (fun e : E => M * ‖e - x‖) (𝓝 x) (𝓝 (M * 0)) by simpa
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))
#align is_bounded_linear_map.tendsto IsBoundedLinearMap.tendsto

/- warning: is_bounded_linear_map.continuous -> IsBoundedLinearMap.continuous is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Continuous.{u2, u3} E F (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Continuous.{u2, u1} E F (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) f)
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.continuous IsBoundedLinearMap.continuousₓ'. -/
theorem continuous (hf : IsBoundedLinearMap 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun _ => hf.Tendsto _
#align is_bounded_linear_map.continuous IsBoundedLinearMap.continuous

/- warning: is_bounded_linear_map.lim_zero_bounded_linear_map -> IsBoundedLinearMap.lim_zero_bounded_linear_map is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Filter.Tendsto.{u2, u3} E F f (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) (nhds.{u3} F (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (OfNat.ofNat.{u3} F 0 (OfNat.mk.{u3} F 0 (Zero.zero.{u3} F (AddZeroClass.toHasZero.{u3} F (AddMonoid.toAddZeroClass.{u3} F (SubNegMonoid.toAddMonoid.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4)))))))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (Filter.Tendsto.{u2, u1} E F f (nhds.{u2} E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) (nhds.{u1} F (UniformSpace.toTopologicalSpace.{u1} F (PseudoMetricSpace.toUniformSpace.{u1} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.lim_zero_bounded_linear_map IsBoundedLinearMap.lim_zero_bounded_linear_mapₓ'. -/
theorem lim_zero_bounded_linear_map (hf : IsBoundedLinearMap 𝕜 f) : Tendsto f (𝓝 0) (𝓝 0) :=
  (hf.1.mk' _).map_zero ▸ continuous_iff_continuousAt.1 hf.Continuous 0
#align is_bounded_linear_map.lim_zero_bounded_linear_map IsBoundedLinearMap.lim_zero_bounded_linear_map

section

open Asymptotics Filter

/- warning: is_bounded_linear_map.is_O_id -> IsBoundedLinearMap.isBigO_id is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (l : Filter.{u2} E), Asymptotics.IsBigO.{u2, u3, u2} E F E (NormedAddCommGroup.toHasNorm.{u3} F _inst_4) (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) l f (fun (x : E) => x))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (l : Filter.{u2} E), Asymptotics.IsBigO.{u2, u1, u2} E F E (NormedAddCommGroup.toNorm.{u1} F _inst_4) (NormedAddCommGroup.toNorm.{u2} E _inst_2) l f (fun (x : E) => x))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.is_O_id IsBoundedLinearMap.isBigO_idₓ'. -/
theorem isBigO_id {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) : f =O[l] fun x => x :=
  let ⟨M, hMp, hM⟩ := h.bound
  IsBigO.of_bound _ (mem_of_superset univ_mem fun x _ => hM x)
#align is_bounded_linear_map.is_O_id IsBoundedLinearMap.isBigO_id

/- warning: is_bounded_linear_map.is_O_comp -> IsBoundedLinearMap.isBigO_comp is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u1, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u3}} [_inst_6 : NormedAddCommGroup.{u3} G] [_inst_7 : NormedSpace.{u1, u3} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} G _inst_6)] {E : Type.{u4}} {g : F -> G}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 g) -> (forall {f : E -> F} (l : Filter.{u4} E), Asymptotics.IsBigO.{u4, u3, u2} E G F (NormedAddCommGroup.toHasNorm.{u3} G _inst_6) (NormedAddCommGroup.toHasNorm.{u2} F _inst_4) l (fun (x' : E) => g (f x')) f)
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u3, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u3, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {E : Type.{u4}} {g : F -> G}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 g) -> (forall {f : E -> F} (l : Filter.{u4} E), Asymptotics.IsBigO.{u4, u1, u2} E G F (NormedAddCommGroup.toNorm.{u1} G _inst_6) (NormedAddCommGroup.toNorm.{u2} F _inst_4) l (fun (x' : E) => g (f x')) f)
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.is_O_comp IsBoundedLinearMap.isBigO_compₓ'. -/
theorem isBigO_comp {E : Type _} {g : F → G} (hg : IsBoundedLinearMap 𝕜 g) {f : E → F}
    (l : Filter E) : (fun x' => g (f x')) =O[l] f :=
  (hg.isBigO_id ⊤).comp_tendsto le_top
#align is_bounded_linear_map.is_O_comp IsBoundedLinearMap.isBigO_comp

/- warning: is_bounded_linear_map.is_O_sub -> IsBoundedLinearMap.isBigO_sub is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u1, u2, u3} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (l : Filter.{u2} E) (x : E), Asymptotics.IsBigO.{u2, u3, u2} E F E (NormedAddCommGroup.toHasNorm.{u3} F _inst_4) (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) l (fun (x' : E) => f (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x' x)) (fun (x' : E) => HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x' x))
but is expected to have type
  forall {𝕜 : Type.{u3}} [_inst_1 : NontriviallyNormedField.{u3} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u3, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : NormedSpace.{u3, u1} 𝕜 F (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)] {f : E -> F}, (IsBoundedLinearMap.{u3, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u3} 𝕜 _inst_1) E _inst_2 _inst_3 F _inst_4 _inst_5 f) -> (forall (l : Filter.{u2} E) (x : E), Asymptotics.IsBigO.{u2, u1, u2} E F E (NormedAddCommGroup.toNorm.{u1} F _inst_4) (NormedAddCommGroup.toNorm.{u2} E _inst_2) l (fun (x' : E) => f (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x' x)) (fun (x' : E) => HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x' x))
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map.is_O_sub IsBoundedLinearMap.isBigO_subₓ'. -/
theorem isBigO_sub {f : E → F} (h : IsBoundedLinearMap 𝕜 f) (l : Filter E) (x : E) :
    (fun x' => f (x' - x)) =O[l] fun x' => x' - x :=
  isBigO_comp h l
#align is_bounded_linear_map.is_O_sub IsBoundedLinearMap.isBigO_sub

end

end IsBoundedLinearMap

section

variable {ι : Type _} [Fintype ι]

/- warning: is_bounded_linear_map_prod_multilinear -> isBoundedLinearMap_prod_multilinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map_prod_multilinear isBoundedLinearMap_prod_multilinearₓ'. -/
/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
theorem isBoundedLinearMap_prod_multilinear {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedLinearMap 𝕜 fun p : ContinuousMultilinearMap 𝕜 E F × ContinuousMultilinearMap 𝕜 E G =>
      p.1.Prod p.2 :=
  { map_add := fun p₁ p₂ => by ext1 m; rfl
    map_smul := fun c p => by ext1 m; rfl
    bound :=
      ⟨1, zero_lt_one, fun p => by
        rw [one_mul]
        apply ContinuousMultilinearMap.op_norm_le_bound _ (norm_nonneg _) fun m => _
        rw [ContinuousMultilinearMap.prod_apply, norm_prod_le_iff]
        constructor
        ·
          exact
            (p.1.le_op_norm m).trans
              (mul_le_mul_of_nonneg_right (norm_fst_le p)
                (Finset.prod_nonneg fun i hi => norm_nonneg _))
        ·
          exact
            (p.2.le_op_norm m).trans
              (mul_le_mul_of_nonneg_right (norm_snd_le p)
                (Finset.prod_nonneg fun i hi => norm_nonneg _))⟩ }
#align is_bounded_linear_map_prod_multilinear isBoundedLinearMap_prod_multilinear

/- warning: is_bounded_linear_map_continuous_multilinear_map_comp_linear -> isBoundedLinearMap_continuousMultilinearMap_comp_linear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_linear_map_continuous_multilinear_map_comp_linear isBoundedLinearMap_continuousMultilinearMap_comp_linearₓ'. -/
/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
theorem isBoundedLinearMap_continuousMultilinearMap_comp_linear (g : G →L[𝕜] E) :
    IsBoundedLinearMap 𝕜 fun f : ContinuousMultilinearMap 𝕜 (fun i : ι => E) F =>
      f.compContinuousLinearMap fun _ => g :=
  by
  refine'
    IsLinearMap.with_bound ⟨fun f₁ f₂ => by ext m; rfl, fun c f => by ext m; rfl⟩
      (‖g‖ ^ Fintype.card ι) fun f => _
  apply ContinuousMultilinearMap.op_norm_le_bound _ _ fun m => _
  · apply_rules [mul_nonneg, pow_nonneg, norm_nonneg]
  calc
    ‖f (g ∘ m)‖ ≤ ‖f‖ * ∏ i, ‖g (m i)‖ := f.le_op_norm _
    _ ≤ ‖f‖ * ∏ i, ‖g‖ * ‖m i‖ :=
      by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun i hi => norm_nonneg _) fun i hi => g.le_op_norm _
    _ = ‖g‖ ^ Fintype.card ι * ‖f‖ * ∏ i, ‖m i‖ := by
      simp [Finset.prod_mul_distrib, Finset.card_univ]; ring
    
#align is_bounded_linear_map_continuous_multilinear_map_comp_linear isBoundedLinearMap_continuousMultilinearMap_comp_linear

end

section BilinearMap

namespace ContinuousLinearMap

/-! We prove some computation rules for continuous (semi-)bilinear maps in their first argument.
  If `f` is a continuuous bilinear map, to use the corresponding rules for the second argument, use
  `(f _).map_add` and similar.

We have to assume that `F` and `G` are normed spaces in this section, to use
`continuous_linear_map.to_normed_add_comm_group`, but we don't need to assume this for the first
argument of `f`.
-/


variable {R : Type _}

variable {𝕜₂ 𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NontriviallyNormedField 𝕜₂]

variable {M : Type _} [TopologicalSpace M]

variable {σ₁₂ : 𝕜 →+* 𝕜₂}

variable {G' : Type _} [NormedAddCommGroup G'] [NormedSpace 𝕜₂ G'] [NormedSpace 𝕜' G']

variable [SMulCommClass 𝕜₂ 𝕜' G']

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

/- warning: continuous_linear_map.map_add₂ -> ContinuousLinearMap.map_add₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_add₂ ContinuousLinearMap.map_add₂ₓ'. -/
theorem map_add₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
    f (x + x') y = f x y + f x' y := by rw [f.map_add, add_apply]
#align continuous_linear_map.map_add₂ ContinuousLinearMap.map_add₂

/- warning: continuous_linear_map.map_zero₂ -> ContinuousLinearMap.map_zero₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_zero₂ ContinuousLinearMap.map_zero₂ₓ'. -/
theorem map_zero₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (y : F) : f 0 y = 0 := by
  rw [f.map_zero, zero_apply]
#align continuous_linear_map.map_zero₂ ContinuousLinearMap.map_zero₂

/- warning: continuous_linear_map.map_smulₛₗ₂ -> ContinuousLinearMap.map_smulₛₗ₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_smulₛₗ₂ ContinuousLinearMap.map_smulₛₗ₂ₓ'. -/
theorem map_smulₛₗ₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (c : R) (x : M) (y : F) :
    f (c • x) y = ρ₁₂ c • f x y := by rw [f.map_smulₛₗ, smul_apply]
#align continuous_linear_map.map_smulₛₗ₂ ContinuousLinearMap.map_smulₛₗ₂

end Semiring

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] {ρ₁₂ : R →+* 𝕜'}

/- warning: continuous_linear_map.map_sub₂ -> ContinuousLinearMap.map_sub₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_sub₂ ContinuousLinearMap.map_sub₂ₓ'. -/
theorem map_sub₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x x' : M) (y : F) :
    f (x - x') y = f x y - f x' y := by rw [f.map_sub, sub_apply]
#align continuous_linear_map.map_sub₂ ContinuousLinearMap.map_sub₂

/- warning: continuous_linear_map.map_neg₂ -> ContinuousLinearMap.map_neg₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_neg₂ ContinuousLinearMap.map_neg₂ₓ'. -/
theorem map_neg₂ (f : M →SL[ρ₁₂] F →SL[σ₁₂] G') (x : M) (y : F) : f (-x) y = -f x y := by
  rw [f.map_neg, neg_apply]
#align continuous_linear_map.map_neg₂ ContinuousLinearMap.map_neg₂

end Ring

/- warning: continuous_linear_map.map_smul₂ -> ContinuousLinearMap.map_smul₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_smul₂ ContinuousLinearMap.map_smul₂ₓ'. -/
theorem map_smul₂ (f : E →L[𝕜] F →L[𝕜] G) (c : 𝕜) (x : E) (y : F) : f (c • x) y = c • f x y := by
  rw [f.map_smul, smul_apply]
#align continuous_linear_map.map_smul₂ ContinuousLinearMap.map_smul₂

end ContinuousLinearMap

variable (𝕜)

#print IsBoundedBilinearMap /-
/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure IsBoundedBilinearMap (f : E × F → G) : Prop where
  add_left : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y)
  smul_left : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y)
  add_right : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂)
  smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x, y)
  bound : ∃ C > 0, ∀ (x : E) (y : F), ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖
#align is_bounded_bilinear_map IsBoundedBilinearMap
-/

variable {𝕜}

variable {f : E × F → G}

/- warning: continuous_linear_map.is_bounded_bilinear_map -> ContinuousLinearMap.isBoundedBilinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.is_bounded_bilinear_map ContinuousLinearMap.isBoundedBilinearMapₓ'. -/
theorem ContinuousLinearMap.isBoundedBilinearMap (f : E →L[𝕜] F →L[𝕜] G) :
    IsBoundedBilinearMap 𝕜 fun x : E × F => f x.1 x.2 :=
  { add_left := f.map_add₂
    smul_left := f.map_smul₂
    add_right := fun x => (f x).map_add
    smul_right := fun c x => (f x).map_smul c
    bound :=
      ⟨max ‖f‖ 1, zero_lt_one.trans_le (le_max_right _ _), fun x y =>
        (f.le_op_norm₂ x y).trans <| by
          apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_left] ⟩ }
#align continuous_linear_map.is_bounded_bilinear_map ContinuousLinearMap.isBoundedBilinearMap

/- warning: is_bounded_bilinear_map.is_O -> IsBoundedBilinearMap.isBigO is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Asymptotics.IsBigO.{max u2 u3, u4, 0} (Prod.{u2, u3} E F) G Real (NormedAddCommGroup.toHasNorm.{u4} G _inst_6) Real.hasNorm (Top.top.{max u2 u3} (Filter.{max u2 u3} (Prod.{u2, u3} E F)) (Filter.hasTop.{max u2 u3} (Prod.{u2, u3} E F))) f (fun (p : Prod.{u2, u3} E F) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (Prod.fst.{u2, u3} E F p)) (Norm.norm.{u3} F (NormedAddCommGroup.toHasNorm.{u3} F _inst_4) (Prod.snd.{u2, u3} E F p))))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Asymptotics.IsBigO.{max u3 u2, u1, 0} (Prod.{u3, u2} E F) G Real (NormedAddCommGroup.toNorm.{u1} G _inst_6) Real.norm (Top.top.{max u3 u2} (Filter.{max u3 u2} (Prod.{u3, u2} E F)) (Filter.instTopFilter.{max u3 u2} (Prod.{u3, u2} E F))) f (fun (p : Prod.{u3, u2} E F) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u3} E (NormedAddCommGroup.toNorm.{u3} E _inst_2) (Prod.fst.{u3, u2} E F p)) (Norm.norm.{u2} F (NormedAddCommGroup.toNorm.{u2} F _inst_4) (Prod.snd.{u3, u2} E F p))))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_O IsBoundedBilinearMap.isBigOₓ'. -/
protected theorem IsBoundedBilinearMap.isBigO (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p.1‖ * ‖p.2‖ :=
  let ⟨C, Cpos, hC⟩ := h.bound
  Asymptotics.IsBigO.of_bound _ <|
    Filter.eventually_of_forall fun ⟨x, y⟩ => by simpa [mul_assoc] using hC x y
#align is_bounded_bilinear_map.is_O IsBoundedBilinearMap.isBigO

/- warning: is_bounded_bilinear_map.is_O_comp -> IsBoundedBilinearMap.isBigO_comp is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G} {α : Type.{u5}}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {g : α -> E} {h : α -> F} {l : Filter.{u5} α}, Asymptotics.IsBigO.{u5, u4, 0} α G Real (NormedAddCommGroup.toHasNorm.{u4} G _inst_6) Real.hasNorm l (fun (x : α) => f (Prod.mk.{u2, u3} E F (g x) (h x))) (fun (x : α) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (g x)) (Norm.norm.{u3} F (NormedAddCommGroup.toHasNorm.{u3} F _inst_4) (h x))))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G} {α : Type.{u5}}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {g : α -> E} {h : α -> F} {l : Filter.{u5} α}, Asymptotics.IsBigO.{u5, u1, 0} α G Real (NormedAddCommGroup.toNorm.{u1} G _inst_6) Real.norm l (fun (x : α) => f (Prod.mk.{u3, u2} E F (g x) (h x))) (fun (x : α) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u3} E (NormedAddCommGroup.toNorm.{u3} E _inst_2) (g x)) (Norm.norm.{u2} F (NormedAddCommGroup.toNorm.{u2} F _inst_4) (h x))))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_O_comp IsBoundedBilinearMap.isBigO_compₓ'. -/
theorem IsBoundedBilinearMap.isBigO_comp {α : Type _} (H : IsBoundedBilinearMap 𝕜 f) {g : α → E}
    {h : α → F} {l : Filter α} : (fun x => f (g x, h x)) =O[l] fun x => ‖g x‖ * ‖h x‖ :=
  H.IsBigO.comp_tendsto le_top
#align is_bounded_bilinear_map.is_O_comp IsBoundedBilinearMap.isBigO_comp

/- warning: is_bounded_bilinear_map.is_O' -> IsBoundedBilinearMap.isBigO' is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Asymptotics.IsBigO.{max u2 u3, u4, 0} (Prod.{u2, u3} E F) G Real (NormedAddCommGroup.toHasNorm.{u4} G _inst_6) Real.hasNorm (Top.top.{max u2 u3} (Filter.{max u2 u3} (Prod.{u2, u3} E F)) (Filter.hasTop.{max u2 u3} (Prod.{u2, u3} E F))) f (fun (p : Prod.{u2, u3} E F) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{max u2 u3} (Prod.{u2, u3} E F) (Prod.hasNorm.{u2, u3} E F (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (NormedAddCommGroup.toHasNorm.{u3} F _inst_4)) p) (Norm.norm.{max u2 u3} (Prod.{u2, u3} E F) (Prod.hasNorm.{u2, u3} E F (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (NormedAddCommGroup.toHasNorm.{u3} F _inst_4)) p)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Asymptotics.IsBigO.{max u3 u2, u1, 0} (Prod.{u3, u2} E F) G Real (NormedAddCommGroup.toNorm.{u1} G _inst_6) Real.norm (Top.top.{max u3 u2} (Filter.{max u3 u2} (Prod.{u3, u2} E F)) (Filter.instTopFilter.{max u3 u2} (Prod.{u3, u2} E F))) f (fun (p : Prod.{u3, u2} E F) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{max u3 u2} (Prod.{u3, u2} E F) (Prod.toNorm.{u3, u2} E F (NormedAddCommGroup.toNorm.{u3} E _inst_2) (NormedAddCommGroup.toNorm.{u2} F _inst_4)) p) (Norm.norm.{max u3 u2} (Prod.{u3, u2} E F) (Prod.toNorm.{u3, u2} E F (NormedAddCommGroup.toNorm.{u3} E _inst_2) (NormedAddCommGroup.toNorm.{u2} F _inst_4)) p)))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_O' IsBoundedBilinearMap.isBigO'ₓ'. -/
protected theorem IsBoundedBilinearMap.isBigO' (h : IsBoundedBilinearMap 𝕜 f) :
    f =O[⊤] fun p : E × F => ‖p‖ * ‖p‖ :=
  h.IsBigO.trans <|
    (@Asymptotics.isBigO_fst_prod' _ E F _ _ _ _).norm_norm.mul
      (@Asymptotics.isBigO_snd_prod' _ E F _ _ _ _).norm_norm
#align is_bounded_bilinear_map.is_O' IsBoundedBilinearMap.isBigO'

/- warning: is_bounded_bilinear_map.map_sub_left -> IsBoundedBilinearMap.map_sub_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {x : E} {y : E} {z : F}, Eq.{succ u4} G (f (Prod.mk.{u2, u3} E F (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y) z)) (HSub.hSub.{u4, u4, u4} G G G (instHSub.{u4} G (SubNegMonoid.toHasSub.{u4} G (AddGroup.toSubNegMonoid.{u4} G (NormedAddGroup.toAddGroup.{u4} G (NormedAddCommGroup.toNormedAddGroup.{u4} G _inst_6))))) (f (Prod.mk.{u2, u3} E F x z)) (f (Prod.mk.{u2, u3} E F y z))))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {x : E} {y : E} {z : F}, Eq.{succ u1} G (f (Prod.mk.{u3, u2} E F (HSub.hSub.{u3, u3, u3} E E E (instHSub.{u3} E (SubNegMonoid.toSub.{u3} E (AddGroup.toSubNegMonoid.{u3} E (NormedAddGroup.toAddGroup.{u3} E (NormedAddCommGroup.toNormedAddGroup.{u3} E _inst_2))))) x y) z)) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (NormedAddGroup.toAddGroup.{u1} G (NormedAddCommGroup.toNormedAddGroup.{u1} G _inst_6))))) (f (Prod.mk.{u3, u2} E F x z)) (f (Prod.mk.{u3, u2} E F y z))))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.map_sub_left IsBoundedBilinearMap.map_sub_leftₓ'. -/
theorem IsBoundedBilinearMap.map_sub_left (h : IsBoundedBilinearMap 𝕜 f) {x y : E} {z : F} :
    f (x - y, z) = f (x, z) - f (y, z) :=
  calc
    f (x - y, z) = f (x + (-1 : 𝕜) • y, z) := by simp [sub_eq_add_neg]
    _ = f (x, z) + (-1 : 𝕜) • f (y, z) := by simp only [h.add_left, h.smul_left]
    _ = f (x, z) - f (y, z) := by simp [sub_eq_add_neg]
    
#align is_bounded_bilinear_map.map_sub_left IsBoundedBilinearMap.map_sub_left

/- warning: is_bounded_bilinear_map.map_sub_right -> IsBoundedBilinearMap.map_sub_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {x : E} {y : F} {z : F}, Eq.{succ u4} G (f (Prod.mk.{u2, u3} E F x (HSub.hSub.{u3, u3, u3} F F F (instHSub.{u3} F (SubNegMonoid.toHasSub.{u3} F (AddGroup.toSubNegMonoid.{u3} F (NormedAddGroup.toAddGroup.{u3} F (NormedAddCommGroup.toNormedAddGroup.{u3} F _inst_4))))) y z))) (HSub.hSub.{u4, u4, u4} G G G (instHSub.{u4} G (SubNegMonoid.toHasSub.{u4} G (AddGroup.toSubNegMonoid.{u4} G (NormedAddGroup.toAddGroup.{u4} G (NormedAddCommGroup.toNormedAddGroup.{u4} G _inst_6))))) (f (Prod.mk.{u2, u3} E F x y)) (f (Prod.mk.{u2, u3} E F x z))))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {x : E} {y : F} {z : F}, Eq.{succ u1} G (f (Prod.mk.{u3, u2} E F x (HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (SubNegMonoid.toSub.{u2} F (AddGroup.toSubNegMonoid.{u2} F (NormedAddGroup.toAddGroup.{u2} F (NormedAddCommGroup.toNormedAddGroup.{u2} F _inst_4))))) y z))) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (NormedAddGroup.toAddGroup.{u1} G (NormedAddCommGroup.toNormedAddGroup.{u1} G _inst_6))))) (f (Prod.mk.{u3, u2} E F x y)) (f (Prod.mk.{u3, u2} E F x z))))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.map_sub_right IsBoundedBilinearMap.map_sub_rightₓ'. -/
theorem IsBoundedBilinearMap.map_sub_right (h : IsBoundedBilinearMap 𝕜 f) {x : E} {y z : F} :
    f (x, y - z) = f (x, y) - f (x, z) :=
  calc
    f (x, y - z) = f (x, y + (-1 : 𝕜) • z) := by simp [sub_eq_add_neg]
    _ = f (x, y) + (-1 : 𝕜) • f (x, z) := by simp only [h.add_right, h.smul_right]
    _ = f (x, y) - f (x, z) := by simp [sub_eq_add_neg]
    
#align is_bounded_bilinear_map.map_sub_right IsBoundedBilinearMap.map_sub_right

/- warning: is_bounded_bilinear_map.continuous -> IsBoundedBilinearMap.continuous is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Continuous.{max u2 u3, u4} (Prod.{u2, u3} E F) G (Prod.topologicalSpace.{u2, u3} E F (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4))))) (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) f)
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Continuous.{max u3 u2, u1} (Prod.{u3, u2} E F) G (instTopologicalSpaceProd.{u3, u2} E F (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4))))) (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)))) f)
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.continuous IsBoundedBilinearMap.continuousₓ'. -/
/-- Useful to use together with `continuous.comp₂`. -/
theorem IsBoundedBilinearMap.continuous (h : IsBoundedBilinearMap 𝕜 f) : Continuous f :=
  by
  have one_ne : (1 : ℝ) ≠ 0 := by simp
  obtain ⟨C, Cpos : 0 < C, hC⟩ := h.bound
  rw [continuous_iff_continuousAt]
  intro x
  have H : ∀ (a : E) (b : F), ‖f (a, b)‖ ≤ C * ‖‖a‖ * ‖b‖‖ :=
    by
    intro a b
    simpa [mul_assoc] using hC a b
  have h₁ : (fun e : E × F => f (e.1 - x.1, e.2)) =o[𝓝 x] fun e => (1 : ℝ) :=
    by
    refine' (Asymptotics.isBigO_of_le' (𝓝 x) fun e => H (e.1 - x.1) e.2).trans_isLittleO _
    rw [Asymptotics.isLittleO_const_iff one_ne]
    convert((continuous_fst.sub continuous_const).norm.mul continuous_snd.norm).ContinuousAt
    · simp
    infer_instance
  have h₂ : (fun e : E × F => f (x.1, e.2 - x.2)) =o[𝓝 x] fun e => (1 : ℝ) :=
    by
    refine' (Asymptotics.isBigO_of_le' (𝓝 x) fun e => H x.1 (e.2 - x.2)).trans_isLittleO _
    rw [Asymptotics.isLittleO_const_iff one_ne]
    convert(continuous_const.mul (continuous_snd.sub continuous_const).norm).ContinuousAt
    · simp
    infer_instance
  have := h₁.add h₂
  rw [Asymptotics.isLittleO_const_iff one_ne] at this
  change tendsto _ _ _
  convert this.add_const (f x)
  · ext e
    simp [h.map_sub_left, h.map_sub_right]
  · simp
#align is_bounded_bilinear_map.continuous IsBoundedBilinearMap.continuous

/- warning: is_bounded_bilinear_map.continuous_left -> IsBoundedBilinearMap.continuous_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {e₂ : F}, Continuous.{u2, u4} E G (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (fun (e₁ : E) => f (Prod.mk.{u2, u3} E F e₁ e₂)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {e₂ : F}, Continuous.{u3, u1} E G (UniformSpace.toTopologicalSpace.{u3} E (PseudoMetricSpace.toUniformSpace.{u3} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)))) (fun (e₁ : E) => f (Prod.mk.{u3, u2} E F e₁ e₂)))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.continuous_left IsBoundedBilinearMap.continuous_leftₓ'. -/
theorem IsBoundedBilinearMap.continuous_left (h : IsBoundedBilinearMap 𝕜 f) {e₂ : F} :
    Continuous fun e₁ => f (e₁, e₂) :=
  h.Continuous.comp (continuous_id.prod_mk continuous_const)
#align is_bounded_bilinear_map.continuous_left IsBoundedBilinearMap.continuous_left

/- warning: is_bounded_bilinear_map.continuous_right -> IsBoundedBilinearMap.continuous_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {e₁ : E}, Continuous.{u3, u4} F G (UniformSpace.toTopologicalSpace.{u3} F (PseudoMetricSpace.toUniformSpace.{u3} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)))) (UniformSpace.toTopologicalSpace.{u4} G (PseudoMetricSpace.toUniformSpace.{u4} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u4} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)))) (fun (e₂ : F) => f (Prod.mk.{u2, u3} E F e₁ e₂)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall {e₁ : E}, Continuous.{u2, u1} F G (UniformSpace.toTopologicalSpace.{u2} F (PseudoMetricSpace.toUniformSpace.{u2} F (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)))) (UniformSpace.toTopologicalSpace.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)))) (fun (e₂ : F) => f (Prod.mk.{u3, u2} E F e₁ e₂)))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.continuous_right IsBoundedBilinearMap.continuous_rightₓ'. -/
theorem IsBoundedBilinearMap.continuous_right (h : IsBoundedBilinearMap 𝕜 f) {e₁ : E} :
    Continuous fun e₂ => f (e₁, e₂) :=
  h.Continuous.comp (continuous_const.prod_mk continuous_id)
#align is_bounded_bilinear_map.continuous_right IsBoundedBilinearMap.continuous_right

/- warning: continuous_linear_map.continuous₂ -> ContinuousLinearMap.continuous₂ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.continuous₂ ContinuousLinearMap.continuous₂ₓ'. -/
/-- Useful to use together with `continuous.comp₂`. -/
theorem ContinuousLinearMap.continuous₂ (f : E →L[𝕜] F →L[𝕜] G) :
    Continuous (Function.uncurry fun x y => f x y) :=
  f.IsBoundedBilinearMap.Continuous
#align continuous_linear_map.continuous₂ ContinuousLinearMap.continuous₂

/- warning: is_bounded_bilinear_map.is_bounded_linear_map_left -> IsBoundedBilinearMap.isBoundedLinearMap_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall (y : F), IsBoundedLinearMap.{u1, u2, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => f (Prod.mk.{u2, u3} E F x y)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall (y : F), IsBoundedLinearMap.{u4, u3, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) E _inst_2 _inst_3 G _inst_6 _inst_7 (fun (x : E) => f (Prod.mk.{u3, u2} E F x y)))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_bounded_linear_map_left IsBoundedBilinearMap.isBoundedLinearMap_leftₓ'. -/
theorem IsBoundedBilinearMap.isBoundedLinearMap_left (h : IsBoundedBilinearMap 𝕜 f) (y : F) :
    IsBoundedLinearMap 𝕜 fun x => f (x, y) :=
  { map_add := fun x x' => h.add_left _ _ _
    map_smul := fun c x => h.smul_left _ _ _
    bound := by
      rcases h.bound with ⟨C, C_pos, hC⟩
      refine' ⟨C * (‖y‖ + 1), mul_pos C_pos (lt_of_lt_of_le zero_lt_one (by simp)), fun x => _⟩
      have : ‖y‖ ≤ ‖y‖ + 1 := by simp [zero_le_one]
      calc
        ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖ := hC x y
        _ ≤ C * ‖x‖ * (‖y‖ + 1) := by
          apply_rules [norm_nonneg, mul_le_mul_of_nonneg_left, le_of_lt C_pos, mul_nonneg]
        _ = C * (‖y‖ + 1) * ‖x‖ := by ring
         }
#align is_bounded_bilinear_map.is_bounded_linear_map_left IsBoundedBilinearMap.isBoundedLinearMap_left

/- warning: is_bounded_bilinear_map.is_bounded_linear_map_right -> IsBoundedBilinearMap.isBoundedLinearMap_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall (x : E), IsBoundedLinearMap.{u1, u3, u4} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 (fun (y : F) => f (Prod.mk.{u2, u3} E F x y)))
but is expected to have type
  forall {𝕜 : Type.{u4}} [_inst_1 : NontriviallyNormedField.{u4} 𝕜] {E : Type.{u3}} [_inst_2 : NormedAddCommGroup.{u3} E] [_inst_3 : NormedSpace.{u4, u3} 𝕜 E (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} E _inst_2)] {F : Type.{u2}} [_inst_4 : NormedAddCommGroup.{u2} F] [_inst_5 : NormedSpace.{u4, u2} 𝕜 F (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} F _inst_4)] {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : NormedSpace.{u4, u1} 𝕜 G (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} G _inst_6)] {f : (Prod.{u3, u2} E F) -> G}, (IsBoundedBilinearMap.{u4, u3, u2, u1} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (forall (x : E), IsBoundedLinearMap.{u4, u2, u1} 𝕜 (NontriviallyNormedField.toNormedField.{u4} 𝕜 _inst_1) F _inst_4 _inst_5 G _inst_6 _inst_7 (fun (y : F) => f (Prod.mk.{u3, u2} E F x y)))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_bounded_linear_map_right IsBoundedBilinearMap.isBoundedLinearMap_rightₓ'. -/
theorem IsBoundedBilinearMap.isBoundedLinearMap_right (h : IsBoundedBilinearMap 𝕜 f) (x : E) :
    IsBoundedLinearMap 𝕜 fun y => f (x, y) :=
  { map_add := fun y y' => h.add_right _ _ _
    map_smul := fun c y => h.smul_right _ _ _
    bound := by
      rcases h.bound with ⟨C, C_pos, hC⟩
      refine' ⟨C * (‖x‖ + 1), mul_pos C_pos (lt_of_lt_of_le zero_lt_one (by simp)), fun y => _⟩
      have : ‖x‖ ≤ ‖x‖ + 1 := by simp [zero_le_one]
      calc
        ‖f (x, y)‖ ≤ C * ‖x‖ * ‖y‖ := hC x y
        _ ≤ C * (‖x‖ + 1) * ‖y‖ := by
          apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, mul_le_mul_of_nonneg_left,
            le_of_lt C_pos]
         }
#align is_bounded_bilinear_map.is_bounded_linear_map_right IsBoundedBilinearMap.isBoundedLinearMap_right

/- warning: is_bounded_bilinear_map_smul -> isBoundedBilinearMapSmul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_smul isBoundedBilinearMapSmulₓ'. -/
theorem isBoundedBilinearMapSmul {𝕜' : Type _} [NormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {E : Type _}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × E => p.1 • p.2 :=
  (lsmul 𝕜 𝕜' : 𝕜' →L[𝕜] E →L[𝕜] E).IsBoundedBilinearMap
#align is_bounded_bilinear_map_smul isBoundedBilinearMapSmul

/- warning: is_bounded_bilinear_map_mul -> isBoundedBilinearMapMul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜], IsBoundedBilinearMap.{u1, u1, u1, u1} 𝕜 _inst_1 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) (fun (p : Prod.{u1, u1} 𝕜 𝕜) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.fst.{u1, u1} 𝕜 𝕜 p) (Prod.snd.{u1, u1} 𝕜 𝕜 p))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜], IsBoundedBilinearMap.{u1, u1, u1, u1} 𝕜 _inst_1 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (NormedField.toNormedSpace.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)) (fun (p : Prod.{u1, u1} 𝕜 𝕜) => HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1)))))))) (Prod.fst.{u1, u1} 𝕜 𝕜 p) (Prod.snd.{u1, u1} 𝕜 𝕜 p))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_mul isBoundedBilinearMapMulₓ'. -/
theorem isBoundedBilinearMapMul : IsBoundedBilinearMap 𝕜 fun p : 𝕜 × 𝕜 => p.1 * p.2 := by
  simp_rw [← smul_eq_mul] <;> exact isBoundedBilinearMapSmul
#align is_bounded_bilinear_map_mul isBoundedBilinearMapMul

/- warning: is_bounded_bilinear_map_comp -> isBoundedBilinearMapComp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_comp isBoundedBilinearMapCompₓ'. -/
theorem isBoundedBilinearMapComp :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × (E →L[𝕜] F) => p.1.comp p.2 :=
  (compL 𝕜 E F G).IsBoundedBilinearMap
#align is_bounded_bilinear_map_comp isBoundedBilinearMapComp

/- warning: continuous_linear_map.is_bounded_linear_map_comp_left -> ContinuousLinearMap.isBoundedLinearMap_comp_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.is_bounded_linear_map_comp_left ContinuousLinearMap.isBoundedLinearMap_comp_leftₓ'. -/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_left (g : F →L[𝕜] G) :
    IsBoundedLinearMap 𝕜 fun f : E →L[𝕜] F => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMapComp.isBoundedLinearMap_right _
#align continuous_linear_map.is_bounded_linear_map_comp_left ContinuousLinearMap.isBoundedLinearMap_comp_left

/- warning: continuous_linear_map.is_bounded_linear_map_comp_right -> ContinuousLinearMap.isBoundedLinearMap_comp_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.is_bounded_linear_map_comp_right ContinuousLinearMap.isBoundedLinearMap_comp_rightₓ'. -/
theorem ContinuousLinearMap.isBoundedLinearMap_comp_right (f : E →L[𝕜] F) :
    IsBoundedLinearMap 𝕜 fun g : F →L[𝕜] G => ContinuousLinearMap.comp g f :=
  isBoundedBilinearMapComp.isBoundedLinearMap_left _
#align continuous_linear_map.is_bounded_linear_map_comp_right ContinuousLinearMap.isBoundedLinearMap_comp_right

/- warning: is_bounded_bilinear_map_apply -> isBoundedBilinearMapApply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_apply isBoundedBilinearMapApplyₓ'. -/
theorem isBoundedBilinearMapApply : IsBoundedBilinearMap 𝕜 fun p : (E →L[𝕜] F) × E => p.1 p.2 :=
  (ContinuousLinearMap.flip (apply 𝕜 F : E →L[𝕜] (E →L[𝕜] F) →L[𝕜] F)).IsBoundedBilinearMap
#align is_bounded_bilinear_map_apply isBoundedBilinearMapApply

/- warning: is_bounded_bilinear_map_smul_right -> isBoundedBilinearMapSmulRight is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_smul_right isBoundedBilinearMapSmulRightₓ'. -/
/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
theorem isBoundedBilinearMapSmulRight :
    IsBoundedBilinearMap 𝕜 fun p =>
      (ContinuousLinearMap.smulRight : (E →L[𝕜] 𝕜) → F → E →L[𝕜] F) p.1 p.2 :=
  (smulRightL 𝕜 E F).IsBoundedBilinearMap
#align is_bounded_bilinear_map_smul_right isBoundedBilinearMapSmulRight

/- warning: is_bounded_bilinear_map_comp_multilinear -> isBoundedBilinearMapCompMultilinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_comp_multilinear isBoundedBilinearMapCompMultilinearₓ'. -/
/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
theorem isBoundedBilinearMapCompMultilinear {ι : Type _} {E : ι → Type _} [Fintype ι]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] :
    IsBoundedBilinearMap 𝕜 fun p : (F →L[𝕜] G) × ContinuousMultilinearMap 𝕜 E F =>
      p.1.compContinuousMultilinearMap p.2 :=
  (compContinuousMultilinearMapL 𝕜 E F G).IsBoundedBilinearMap
#align is_bounded_bilinear_map_comp_multilinear isBoundedBilinearMapCompMultilinear

/- warning: is_bounded_bilinear_map.linear_deriv -> IsBoundedBilinearMap.linearDeriv is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Prod.{u2, u3} E F) -> (LinearMap.{u1, u1, max u2 u3, u4} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u2, u3} E F) G (Prod.addCommMonoid.{u2, u3} E F (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4))) (AddCommGroup.toAddCommMonoid.{u4} G (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6)) (Prod.module.{u1, u2, u3} 𝕜 E F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7))
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : NontriviallyNormedField.{u1} 𝕜] {E : Type.{u2}} [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : NormedSpace.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)] {F : Type.{u3}} [_inst_4 : NormedAddCommGroup.{u3} F] [_inst_5 : NormedSpace.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4)] {G : Type.{u4}} [_inst_6 : NormedAddCommGroup.{u4} G] [_inst_7 : NormedSpace.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6)] {f : (Prod.{u2, u3} E F) -> G}, (IsBoundedBilinearMap.{u1, u2, u3, u4} 𝕜 _inst_1 E _inst_2 _inst_3 F _inst_4 _inst_5 G _inst_6 _inst_7 f) -> (Prod.{u2, u3} E F) -> (LinearMap.{u1, u1, max u3 u2, u4} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))))) (Prod.{u2, u3} E F) G (Prod.instAddCommMonoidSum.{u2, u3} E F (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4))) (AddCommGroup.toAddCommMonoid.{u4} G (NormedAddCommGroup.toAddCommGroup.{u4} G _inst_6)) (Prod.module.{u1, u2, u3} 𝕜 E F (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (AddCommGroup.toAddCommMonoid.{u3} F (NormedAddCommGroup.toAddCommGroup.{u3} F _inst_4)) (NormedSpace.toModule.{u1, u2} 𝕜 E (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) _inst_3) (NormedSpace.toModule.{u1, u3} 𝕜 F (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} F _inst_4) _inst_5)) (NormedSpace.toModule.{u1, u4} 𝕜 G (NontriviallyNormedField.toNormedField.{u1} 𝕜 _inst_1) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} G _inst_6) _inst_7))
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.linear_deriv IsBoundedBilinearMap.linearDerivₓ'. -/
/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `is_bounded_bilinear_map.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
``. -/
def IsBoundedBilinearMap.linearDeriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →ₗ[𝕜] G
    where
  toFun q := f (p.1, q.2) + f (q.1, p.2)
  map_add' q₁ q₂ :=
    by
    change
      f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) =
        f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2))
    simp [h.add_left, h.add_right]; abel
  map_smul' c q :=
    by
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2))
    simp [h.smul_left, h.smul_right, smul_add]
#align is_bounded_bilinear_map.linear_deriv IsBoundedBilinearMap.linearDeriv

/- warning: is_bounded_bilinear_map.deriv -> IsBoundedBilinearMap.deriv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.deriv IsBoundedBilinearMap.derivₓ'. -/
/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`is_bounded_bilinear_map.has_fderiv_at` in `analysis.calculus.fderiv`. -/
def IsBoundedBilinearMap.deriv (h : IsBoundedBilinearMap 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
  (h.linearDeriv p).mkContinuousOfExistsBound <|
    by
    rcases h.bound with ⟨C, Cpos, hC⟩
    refine' ⟨C * ‖p.1‖ + C * ‖p.2‖, fun q => _⟩
    calc
      ‖f (p.1, q.2) + f (q.1, p.2)‖ ≤ C * ‖p.1‖ * ‖q.2‖ + C * ‖q.1‖ * ‖p.2‖ :=
        norm_add_le_of_le (hC _ _) (hC _ _)
      _ ≤ C * ‖p.1‖ * ‖q‖ + C * ‖q‖ * ‖p.2‖ :=
        by
        apply add_le_add
        exact
          mul_le_mul_of_nonneg_left (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _))
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos)
      _ = (C * ‖p.1‖ + C * ‖p.2‖) * ‖q‖ := by ring
      
#align is_bounded_bilinear_map.deriv IsBoundedBilinearMap.deriv

/- warning: is_bounded_bilinear_map_deriv_coe -> IsBoundedBilinearMap.deriv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map_deriv_coe IsBoundedBilinearMap.deriv_applyₓ'. -/
@[simp]
theorem IsBoundedBilinearMap.deriv_apply (h : IsBoundedBilinearMap 𝕜 f) (p q : E × F) :
    h.deriv p q = f (p.1, q.2) + f (q.1, p.2) :=
  rfl
#align is_bounded_bilinear_map_deriv_coe IsBoundedBilinearMap.deriv_apply

variable (𝕜)

/- warning: continuous_linear_map.mul_left_right_is_bounded_bilinear -> ContinuousLinearMap.mulLeftRightIsBoundedBilinear is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.mul_left_right_is_bounded_bilinear ContinuousLinearMap.mulLeftRightIsBoundedBilinearₓ'. -/
/-- The function `continuous_linear_map.mul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded
bilinear map. -/
theorem ContinuousLinearMap.mulLeftRightIsBoundedBilinear (𝕜' : Type _) [NormedRing 𝕜']
    [NormedAlgebra 𝕜 𝕜'] :
    IsBoundedBilinearMap 𝕜 fun p : 𝕜' × 𝕜' => ContinuousLinearMap.mulLeftRight 𝕜 𝕜' p.1 p.2 :=
  (ContinuousLinearMap.mulLeftRight 𝕜 𝕜').IsBoundedBilinearMap
#align continuous_linear_map.mul_left_right_is_bounded_bilinear ContinuousLinearMap.mulLeftRightIsBoundedBilinear

variable {𝕜}

/- warning: is_bounded_bilinear_map.is_bounded_linear_map_deriv -> IsBoundedBilinearMap.isBoundedLinearMap_deriv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_bounded_bilinear_map.is_bounded_linear_map_deriv IsBoundedBilinearMap.isBoundedLinearMap_derivₓ'. -/
/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
theorem IsBoundedBilinearMap.isBoundedLinearMap_deriv (h : IsBoundedBilinearMap 𝕜 f) :
    IsBoundedLinearMap 𝕜 fun p : E × F => h.deriv p :=
  by
  rcases h.bound with ⟨C, Cpos : 0 < C, hC⟩
  refine' IsLinearMap.with_bound ⟨fun p₁ p₂ => _, fun c p => _⟩ (C + C) fun p => _
  ·
    ext <;>
        simp only [h.add_left, h.add_right, coe_comp', Function.comp_apply, inl_apply,
          IsBoundedBilinearMap.deriv_apply, Prod.fst_add, Prod.snd_add, add_apply] <;>
      abel
  ·
    ext <;>
      simp only [h.smul_left, h.smul_right, smul_add, coe_comp', Function.comp_apply,
        IsBoundedBilinearMap.deriv_apply, Prod.smul_fst, Prod.smul_snd, coe_smul', Pi.smul_apply]
  · refine'
      ContinuousLinearMap.op_norm_le_bound _
        (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) fun q => _
    calc
      ‖f (p.1, q.2) + f (q.1, p.2)‖ ≤ C * ‖p.1‖ * ‖q.2‖ + C * ‖q.1‖ * ‖p.2‖ :=
        norm_add_le_of_le (hC _ _) (hC _ _)
      _ ≤ C * ‖p‖ * ‖q‖ + C * ‖q‖ * ‖p‖ := by
        apply_rules [add_le_add, mul_le_mul, norm_nonneg, Cpos.le, le_refl, le_max_left,
          le_max_right, mul_nonneg]
      _ = (C + C) * ‖p‖ * ‖q‖ := by ring
      
#align is_bounded_bilinear_map.is_bounded_linear_map_deriv IsBoundedBilinearMap.isBoundedLinearMap_deriv

end BilinearMap

/- warning: continuous.clm_comp -> Continuous.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous.clm_comp Continuous.clm_compₓ'. -/
theorem Continuous.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    (hg : Continuous g) (hf : Continuous f) : Continuous fun x => (g x).comp (f x) :=
  (compL 𝕜 E F G).continuous₂.comp₂ hg hf
#align continuous.clm_comp Continuous.clm_comp

/- warning: continuous_on.clm_comp -> ContinuousOn.clm_comp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_on.clm_comp ContinuousOn.clm_compₓ'. -/
theorem ContinuousOn.clm_comp {X} [TopologicalSpace X] {g : X → F →L[𝕜] G} {f : X → E →L[𝕜] F}
    {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (g x).comp (f x)) s :=
  (compL 𝕜 E F G).continuous₂.comp_continuousOn (hg.Prod hf)
#align continuous_on.clm_comp ContinuousOn.clm_comp

namespace ContinuousLinearEquiv

open Set

/-!
### The set of continuous linear equivalences between two Banach spaces is open

In this section we establish that the set of continuous linear equivalences between two Banach
spaces is an open subset of the space of linear maps between them.
-/


/- warning: continuous_linear_equiv.is_open -> ContinuousLinearEquiv.isOpen is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.is_open ContinuousLinearEquiv.isOpenₓ'. -/
protected theorem isOpen [CompleteSpace E] : IsOpen (range (coe : (E ≃L[𝕜] F) → E →L[𝕜] F)) :=
  by
  rw [isOpen_iff_mem_nhds, forall_range_iff]
  refine' fun e => IsOpen.mem_nhds _ (mem_range_self _)
  let O : (E →L[𝕜] F) → E →L[𝕜] E := fun f => (e.symm : F →L[𝕜] E).comp f
  have h_O : Continuous O := is_bounded_bilinear_map_comp.continuous_right
  convert show IsOpen (O ⁻¹' { x | IsUnit x }) from units.is_open.preimage h_O using 1
  ext f'
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨(e'.trans e.symm).toUnit, rfl⟩
  · rintro ⟨w, hw⟩
    use (units_equiv 𝕜 E w).trans e
    ext x
    simp [coeFn_coe_base' w, hw]
#align continuous_linear_equiv.is_open ContinuousLinearEquiv.isOpen

/- warning: continuous_linear_equiv.nhds -> ContinuousLinearEquiv.nhds is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.nhds ContinuousLinearEquiv.nhdsₓ'. -/
protected theorem nhds [CompleteSpace E] (e : E ≃L[𝕜] F) :
    range (coe : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (e : E →L[𝕜] F) :=
  IsOpen.mem_nhds ContinuousLinearEquiv.isOpen (by simp)
#align continuous_linear_equiv.nhds ContinuousLinearEquiv.nhds

end ContinuousLinearEquiv

