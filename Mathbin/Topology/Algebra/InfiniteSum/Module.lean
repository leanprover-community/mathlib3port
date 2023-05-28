/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis

! This file was ported from Lean 3 source module topology.algebra.infinite_sum.module
! leanprover-community/mathlib commit 75be6b616681ab6ca66d798ead117e75cd64f125
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.InfiniteSum.Basic
import Mathbin.Topology.Algebra.Module.Basic

/-! # Infinite sums in topological vector spaces 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


variable {ι R R₂ M M₂ : Type _}

section SmulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι → R}

/- warning: has_sum.smul_const -> HasSum.smul_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : TopologicalSpace.{u3} M] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u2, u3} R M _inst_1 _inst_4] [_inst_6 : ContinuousSMul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_4 _inst_5)))) _inst_2 _inst_3] {f : ι -> R} {r : R}, (HasSum.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_2 f r) -> (forall (a : M), HasSum.{u3, u1} M ι _inst_4 _inst_3 (fun (z : ι) => SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_4 _inst_5)))) (f z) a) (SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_4 _inst_5)))) r a))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : AddCommMonoid.{u1} M] [_inst_5 : Module.{u3, u1} R M _inst_1 _inst_4] [_inst_6 : ContinuousSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_4 _inst_5)))) _inst_2 _inst_3] {f : ι -> R} {r : R}, (HasSum.{u3, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_2 f r) -> (forall (a : M), HasSum.{u1, u2} M ι _inst_4 _inst_3 (fun (z : ι) => HSMul.hSMul.{u3, u1, u1} R M M (instHSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_4 _inst_5))))) (f z) a) (HSMul.hSMul.{u3, u1, u1} R M M (instHSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_4 _inst_5))))) r a))
Case conversion may be inaccurate. Consider using '#align has_sum.smul_const HasSum.smul_constₓ'. -/
theorem HasSum.smul_const {r : R} (hf : HasSum f r) (a : M) : HasSum (fun z => f z • a) (r • a) :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)
#align has_sum.smul_const HasSum.smul_const

/- warning: summable.smul_const -> Summable.smul_const is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} {M : Type.{u3}} [_inst_1 : Semiring.{u2} R] [_inst_2 : TopologicalSpace.{u2} R] [_inst_3 : TopologicalSpace.{u3} M] [_inst_4 : AddCommMonoid.{u3} M] [_inst_5 : Module.{u2, u3} R M _inst_1 _inst_4] [_inst_6 : ContinuousSMul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_4 _inst_5)))) _inst_2 _inst_3] {f : ι -> R}, (Summable.{u2, u1} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_1))) _inst_2 f) -> (forall (a : M), Summable.{u3, u1} M ι _inst_4 _inst_3 (fun (z : ι) => SMul.smul.{u2, u3} R M (SMulZeroClass.toHasSmul.{u2, u3} R M (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (SMulWithZero.toSmulZeroClass.{u2, u3} R M (MulZeroClass.toHasZero.{u2} R (MulZeroOneClass.toMulZeroClass.{u2} R (MonoidWithZero.toMulZeroOneClass.{u2} R (Semiring.toMonoidWithZero.{u2} R _inst_1)))) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (MulActionWithZero.toSMulWithZero.{u2, u3} R M (Semiring.toMonoidWithZero.{u2} R _inst_1) (AddZeroClass.toHasZero.{u3} M (AddMonoid.toAddZeroClass.{u3} M (AddCommMonoid.toAddMonoid.{u3} M _inst_4))) (Module.toMulActionWithZero.{u2, u3} R M _inst_1 _inst_4 _inst_5)))) (f z) a))
but is expected to have type
  forall {ι : Type.{u2}} {R : Type.{u3}} {M : Type.{u1}} [_inst_1 : Semiring.{u3} R] [_inst_2 : TopologicalSpace.{u3} R] [_inst_3 : TopologicalSpace.{u1} M] [_inst_4 : AddCommMonoid.{u1} M] [_inst_5 : Module.{u3, u1} R M _inst_1 _inst_4] [_inst_6 : ContinuousSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_4 _inst_5)))) _inst_2 _inst_3] {f : ι -> R}, (Summable.{u3, u2} R ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_1))) _inst_2 f) -> (forall (a : M), Summable.{u1, u2} M ι _inst_4 _inst_3 (fun (z : ι) => HSMul.hSMul.{u3, u1, u1} R M M (instHSMul.{u3, u1} R M (SMulZeroClass.toSMul.{u3, u1} R M (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (SMulWithZero.toSMulZeroClass.{u3, u1} R M (MonoidWithZero.toZero.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_1)) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (MulActionWithZero.toSMulWithZero.{u3, u1} R M (Semiring.toMonoidWithZero.{u3} R _inst_1) (AddMonoid.toZero.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_4)) (Module.toMulActionWithZero.{u3, u1} R M _inst_1 _inst_4 _inst_5))))) (f z) a))
Case conversion may be inaccurate. Consider using '#align summable.smul_const Summable.smul_constₓ'. -/
theorem Summable.smul_const (hf : Summable f) (a : M) : Summable fun z => f z • a :=
  (hf.HasSum.smul_const _).Summable
#align summable.smul_const Summable.smul_const

#print tsum_smul_const /-
theorem tsum_smul_const [T2Space M] (hf : Summable f) (a : M) : (∑' z, f z • a) = (∑' z, f z) • a :=
  (hf.HasSum.smul_const _).tsum_eq
#align tsum_smul_const tsum_smul_const
-/

end SmulConst

section HasSum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂} {σ' : R₂ →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ]

/- warning: continuous_linear_map.has_sum -> ContinuousLinearMap.hasSum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.has_sum ContinuousLinearMap.hasSumₓ'. -/
/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearMap.hasSum {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
    (hf : HasSum f x) : HasSum (fun b : ι => φ (f b)) (φ x) := by
  simpa only using hf.map φ.to_linear_map.to_add_monoid_hom φ.continuous
#align continuous_linear_map.has_sum ContinuousLinearMap.hasSum

/- warning: has_sum.mapL -> HasSum.mapL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align has_sum.mapL HasSum.mapLₓ'. -/
alias ContinuousLinearMap.hasSum ← HasSum.mapL
#align has_sum.mapL HasSum.mapL

/- warning: continuous_linear_map.summable -> ContinuousLinearMap.summable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.summable ContinuousLinearMap.summableₓ'. -/
protected theorem ContinuousLinearMap.summable {f : ι → M} (φ : M →SL[σ] M₂) (hf : Summable f) :
    Summable fun b : ι => φ (f b) :=
  (hf.HasSum.mapL φ).Summable
#align continuous_linear_map.summable ContinuousLinearMap.summable

/- warning: summable.mapL -> Summable.mapL is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align summable.mapL Summable.mapLₓ'. -/
alias ContinuousLinearMap.summable ← Summable.mapL
#align summable.mapL Summable.mapL

/- warning: continuous_linear_map.map_tsum -> ContinuousLinearMap.map_tsum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.map_tsum ContinuousLinearMap.map_tsumₓ'. -/
protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] {f : ι → M} (φ : M →SL[σ] M₂)
    (hf : Summable f) : φ (∑' z, f z) = ∑' z, φ (f z) :=
  (hf.HasSum.mapL φ).tsum_eq.symm
#align continuous_linear_map.map_tsum ContinuousLinearMap.map_tsum

include σ'

/- warning: continuous_linear_equiv.has_sum -> ContinuousLinearEquiv.hasSum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.has_sum ContinuousLinearEquiv.hasSumₓ'. -/
/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSum {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSum (fun b : ι => e (f b)) y ↔ HasSum f (e.symm y) :=
  ⟨fun h => by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
    fun h => by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).HasSum h⟩
#align continuous_linear_equiv.has_sum ContinuousLinearEquiv.hasSum

/- warning: continuous_linear_equiv.has_sum' -> ContinuousLinearEquiv.hasSum' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.has_sum' ContinuousLinearEquiv.hasSum'ₓ'. -/
/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
protected theorem ContinuousLinearEquiv.hasSum' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSum (fun b : ι => e (f b)) (e x) ↔ HasSum f x := by
  rw [e.has_sum, ContinuousLinearEquiv.symm_apply_apply]
#align continuous_linear_equiv.has_sum' ContinuousLinearEquiv.hasSum'

/- warning: continuous_linear_equiv.summable -> ContinuousLinearEquiv.summable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.summable ContinuousLinearEquiv.summableₓ'. -/
protected theorem ContinuousLinearEquiv.summable {f : ι → M} (e : M ≃SL[σ] M₂) :
    (Summable fun b : ι => e (f b)) ↔ Summable f :=
  ⟨fun hf => (e.HasSum.1 hf.HasSum).Summable, (e : M →SL[σ] M₂).Summable⟩
#align continuous_linear_equiv.summable ContinuousLinearEquiv.summable

/- warning: continuous_linear_equiv.tsum_eq_iff -> ContinuousLinearEquiv.tsum_eq_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.tsum_eq_iff ContinuousLinearEquiv.tsum_eq_iffₓ'. -/
theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂] {f : ι → M} (e : M ≃SL[σ] M₂)
    {y : M₂} : (∑' z, e (f z)) = y ↔ (∑' z, f z) = e.symm y :=
  by
  by_cases hf : Summable f
  ·
    exact
      ⟨fun h => (e.has_sum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h =>
        (e.has_sum.mpr (hf.has_sum_iff.mpr h)).tsum_eq⟩
  · have hf' : ¬Summable fun z => e (f z) := fun h => hf (e.summable.mp h)
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf']
    exact
      ⟨by
        rintro rfl
        simp, fun H => by simpa using congr_arg (fun z => e z) H⟩
#align continuous_linear_equiv.tsum_eq_iff ContinuousLinearEquiv.tsum_eq_iff

/- warning: continuous_linear_equiv.map_tsum -> ContinuousLinearEquiv.map_tsum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_equiv.map_tsum ContinuousLinearEquiv.map_tsumₓ'. -/
protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂] {f : ι → M}
    (e : M ≃SL[σ] M₂) : e (∑' z, f z) = ∑' z, e (f z) :=
  by
  refine' symm (e.tsum_eq_iff.mpr _)
  rw [e.symm_apply_apply _]
#align continuous_linear_equiv.map_tsum ContinuousLinearEquiv.map_tsum

end HasSum

