/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module geometry.euclidean.sphere.second_inter
! leanprover-community/mathlib commit 46b633fd842bef9469441c0209906f6dddd2b4f5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Geometry.Euclidean.Sphere.Basic

/-!
# Second intersection of a sphere and a line

This file defines and proves basic results about the second intersection of a sphere with a line
through a point on that sphere.

## Main definitions

* `euclidean_geometry.sphere.second_inter` is the second intersection of a sphere with a line
  through a point on that sphere.

-/


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type _} {P : Type _} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

include V

#print EuclideanGeometry.Sphere.secondInter /-
/-- The second intersection of a sphere with a line through a point on that sphere; that point
if it is the only point of intersection of the line with the sphere. The intended use of this
definition is when `p ∈ s`; the definition does not use `s.radius`, so in general it returns
the second intersection with the sphere through `p` and with center `s.center`. -/
def Sphere.secondInter (s : Sphere P) (p : P) (v : V) : P :=
  (-2 * ⟪v, p -ᵥ s.center⟫ / ⟪v, v⟫) • v +ᵥ p
#align euclidean_geometry.sphere.second_inter EuclideanGeometry.Sphere.secondInter
-/

#print EuclideanGeometry.Sphere.secondInter_dist /-
/-- The distance between `second_inter` and the center equals the distance between the original
point and the center. -/
@[simp]
theorem Sphere.secondInter_dist (s : Sphere P) (p : P) (v : V) :
    dist (s.secondInter p v) s.center = dist p s.center :=
  by
  rw [sphere.second_inter]
  by_cases hv : v = 0; · simp [hv]
  rw [dist_smul_vadd_eq_dist _ _ hv]
  exact Or.inr rfl
#align euclidean_geometry.sphere.second_inter_dist EuclideanGeometry.Sphere.secondInter_dist
-/

#print EuclideanGeometry.Sphere.secondInter_mem /-
/-- The point given by `second_inter` lies on the sphere. -/
@[simp]
theorem Sphere.secondInter_mem {s : Sphere P} {p : P} (v : V) : s.secondInter p v ∈ s ↔ p ∈ s := by
  simp_rw [mem_sphere, sphere.second_inter_dist]
#align euclidean_geometry.sphere.second_inter_mem EuclideanGeometry.Sphere.secondInter_mem
-/

variable (V)

/- warning: euclidean_geometry.sphere.second_inter_zero -> EuclideanGeometry.Sphere.secondInter_zero is a dubious translation:
lean 3 declaration is
  forall (V : Type.{u1}) {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (OfNat.ofNat.{u1} V 0 (OfNat.mk.{u1} V 0 (Zero.zero.{u1} V (AddZeroClass.toHasZero.{u1} V (AddMonoid.toAddZeroClass.{u1} V (SubNegMonoid.toAddMonoid.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))))))))) p
but is expected to have type
  forall (V : Type.{u1}) {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (OfNat.ofNat.{u1} V 0 (Zero.toOfNat0.{u1} V (NegZeroClass.toZero.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1))))))))) p
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.second_inter_zero EuclideanGeometry.Sphere.secondInter_zeroₓ'. -/
/-- If the vector is zero, `second_inter` gives the original point. -/
@[simp]
theorem Sphere.secondInter_zero (s : Sphere P) (p : P) : s.secondInter p (0 : V) = p := by
  simp [sphere.second_inter]
#align euclidean_geometry.sphere.second_inter_zero EuclideanGeometry.Sphere.secondInter_zero

variable {V}

/- warning: euclidean_geometry.sphere.second_inter_eq_self_iff -> EuclideanGeometry.Sphere.secondInter_eq_self_iff is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {v : V}, Iff (Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p v) p) (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) v (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {v : V}, Iff (Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p v) p) (Eq.{1} Real (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) v (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.second_inter_eq_self_iff EuclideanGeometry.Sphere.secondInter_eq_self_iffₓ'. -/
/-- The point given by `second_inter` equals the original point if and only if the line is
orthogonal to the radius vector. -/
theorem Sphere.secondInter_eq_self_iff {s : Sphere P} {p : P} {v : V} :
    s.secondInter p v = p ↔ ⟪v, p -ᵥ s.center⟫ = 0 :=
  by
  refine' ⟨fun hp => _, fun hp => _⟩
  · by_cases hv : v = 0
    · simp [hv]
    rwa [sphere.second_inter, eq_comm, eq_vadd_iff_vsub_eq, vsub_self, eq_comm, smul_eq_zero,
      or_iff_left hv, div_eq_zero_iff, inner_self_eq_zero, or_iff_left hv, mul_eq_zero,
      or_iff_right (by norm_num : (-2 : ℝ) ≠ 0)] at hp
  · rw [sphere.second_inter, hp, MulZeroClass.mul_zero, zero_div, zero_smul, zero_vadd]
#align euclidean_geometry.sphere.second_inter_eq_self_iff EuclideanGeometry.Sphere.secondInter_eq_self_iff

#print EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem /-
/-- A point on a line through a point on a sphere equals that point or `second_inter`. -/
theorem Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem {s : Sphere P} {p : P}
    (hp : p ∈ s) {v : V} {p' : P} (hp' : p' ∈ AffineSubspace.mk' p (ℝ ∙ v)) :
    p' = p ∨ p' = s.secondInter p v ↔ p' ∈ s :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rcases h with (h | h)
    · rwa [h]
    · rwa [h, sphere.second_inter_mem]
  · rw [AffineSubspace.mem_mk'_iff_vsub_mem, Submodule.mem_span_singleton] at hp'
    rcases hp' with ⟨r, hr⟩
    rw [eq_comm, ← eq_vadd_iff_vsub_eq] at hr
    subst hr
    by_cases hv : v = 0
    · simp [hv]
    rw [sphere.second_inter]
    rw [mem_sphere] at h hp
    rw [← hp, dist_smul_vadd_eq_dist _ _ hv] at h
    rcases h with (h | h) <;> simp [h]
#align euclidean_geometry.sphere.eq_or_eq_second_inter_of_mem_mk'_span_singleton_iff_mem EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem
-/

/- warning: euclidean_geometry.sphere.second_inter_smul -> EuclideanGeometry.Sphere.secondInter_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.second_inter_smul EuclideanGeometry.Sphere.secondInter_smulₓ'. -/
/-- `second_inter` is unchanged by multiplying the vector by a nonzero real. -/
@[simp]
theorem Sphere.secondInter_smul (s : Sphere P) (p : P) (v : V) {r : ℝ} (hr : r ≠ 0) :
    s.secondInter p (r • v) = s.secondInter p v :=
  by
  simp_rw [sphere.second_inter, real_inner_smul_left, inner_smul_right, smul_smul,
    div_mul_eq_div_div]
  rw [mul_comm, ← mul_div_assoc, ← mul_div_assoc, mul_div_cancel_left _ hr, mul_comm, mul_assoc,
    mul_div_cancel_left _ hr, mul_comm]
#align euclidean_geometry.sphere.second_inter_smul EuclideanGeometry.Sphere.secondInter_smul

/- warning: euclidean_geometry.sphere.second_inter_neg -> EuclideanGeometry.Sphere.secondInter_neg is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P) (v : V), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (Neg.neg.{u1} V (SubNegMonoid.toHasNeg.{u1} V (AddGroup.toSubNegMonoid.{u1} V (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)))) v)) (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p v)
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P) (v : V), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (Neg.neg.{u1} V (NegZeroClass.toNeg.{u1} V (SubNegZeroMonoid.toNegZeroClass.{u1} V (SubtractionMonoid.toSubNegZeroMonoid.{u1} V (SubtractionCommMonoid.toSubtractionMonoid.{u1} V (AddCommGroup.toDivisionAddCommMonoid.{u1} V (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1)))))) v)) (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p v)
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.second_inter_neg EuclideanGeometry.Sphere.secondInter_negₓ'. -/
/-- `second_inter` is unchanged by negating the vector. -/
@[simp]
theorem Sphere.secondInter_neg (s : Sphere P) (p : P) (v : V) :
    s.secondInter p (-v) = s.secondInter p v := by
  rw [← neg_one_smul ℝ v, s.second_inter_smul p v (by norm_num : (-1 : ℝ) ≠ 0)]
#align euclidean_geometry.sphere.second_inter_neg EuclideanGeometry.Sphere.secondInter_neg

#print EuclideanGeometry.Sphere.secondInter_secondInter /-
/-- Applying `second_inter` twice returns the original point. -/
@[simp]
theorem Sphere.secondInter_secondInter (s : Sphere P) (p : P) (v : V) :
    s.secondInter (s.secondInter p v) v = p :=
  by
  by_cases hv : v = 0; · simp [hv]
  have hv' : ⟪v, v⟫ ≠ 0 := inner_self_ne_zero.2 hv
  simp only [sphere.second_inter, vadd_vsub_assoc, vadd_vadd, inner_add_right, inner_smul_right,
    div_mul_cancel _ hv']
  rw [← @vsub_eq_zero_iff_eq V, vadd_vsub, ← add_smul, ← add_div]
  convert zero_smul ℝ _
  convert zero_div _
  ring
#align euclidean_geometry.sphere.second_inter_second_inter EuclideanGeometry.Sphere.secondInter_secondInter
-/

/- warning: euclidean_geometry.sphere.second_inter_eq_line_map -> EuclideanGeometry.Sphere.secondInter_eq_lineMap is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P) (p' : P), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p)) (coeFn.{max 1 (succ u1) (succ u2), succ u2} (AffineMap.{0, 0, 0, u1, u2} Real Real Real V P Real.ring (NonUnitalNonAssocRing.toAddCommGroup.{0} Real (NonAssocRing.toNonUnitalNonAssocRing.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (Semiring.toModule.{0} Real (Ring.toSemiring.{0} Real Real.ring)) (addGroupIsAddTorsor.{0} Real (AddGroupWithOne.toAddGroup.{0} Real (AddCommGroupWithOne.toAddGroupWithOne.{0} Real (Ring.toAddCommGroupWithOne.{0} Real Real.ring)))) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (fun (_x : AffineMap.{0, 0, 0, u1, u2} Real Real Real V P Real.ring (NonUnitalNonAssocRing.toAddCommGroup.{0} Real (NonAssocRing.toNonUnitalNonAssocRing.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (Semiring.toModule.{0} Real (Ring.toSemiring.{0} Real Real.ring)) (addGroupIsAddTorsor.{0} Real (AddGroupWithOne.toAddGroup.{0} Real (AddCommGroupWithOne.toAddGroupWithOne.{0} Real (Ring.toAddCommGroupWithOne.{0} Real Real.ring)))) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) => Real -> P) (AffineMap.hasCoeToFun.{0, 0, 0, u1, u2} Real Real Real V P Real.ring (NonUnitalNonAssocRing.toAddCommGroup.{0} Real (NonAssocRing.toNonUnitalNonAssocRing.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (Semiring.toModule.{0} Real (Ring.toSemiring.{0} Real Real.ring)) (addGroupIsAddTorsor.{0} Real (AddGroupWithOne.toAddGroup.{0} Real (AddCommGroupWithOne.toAddGroupWithOne.{0} Real (Ring.toAddCommGroupWithOne.{0} Real Real.ring)))) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) (AffineMap.lineMap.{0, u1, u2} Real V P Real.ring (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p p') (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toHasInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p) (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p))))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] (s : EuclideanGeometry.Sphere.{u2} P _inst_3) (p : P) (p' : P), Eq.{succ u2} P (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p)) (FunLike.coe.{max (succ u1) (succ u2), 1, succ u2} (AffineMap.{0, 0, 0, u1, u2} Real Real Real V P Real.instRingReal (Ring.toAddCommGroup.{0} Real Real.instRingReal) (Semiring.toModule.{0} Real (Ring.toSemiring.{0} Real Real.instRingReal)) (addGroupIsAddTorsor.{0} Real (AddGroupWithOne.toAddGroup.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) Real (fun (_x : Real) => (fun (a._@.Mathlib.LinearAlgebra.AffineSpace.AffineMap._hyg.1003 : Real) => P) _x) (AffineMap.funLike.{0, 0, 0, u1, u2} Real Real Real V P Real.instRingReal (Ring.toAddCommGroup.{0} Real Real.instRingReal) (Semiring.toModule.{0} Real (Ring.toSemiring.{0} Real Real.instRingReal)) (addGroupIsAddTorsor.{0} Real (AddGroupWithOne.toAddGroup.{0} Real (Ring.toAddGroupWithOne.{0} Real Real.instRingReal))) (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) (AffineMap.lineMap.{0, u1, u2} Real V P Real.instRingReal (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4) p p') (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p) (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)))) (Inner.inner.{0, u1} Real V (InnerProductSpace.toInner.{0, u1} Real V Real.isROrC _inst_1 _inst_2) (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p) (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p))))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.second_inter_eq_line_map EuclideanGeometry.Sphere.secondInter_eq_lineMapₓ'. -/
/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the result of `second_inter` may be expressed using `line_map`. -/
theorem Sphere.secondInter_eq_lineMap (s : Sphere P) (p p' : P) :
    s.secondInter p (p' -ᵥ p) =
      AffineMap.lineMap p p' (-2 * ⟪p' -ᵥ p, p -ᵥ s.center⟫ / ⟪p' -ᵥ p, p' -ᵥ p⟫) :=
  rfl
#align euclidean_geometry.sphere.second_inter_eq_line_map EuclideanGeometry.Sphere.secondInter_eq_lineMap

#print EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan /-
/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the result lies in the span of the two points. -/
theorem Sphere.secondInter_vsub_mem_affineSpan (s : Sphere P) (p₁ p₂ : P) :
    s.secondInter p₁ (p₂ -ᵥ p₁) ∈ line[ℝ, p₁, p₂] :=
  smul_vsub_vadd_mem_affineSpan_pair _ _ _
#align euclidean_geometry.sphere.second_inter_vsub_mem_affine_span EuclideanGeometry.Sphere.secondInter_vsub_mem_affineSpan
-/

#print EuclideanGeometry.Sphere.secondInter_collinear /-
/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, the three points are collinear. -/
theorem Sphere.secondInter_collinear (s : Sphere P) (p p' : P) :
    Collinear ℝ ({p, p', s.secondInter p (p' -ᵥ p)} : Set P) :=
  by
  rw [Set.pair_comm, Set.insert_comm]
  exact
    (collinear_insert_iff_of_mem_affineSpan (s.second_inter_vsub_mem_affine_span _ _)).2
      (collinear_pair ℝ _ _)
#align euclidean_geometry.sphere.second_inter_collinear EuclideanGeometry.Sphere.secondInter_collinear
-/

/- warning: euclidean_geometry.sphere.wbtw_second_inter -> EuclideanGeometry.Sphere.wbtw_secondInter is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {p' : P}, (Membership.Mem.{u2, u2} P (EuclideanGeometry.Sphere.{u2} P _inst_3) (EuclideanGeometry.Sphere.hasMem.{u2} P _inst_3) p s) -> (LE.le.{0} Real Real.hasLe (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p' (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)) (EuclideanGeometry.Sphere.radius.{u2} P _inst_3 s)) -> (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p p' (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p)))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {p' : P}, (Membership.mem.{u2, u2} P (EuclideanGeometry.Sphere.{u2} P _inst_3) (EuclideanGeometry.instMembershipSphere.{u2} P _inst_3) p s) -> (LE.le.{0} Real Real.instLEReal (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p' (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)) (EuclideanGeometry.Sphere.radius.{u2} P _inst_3 s)) -> (Wbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4) p p' (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.wbtw_second_inter EuclideanGeometry.Sphere.wbtw_secondInterₓ'. -/
/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, and the second point is not outside the sphere, the second point is weakly
between the first point and the result of `second_inter`. -/
theorem Sphere.wbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center ≤ s.radius) : Wbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) :=
  by
  by_cases h : p' = p; · simp [h]
  refine'
    wbtw_of_collinear_of_dist_center_le_radius (s.second_inter_collinear p p') hp hp'
      ((sphere.second_inter_mem _).2 hp) _
  intro he
  rw [eq_comm, sphere.second_inter_eq_self_iff, ← neg_neg (p' -ᵥ p), inner_neg_left,
    neg_vsub_eq_vsub_rev, neg_eq_zero, eq_comm] at he
  exact ((inner_pos_or_eq_of_dist_le_radius hp hp').resolve_right (Ne.symm h)).Ne he
#align euclidean_geometry.sphere.wbtw_second_inter EuclideanGeometry.Sphere.wbtw_secondInter

/- warning: euclidean_geometry.sphere.sbtw_second_inter -> EuclideanGeometry.Sphere.sbtw_secondInter is a dubious translation:
lean 3 declaration is
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {p' : P}, (Membership.Mem.{u2, u2} P (EuclideanGeometry.Sphere.{u2} P _inst_3) (EuclideanGeometry.Sphere.hasMem.{u2} P _inst_3) p s) -> (LT.lt.{0} Real Real.hasLt (Dist.dist.{u2} P (PseudoMetricSpace.toHasDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p' (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)) (EuclideanGeometry.Sphere.radius.{u2} P _inst_3 s)) -> (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4) p p' (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toHasVsub.{u1, u2} V P (NormedAddGroup.toAddGroup.{u1} V (NormedAddCommGroup.toNormedAddGroup.{u1} V _inst_1)) (NormedAddTorsor.toAddTorsor'.{u1, u2} V P _inst_1 _inst_3 _inst_4)) p' p)))
but is expected to have type
  forall {V : Type.{u1}} {P : Type.{u2}} [_inst_1 : NormedAddCommGroup.{u1} V] [_inst_2 : InnerProductSpace.{0, u1} Real V Real.isROrC _inst_1] [_inst_3 : MetricSpace.{u2} P] [_inst_4 : NormedAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)] {s : EuclideanGeometry.Sphere.{u2} P _inst_3} {p : P} {p' : P}, (Membership.mem.{u2, u2} P (EuclideanGeometry.Sphere.{u2} P _inst_3) (EuclideanGeometry.instMembershipSphere.{u2} P _inst_3) p s) -> (LT.lt.{0} Real Real.instLTReal (Dist.dist.{u2} P (PseudoMetricSpace.toDist.{u2} P (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3)) p' (EuclideanGeometry.Sphere.center.{u2} P _inst_3 s)) (EuclideanGeometry.Sphere.radius.{u2} P _inst_3 s)) -> (Sbtw.{0, u1, u2} Real V P Real.orderedRing (NormedAddCommGroup.toAddCommGroup.{u1} V _inst_1) (NormedSpace.toModule.{0, u1} Real V Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (InnerProductSpace.toNormedSpace.{0, u1} Real V Real.isROrC _inst_1 _inst_2)) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4) p p' (EuclideanGeometry.Sphere.secondInter.{u1, u2} V P _inst_1 _inst_2 _inst_3 _inst_4 s p (VSub.vsub.{u1, u2} V P (AddTorsor.toVSub.{u1, u2} V P (SeminormedAddGroup.toAddGroup.{u1} V (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} V (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1))) (NormedAddTorsor.toAddTorsor.{u1, u2} V P (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} V _inst_1) (MetricSpace.toPseudoMetricSpace.{u2} P _inst_3) _inst_4)) p' p)))
Case conversion may be inaccurate. Consider using '#align euclidean_geometry.sphere.sbtw_second_inter EuclideanGeometry.Sphere.sbtw_secondInterₓ'. -/
/-- If the vector passed to `second_inter` is given by a subtraction involving the point in
`second_inter`, and the second point is inside the sphere, the second point is strictly between
the first point and the result of `second_inter`. -/
theorem Sphere.sbtw_secondInter {s : Sphere P} {p p' : P} (hp : p ∈ s)
    (hp' : dist p' s.center < s.radius) : Sbtw ℝ p p' (s.secondInter p (p' -ᵥ p)) :=
  by
  refine' ⟨sphere.wbtw_second_inter hp hp'.le, _, _⟩
  · rintro rfl
    rw [mem_sphere] at hp
    simpa [hp] using hp'
  · rintro h
    rw [h, mem_sphere.1 ((sphere.second_inter_mem _).2 hp)] at hp'
    exact lt_irrefl _ hp'
#align euclidean_geometry.sphere.sbtw_second_inter EuclideanGeometry.Sphere.sbtw_secondInter

end EuclideanGeometry

