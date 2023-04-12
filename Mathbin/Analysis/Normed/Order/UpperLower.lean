/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.order.upper_lower
! leanprover-community/mathlib commit 992efbda6f85a5c9074375d3c7cb9764c64d8f72
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Field.Pi
import Mathbin.Analysis.Normed.Group.Pointwise
import Mathbin.Analysis.Normed.Order.Basic
import Mathbin.Topology.Algebra.Order.UpperLower

/-!
# Upper/lower/order-connected sets in normed groups

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/


open Function Metric Set

variable {α ι : Type _}

section MetricSpace

variable [NormedOrderedGroup α] {s : Set α}

#print IsUpperSet.thickening' /-
@[to_additive IsUpperSet.thickening]
protected theorem IsUpperSet.thickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left
#align is_upper_set.thickening' IsUpperSet.thickening'
#align is_upper_set.thickening IsUpperSet.thickening
-/

#print IsLowerSet.thickening' /-
@[to_additive IsLowerSet.thickening]
protected theorem IsLowerSet.thickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (thickening ε s) := by
  rw [← ball_mul_one]
  exact hs.mul_left
#align is_lower_set.thickening' IsLowerSet.thickening'
#align is_lower_set.thickening IsLowerSet.thickening
-/

#print IsUpperSet.cthickening' /-
@[to_additive IsUpperSet.cthickening]
protected theorem IsUpperSet.cthickening' (hs : IsUpperSet s) (ε : ℝ) :
    IsUpperSet (cthickening ε s) :=
  by
  rw [cthickening_eq_Inter_thickening'']
  exact isUpperSet_interᵢ₂ fun δ hδ => hs.thickening' _
#align is_upper_set.cthickening' IsUpperSet.cthickening'
#align is_upper_set.cthickening IsUpperSet.cthickening
-/

#print IsLowerSet.cthickening' /-
@[to_additive IsLowerSet.cthickening]
protected theorem IsLowerSet.cthickening' (hs : IsLowerSet s) (ε : ℝ) :
    IsLowerSet (cthickening ε s) :=
  by
  rw [cthickening_eq_Inter_thickening'']
  exact isLowerSet_interᵢ₂ fun δ hδ => hs.thickening' _
#align is_lower_set.cthickening' IsLowerSet.cthickening'
#align is_lower_set.cthickening IsLowerSet.cthickening
-/

end MetricSpace

/-! ### `ℝⁿ` -/


section Finite

variable [Finite ι] {s : Set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

/- warning: is_upper_set.mem_interior_of_forall_lt -> IsUpperSet.mem_interior_of_forall_lt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {y : ι -> Real}, (IsUpperSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) s) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (forall (i : ι), LT.lt.{0} Real Real.hasLt (x i) (y i)) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) y (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {y : ι -> Real}, (IsUpperSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) s) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (forall (i : ι), LT.lt.{0} Real Real.instLTReal (x i) (y i)) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) y (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))
Case conversion may be inaccurate. Consider using '#align is_upper_set.mem_interior_of_forall_lt IsUpperSet.mem_interior_of_forall_ltₓ'. -/
theorem IsUpperSet.mem_interior_of_forall_lt (hs : IsUpperSet s) (hx : x ∈ closure s)
    (h : ∀ i, x i < y i) : y ∈ interior s :=
  by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, z i < y i :=
    by
    refine' fun i => (hxy _).trans_le' (sub_le_iff_le_add'.1 <| (le_abs_self _).trans _)
    rw [← Real.norm_eq_abs, ← dist_eq_norm']
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine' mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩
  rintro w hw
  refine' hs (fun i => _) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((lt_sub_iff_add_lt.2 <| hyz _).trans (hw _ <| mem_univ _).1).le
#align is_upper_set.mem_interior_of_forall_lt IsUpperSet.mem_interior_of_forall_lt

/- warning: is_lower_set.mem_interior_of_forall_lt -> IsLowerSet.mem_interior_of_forall_lt is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {y : ι -> Real}, (IsLowerSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) s) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (forall (i : ι), LT.lt.{0} Real Real.hasLt (y i) (x i)) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) y (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {y : ι -> Real}, (IsLowerSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) s) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (forall (i : ι), LT.lt.{0} Real Real.instLTReal (y i) (x i)) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) y (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))
Case conversion may be inaccurate. Consider using '#align is_lower_set.mem_interior_of_forall_lt IsLowerSet.mem_interior_of_forall_ltₓ'. -/
theorem IsLowerSet.mem_interior_of_forall_lt (hs : IsLowerSet s) (hx : x ∈ closure s)
    (h : ∀ i, y i < x i) : y ∈ interior s :=
  by
  cases nonempty_fintype ι
  obtain ⟨ε, hε, hxy⟩ := Pi.exists_forall_pos_add_lt h
  obtain ⟨z, hz, hxz⟩ := Metric.mem_closure_iff.1 hx _ hε
  rw [dist_pi_lt_iff hε] at hxz
  have hyz : ∀ i, y i < z i :=
    by
    refine' fun i =>
      (lt_sub_iff_add_lt.2 <| hxy _).trans_le (sub_le_comm.1 <| (le_abs_self _).trans _)
    rw [← Real.norm_eq_abs, ← dist_eq_norm]
    exact (hxz _).le
  obtain ⟨δ, hδ, hyz⟩ := Pi.exists_forall_pos_add_lt hyz
  refine' mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩
  rintro w hw
  refine' hs (fun i => _) hz
  simp_rw [ball_pi _ hδ, Real.ball_eq_Ioo] at hw
  exact ((hw _ <| mem_univ _).2.trans <| hyz _).le
#align is_lower_set.mem_interior_of_forall_lt IsLowerSet.mem_interior_of_forall_lt

end Finite

section Fintype

variable [Fintype ι] {s : Set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

/- warning: is_upper_set.exists_subset_ball -> IsUpperSet.exists_subset_ball is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {δ : Real}, (IsUpperSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) s) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Exists.{succ u1} (ι -> Real) (fun (y : ι -> Real) => And (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) δ (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) x δ)) (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) δ (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {δ : Real}, (IsUpperSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) s) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Exists.{succ u1} (ι -> Real) (fun (y : ι -> Real) => And (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.instHasSubsetSet.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) δ (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) x δ)) (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.instHasSubsetSet.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) δ (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))))
Case conversion may be inaccurate. Consider using '#align is_upper_set.exists_subset_ball IsUpperSet.exists_subset_ballₓ'. -/
theorem IsUpperSet.exists_subset_ball (hs : IsUpperSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s :=
  by
  refine' ⟨x + const _ (3 / 4 * δ), closed_ball_subset_closed_ball' _, _⟩
  · rw [dist_self_add_left]
    refine' (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq _
    simp [Real.norm_of_nonneg, hδ.le, zero_le_three]
    ring_nf
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine' fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => _
  rw [mem_closed_ball, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith
#align is_upper_set.exists_subset_ball IsUpperSet.exists_subset_ball

/- warning: is_lower_set.exists_subset_ball -> IsLowerSet.exists_subset_ball is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {δ : Real}, (IsLowerSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.hasLe)) s) -> (Membership.Mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.hasMem.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) δ) -> (Exists.{succ u1} (ι -> Real) (fun (y : ι -> Real) => And (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) δ (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) x δ)) (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.hasSubset.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) δ (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Fintype.{u1} ι] {s : Set.{u1} (ι -> Real)} {x : ι -> Real} {δ : Real}, (IsLowerSet.{u1} (ι -> Real) (Pi.hasLe.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (i : ι) => Real.instLEReal)) s) -> (Membership.mem.{u1, u1} (ι -> Real) (Set.{u1} (ι -> Real)) (Set.instMembershipSet.{u1} (ι -> Real)) x (closure.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s)) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) δ) -> (Exists.{succ u1} (ι -> Real) (fun (y : ι -> Real) => And (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.instHasSubsetSet.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) δ (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) x δ)) (HasSubset.Subset.{u1} (Set.{u1} (ι -> Real)) (Set.instHasSubsetSet.{u1} (ι -> Real)) (Metric.closedBall.{u1} (ι -> Real) (pseudoMetricSpacePi.{u1, 0} ι (fun (ᾰ : ι) => Real) _inst_1 (fun (a : ι) => Real.pseudoMetricSpace)) y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) δ (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))) (interior.{u1} (ι -> Real) (Pi.topologicalSpace.{u1, 0} ι (fun (ᾰ : ι) => Real) (fun (a : ι) => UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) s))))
Case conversion may be inaccurate. Consider using '#align is_lower_set.exists_subset_ball IsLowerSet.exists_subset_ballₓ'. -/
theorem IsLowerSet.exists_subset_ball (hs : IsLowerSet s) (hx : x ∈ closure s) (hδ : 0 < δ) :
    ∃ y, closedBall y (δ / 4) ⊆ closedBall x δ ∧ closedBall y (δ / 4) ⊆ interior s :=
  by
  refine' ⟨x - const _ (3 / 4 * δ), closed_ball_subset_closed_ball' _, _⟩
  · rw [dist_self_sub_left]
    refine' (add_le_add_left (pi_norm_const_le <| 3 / 4 * δ) _).trans_eq _
    simp [Real.norm_of_nonneg, hδ.le, zero_le_three]
    ring_nf
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four)
  refine' fun z hz => hs.mem_interior_of_forall_lt (subset_closure hy) fun i => _
  rw [mem_closed_ball, dist_eq_norm'] at hz
  rw [dist_eq_norm] at hxy
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le
  replace hz := (norm_le_pi_norm _ i).trans hz
  dsimp at hxy hz
  rw [abs_sub_le_iff] at hxy hz
  linarith
#align is_lower_set.exists_subset_ball IsLowerSet.exists_subset_ball

end Fintype

