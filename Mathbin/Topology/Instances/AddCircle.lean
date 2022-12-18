/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module topology.instances.add_circle
! leanprover-community/mathlib commit c5c7e2760814660967bc27f0de95d190a22297f3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.AddAut
import Mathbin.GroupTheory.Divisible
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.RingTheory.Int.Basic
import Mathbin.Algebra.Order.Floor
import Mathbin.Algebra.Order.ToIntervalMod
import Mathbin.Topology.Instances.Real

/-!
# The additive circle

We define the additive circle `add_circle p` as the quotient `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`.

See also `circle` and `real.angle`.  For the normed group structure on `add_circle`, see
`add_circle.normed_add_comm_group` in a later file.

## Main definitions:

 * `add_circle`: the additive circle `𝕜 ⧸ (ℤ ∙ p)` for some period `p : 𝕜`
 * `unit_add_circle`: the special case `ℝ ⧸ ℤ`
 * `add_circle.equiv_add_circle`: the rescaling equivalence `add_circle p ≃+ add_circle q`
 * `add_circle.equiv_Ico`: the natural equivalence `add_circle p ≃ Ico 0 p`
 * `add_circle.add_order_of_div_of_gcd_eq_one`: rational points have finite order
 * `add_circle.exists_gcd_eq_one_of_is_of_fin_add_order`: finite-order points are rational

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/


noncomputable section

open Set AddSubgroup TopologicalSpace

variable {𝕜 : Type _}

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜 -/
/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[nolint unused_arguments]
def AddCircle [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p deriving AddCommGroup, TopologicalSpace, TopologicalAddGroup, Inhabited,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜»
#align add_circle AddCircle

namespace AddCircle

section LinearOrderedAddCommGroup

variable [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜)

theorem coe_nsmul {n : ℕ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
#align add_circle.coe_nsmul AddCircle.coe_nsmul

theorem coe_zsmul {n : ℤ} {x : 𝕜} : (↑(n • x) : AddCircle p) = n • (x : AddCircle p) :=
  rfl
#align add_circle.coe_zsmul AddCircle.coe_zsmul

theorem coe_neg {x : 𝕜} : (↑(-x) : AddCircle p) = -(x : AddCircle p) :=
  rfl
#align add_circle.coe_neg AddCircle.coe_neg

theorem coe_eq_zero_iff {x : 𝕜} : (x : AddCircle p) = 0 ↔ ∃ n : ℤ, n • p = x := by
  simp [AddSubgroup.mem_zmultiples_iff]
#align add_circle.coe_eq_zero_iff AddCircle.coe_eq_zero_iff

theorem coe_eq_zero_of_pos_iff (hp : 0 < p) {x : 𝕜} (hx : 0 < x) :
    (x : AddCircle p) = 0 ↔ ∃ n : ℕ, n • p = x := by
  rw [coe_eq_zero_iff]
  constructor <;> rintro ⟨n, rfl⟩
  · replace hx : 0 < n
    · contrapose! hx
      simpa only [← neg_nonneg, ← zsmul_neg, zsmul_neg'] using zsmul_nonneg hp.le (neg_nonneg.2 hx)
    exact ⟨n.to_nat, by rw [← coe_nat_zsmul, Int.toNat_of_nonneg hx.le]⟩
  · exact ⟨(n : ℤ), by simp⟩
#align add_circle.coe_eq_zero_of_pos_iff AddCircle.coe_eq_zero_of_pos_iff

@[continuity, nolint unused_arguments]
protected theorem continuous_mk' :
    Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng
#align add_circle.continuous_mk' AddCircle.continuous_mk'

variable [hp : Fact (0 < p)]

include hp

variable [Archimedean 𝕜]

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equivIco : AddCircle p ≃ ico 0 p :=
  (QuotientAddGroup.equivIcoMod 0 hp.out).trans <| Equiv.Set.ofEq <| by rw [zero_add]
#align add_circle.equiv_Ico AddCircle.equivIco

@[continuity]
theorem continuous_equiv_Ico_symm : Continuous (equivIco p).symm :=
  continuous_quotient_mk.comp continuous_subtype_coe
#align add_circle.continuous_equiv_Ico_symm AddCircle.continuous_equiv_Ico_symm

/-- The image of the closed-open interval `[0, p)` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp]
theorem coe_image_Ico_eq : (coe : 𝕜 → AddCircle p) '' ico 0 p = univ := by
  rw [image_eq_range]
  exact (equiv_Ico p).symm.range_eq_univ
#align add_circle.coe_image_Ico_eq AddCircle.coe_image_Ico_eq

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp]
theorem coe_image_Icc_eq : (coe : 𝕜 → AddCircle p) '' icc 0 p = univ :=
  eq_top_mono (image_subset _ Ico_subset_Icc_self) <| coe_image_Ico_eq _
#align add_circle.coe_image_Icc_eq AddCircle.coe_image_Icc_eq

end LinearOrderedAddCommGroup

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p q : 𝕜)

/-- The rescaling equivalence between additive circles with different periods. -/
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  QuotientAddGroup.congr _ _ (AddAut.mulRight <| (Units.mk0 p hp)⁻¹ * Units.mk0 q hq) <| by
    rw [AddMonoidHom.map_zmultiples, AddMonoidHom.coe_coe, AddAut.mul_right_apply, Units.val_mul,
      Units.val_mk0, Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel_left₀ hp]
#align add_circle.equiv_add_circle AddCircle.equivAddCircle

@[simp]
theorem equiv_add_circle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl
#align add_circle.equiv_add_circle_apply_mk AddCircle.equiv_add_circle_apply_mk

@[simp]
theorem equiv_add_circle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl
#align add_circle.equiv_add_circle_symm_apply_mk AddCircle.equiv_add_circle_symm_apply_mk

variable [hp : Fact (0 < p)]

include hp

section FloorRing

variable [FloorRing 𝕜]

@[simp]
theorem coe_equiv_Ico_mk_apply (x : 𝕜) :
    (equivIco p <| QuotientAddGroup.mk x : 𝕜) = Int.fract (x / p) * p :=
  to_Ico_mod_eq_fract_mul _ x
#align add_circle.coe_equiv_Ico_mk_apply AddCircle.coe_equiv_Ico_mk_apply

instance :
    DivisibleBy (AddCircle p)
      ℤ where 
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p x : 𝕜)) : AddCircle p)
  div_zero x := by simp only [algebraMap.coe_zero, QuotientAddGroup.coe_zero, inv_zero, zero_mul]
  div_cancel n x hn := by 
    replace hn : (n : 𝕜) ≠ 0;
    · norm_cast
      assumption
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p x)) = x
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul]
    exact (equiv_Ico p).symm_apply_apply x

end FloorRing

section FiniteOrderPoints

variable {p}

theorem add_order_of_div_of_gcd_eq_one {m n : ℕ} (hn : 0 < n) (h : gcd m n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  rcases m.eq_zero_or_pos with (rfl | hm)
  · rw [gcd_zero_left, normalize_eq] at h
    simp [h]
  set x : AddCircle p := ↑(↑m / ↑n * p)
  have hn₀ : (n : 𝕜) ≠ 0 := by 
    norm_cast
    exact ne_of_gt hn
  have hnx : n • x = 0 := by
    rw [← coe_nsmul, nsmul_eq_mul, ← mul_assoc, mul_div, mul_div_cancel_left _ hn₀, ← nsmul_eq_mul,
      QuotientAddGroup.eq_zero_iff]
    exact nsmul_mem_zmultiples p m
  apply Nat.dvd_antisymm (add_order_of_dvd_of_nsmul_eq_zero hnx)
  suffices ∃ z : ℕ, z * n = addOrderOf x * m by
    obtain ⟨z, hz⟩ := this
    simpa only [h, mul_one, gcd_comm n] using dvd_mul_gcd_of_dvd_mul (Dvd.intro_left z hz)
  replace hp := hp.out
  have : 0 < addOrderOf x • (↑m / ↑n * p) :=
    smul_pos (add_order_of_pos' <| (is_of_fin_add_order_iff_nsmul_eq_zero _).2 ⟨n, hn, hnx⟩)
      (by positivity)
  obtain ⟨z, hz⟩ := (coe_eq_zero_of_pos_iff p hp this).mp (add_order_of_nsmul_eq_zero x)
  rw [← smul_mul_assoc, nsmul_eq_mul, nsmul_eq_mul, mul_left_inj' hp.ne.symm, mul_div,
    eq_div_iff hn₀] at hz
  norm_cast  at hz
  exact ⟨z, hz⟩
#align add_circle.add_order_of_div_of_gcd_eq_one AddCircle.add_order_of_div_of_gcd_eq_one

theorem add_order_of_div_of_gcd_eq_one' {m : ℤ} {n : ℕ} (hn : 0 < n) (h : gcd m.natAbs n = 1) :
    addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  induction m
  · simp only [Int.ofNat_eq_coe, Int.cast_ofNat, Int.natAbs_ofNat] at h⊢
    exact add_order_of_div_of_gcd_eq_one hn h
  · simp only [Int.cast_negSucc, neg_div, neg_mul, coe_neg, order_of_neg]
    exact add_order_of_div_of_gcd_eq_one hn h
#align add_circle.add_order_of_div_of_gcd_eq_one' AddCircle.add_order_of_div_of_gcd_eq_one'

theorem add_order_of_coe_rat {q : ℚ} : addOrderOf (↑(↑q * p) : AddCircle p) = q.denom := by
  have : (↑(q.denom : ℤ) : 𝕜) ≠ 0 := by 
    norm_cast
    exact q.pos.ne.symm
  rw [← @Rat.num_denom q, Rat.cast_mk_of_ne_zero _ _ this, Int.cast_ofNat, Rat.num_denom,
    add_order_of_div_of_gcd_eq_one' q.pos q.cop]
  infer_instance
#align add_circle.add_order_of_coe_rat AddCircle.add_order_of_coe_rat

variable (p)

theorem gcd_mul_add_order_of_div_eq {n : ℕ} (m : ℕ) (hn : 0 < n) :
    gcd m n * addOrderOf (↑(↑m / ↑n * p) : AddCircle p) = n := by
  let n' := n / gcd m n
  let m' := m / gcd m n
  have h₀ : 0 < gcd m n := by 
    rw [zero_lt_iff] at hn⊢
    contrapose! hn
    exact ((gcd_eq_zero_iff m n).mp hn).2
  have hk' : 0 < n' := Nat.div_pos (Nat.le_of_dvd hn <| gcd_dvd_right m n) h₀
  have hgcd : gcd m' n' = 1 := Nat.coprime_div_gcd_div_gcd h₀
  simp only [mul_left_inj' hp.out.ne.symm, ←
    Nat.cast_div_div_div_cancel_right (gcd_dvd_right m n) (gcd_dvd_left m n),
    add_order_of_div_of_gcd_eq_one hk' hgcd, mul_comm _ n', Nat.div_mul_cancel (gcd_dvd_right m n)]
#align add_circle.gcd_mul_add_order_of_div_eq AddCircle.gcd_mul_add_order_of_div_eq

variable {p} [FloorRing 𝕜]

theorem exists_gcd_eq_one_of_is_of_fin_add_order {u : AddCircle p} (h : IsOfFinAddOrder u) :
    ∃ m, gcd m (addOrderOf u) = 1 ∧ m < addOrderOf u ∧ ↑((m : 𝕜) / addOrderOf u * p) = u := by
  rcases eq_or_ne u 0 with (rfl | hu)
  · exact ⟨0, by simp⟩
  set n := addOrderOf u
  change ∃ m, gcd m n = 1 ∧ m < n ∧ ↑(↑m / ↑n * p) = u
  have hn : 0 < n := add_order_of_pos' h
  have hn₀ : (n : 𝕜) ≠ 0 := by 
    norm_cast
    exact ne_of_gt hn
  let x := (equiv_Ico p u : 𝕜)
  have hxu : (x : AddCircle p) = u := (equiv_Ico p).symm_apply_apply u
  have hx₀ : 0 < addOrderOf (x : AddCircle p) := by
    rw [← hxu] at h
    exact add_order_of_pos' h
  have hx₁ : 0 < x := by 
    refine' lt_of_le_of_ne (equiv_Ico p u).2.1 _
    contrapose! hu
    rw [← hxu, ← hu, QuotientAddGroup.coe_zero]
  obtain ⟨m, hm : m • p = addOrderOf ↑x • x⟩ :=
    (coe_eq_zero_of_pos_iff p hp.out (by positivity)).mp
      (add_order_of_nsmul_eq_zero (x : AddCircle p))
  replace hm : ↑m * p = ↑n * x
  · simpa only [hxu, nsmul_eq_mul] using hm
  have hux : ↑(↑m / ↑n * p) = u := by
    rw [← hxu, ← mul_div_right_comm, hm, mul_comm _ x, mul_div_cancel x hn₀]
  refine' ⟨m, (_ : gcd m n = 1), (_ : m < n), hux⟩
  · have := gcd_mul_add_order_of_div_eq p m hn
    rwa [hux, Nat.mul_left_eq_self_iff hn] at this
  · have : n • x < n • p := smul_lt_smul_of_pos (equiv_Ico p u).2.2 hn
    rwa [nsmul_eq_mul, nsmul_eq_mul, ← hm, mul_lt_mul_right hp.out, Nat.cast_lt] at this
#align
  add_circle.exists_gcd_eq_one_of_is_of_fin_add_order AddCircle.exists_gcd_eq_one_of_is_of_fin_add_order

end FiniteOrderPoints

end LinearOrderedField

variable (p : ℝ)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is compact. -/
instance compact_space [Fact (0 < p)] : CompactSpace <| AddCircle p := by
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p]
  exact is_compact_Icc.image (AddCircle.continuous_mk' p)
#align add_circle.compact_space AddCircle.compact_space

/-- The action on `ℝ` by right multiplication of its the subgroup `zmultiples p` (the multiples of
`p:ℝ`) is properly discontinuous. -/
instance : ProperlyDiscontinuousVadd (zmultiples p).opposite ℝ :=
  (zmultiples p).properly_discontinuous_vadd_opposite_of_tendsto_cofinite
    (AddSubgroup.tendsto_zmultiples_subtype_cofinite p)

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is Hausdorff. -/
instance : T2Space (AddCircle p) :=
  t2SpaceOfProperlyDiscontinuousVaddOfT2Space

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is normal. -/
instance [Fact (0 < p)] : NormalSpace (AddCircle p) :=
  normalOfCompactT2

/-- The "additive circle" `ℝ ⧸ (ℤ ∙ p)` is second-countable. -/
instance : SecondCountableTopology (AddCircle p) :=
  QuotientAddGroup.second_countable_topology

end AddCircle

private theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨zero_lt_one⟩
#align fact_zero_lt_one fact_zero_lt_one

attribute [local instance] fact_zero_lt_one

/- ./././Mathport/Syntax/Translate/Command.lean:315:31: unsupported: @[derive] abbrev -/
/-- The unit circle `ℝ ⧸ ℤ`. -/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)
#align unit_add_circle UnitAddCircle

