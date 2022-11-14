/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathbin.GroupTheory.Divisible
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

## Implementation notes:

Although the most important case is `𝕜 = ℝ` we wish to support other types of scalars, such as
the rational circle `add_circle (1 : ℚ)`, and so we set things up more generally.

## TODO

 * Link with periodicity
 * Lie group structure
 * Exponential equivalence to `circle`

-/


noncomputable section

open Set

open Int hiding mem_zmultiples_iff

open AddSubgroup TopologicalSpace

variable {𝕜 : Type _}

/- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜 -/
/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[nolint unused_arguments]
def AddCircle [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p deriving AddCommGroup, TopologicalSpace, TopologicalAddGroup, Inhabited,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜»
#align add_circle AddCircle

namespace AddCircle

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p q : 𝕜)

@[continuity, nolint unused_arguments]
protected theorem continuous_mk' : Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng
#align add_circle.continuous_mk' AddCircle.continuous_mk'

/-- An auxiliary definition used only for constructing `add_circle.equiv_add_circle`. -/
private def equiv_add_circle_aux (hp : p ≠ 0) : AddCircle p →+ AddCircle q :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (zmultiples q)).comp <| AddMonoidHom.mulRight (p⁻¹ * q)) fun x h => by
    obtain ⟨z, rfl⟩ := mem_zmultiples_iff.1 h <;> simp [hp, mul_assoc (z : 𝕜), ← mul_assoc p]
#align add_circle.equiv_add_circle_aux add_circle.equiv_add_circle_aux

/-- The rescaling equivalence between additive circles with different periods. -/
def equivAddCircle (hp : p ≠ 0) (hq : q ≠ 0) : AddCircle p ≃+ AddCircle q :=
  { equivAddCircleAux p q hp with toFun := equivAddCircleAux p q hp, invFun := equivAddCircleAux q p hq,
    left_inv := by
      rintro ⟨x⟩
      show QuotientAddGroup.mk _ = _
      congr
      field_simp [hp, hq] ,
    right_inv := by
      rintro ⟨x⟩
      show QuotientAddGroup.mk _ = _
      congr
      field_simp [hp, hq] }
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

variable [FloorRing 𝕜] [hp : Fact (0 < p)]

include hp

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equivIco : AddCircle p ≃ ico 0 p where
  invFun := QuotientAddGroup.mk' _ ∘ coe
  toFun x := ⟨(to_Ico_mod_periodic 0 hp.out).lift x, Quot.induction_on x <| to_Ico_mod_mem_Ico' hp.out⟩
  right_inv := by
    rintro ⟨x, hx⟩
    ext
    simp [to_Ico_mod_eq_self, hx.1, hx.2]
  left_inv := by
    rintro ⟨x⟩
    change QuotientAddGroup.mk (toIcoMod 0 hp.out x) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq', neg_add_eq_sub, self_sub_to_Ico_mod, zsmul_eq_mul]
    apply int_cast_mul_mem_zmultiples
#align add_circle.equiv_Ico AddCircle.equivIco

@[simp]
theorem coe_equiv_Ico_mk_apply (x : 𝕜) : (equivIco p <| QuotientAddGroup.mk x : 𝕜) = fract (x / p) * p :=
  to_Ico_mod_eq_fract_mul _ x
#align add_circle.coe_equiv_Ico_mk_apply AddCircle.coe_equiv_Ico_mk_apply

@[continuity]
theorem continuous_equiv_Ico_symm : Continuous (equivIco p).symm :=
  continuous_coinduced_rng.comp continuous_induced_dom
#align add_circle.continuous_equiv_Ico_symm AddCircle.continuous_equiv_Ico_symm

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp]
theorem coe_image_Icc_eq : (coe : 𝕜 → AddCircle p) '' icc 0 p = univ := by
  refine' eq_univ_iff_forall.mpr fun x => _
  let y := equiv_Ico p x
  exact ⟨y, ⟨y.2.1, y.2.2.le⟩, (equiv_Ico p).symm_apply_apply x⟩
#align add_circle.coe_image_Icc_eq AddCircle.coe_image_Icc_eq

instance : DivisibleBy (AddCircle p) ℤ where
  div x n := (↑((n : 𝕜)⁻¹ * (equivIco p x : 𝕜)) : AddCircle p)
  div_zero x := by simp only [algebraMap.coe_zero, QuotientAddGroup.coe_zero, inv_zero, zero_mul]
  div_cancel n x hn := by
    replace hn : (n : 𝕜) ≠ 0
    · norm_cast
      assumption
      
    change n • QuotientAddGroup.mk' _ ((n : 𝕜)⁻¹ * ↑(equiv_Ico p x)) = x
    rw [← map_zsmul, ← smul_mul_assoc, zsmul_eq_mul, mul_inv_cancel hn, one_mul]
    exact (equiv_Ico p).symm_apply_apply x

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

/- ./././Mathport/Syntax/Translate/Command.lean:299:31: unsupported: @[derive] abbrev -/
/-- The unit circle `ℝ ⧸ ℤ`. -/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)
#align unit_add_circle UnitAddCircle

