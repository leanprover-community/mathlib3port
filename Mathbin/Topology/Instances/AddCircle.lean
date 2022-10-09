/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
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
 * Measure space structure
 * Lie group structure
 * Exponential equivalence to `circle`

-/


noncomputable section

open Set

open Int hiding mem_zmultiples_iff

open AddSubgroup

variable {𝕜 : Type _}

-- ./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜
/-- The "additive circle": `𝕜 ⧸ (ℤ ∙ p)`. See also `circle` and `real.angle`. -/
@[nolint unused_arguments]
def AddCircle [LinearOrderedAddCommGroup 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p : 𝕜) :=
  𝕜 ⧸ zmultiples p deriving AddCommGroupₓ, TopologicalSpace, TopologicalAddGroup, Inhabited,
  «./././Mathport/Syntax/Translate/Command.lean:42:9: unsupported derive handler has_coe_t[has_coe_t] 𝕜»

namespace AddCircle

section LinearOrderedField

variable [LinearOrderedField 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] (p q : 𝕜)

@[continuity, nolint unused_arguments]
protected theorem continuous_mk' : Continuous (QuotientAddGroup.mk' (zmultiples p) : 𝕜 → AddCircle p) :=
  continuous_coinduced_rng

/-- An auxiliary definition used only for constructing `add_circle.equiv_add_circle`. -/
private def equiv_add_circle_aux (hp : p ≠ 0) : AddCircle p →+ AddCircle q :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' (zmultiples q)).comp <| AddMonoidHom.mulRight (p⁻¹ * q)) fun x h => by
    obtain ⟨z, rfl⟩ := mem_zmultiples_iff.1 h <;> simp [hp, mul_assoc (z : 𝕜), ← mul_assoc p]

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

@[simp]
theorem equiv_add_circle_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    equivAddCircle p q hp hq (x : 𝕜) = (x * (p⁻¹ * q) : 𝕜) :=
  rfl

@[simp]
theorem equiv_add_circle_symm_apply_mk (hp : p ≠ 0) (hq : q ≠ 0) (x : 𝕜) :
    (equivAddCircle p q hp hq).symm (x : 𝕜) = (x * (q⁻¹ * p) : 𝕜) :=
  rfl

variable [FloorRing 𝕜]

/-- The natural equivalence between `add_circle p` and the half-open interval `[0, p)`. -/
def equivIco (hp : 0 < p) : AddCircle p ≃ Ico 0 p where
  invFun := QuotientAddGroup.mk' _ ∘ coe
  toFun := fun x => ⟨(to_Ico_mod_periodic 0 hp).lift x, Quot.induction_on x <| to_Ico_mod_mem_Ico' hp⟩
  right_inv := by
    rintro ⟨x, hx⟩
    ext
    simp [to_Ico_mod_eq_self, hx.1, hx.2]
  left_inv := by
    rintro ⟨x⟩
    change QuotientAddGroup.mk (toIcoMod 0 hp x) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq', neg_add_eq_sub, self_sub_to_Ico_mod, zsmul_eq_mul]
    apply int_cast_mul_mem_zmultiples

@[simp]
theorem coe_equiv_Ico_mk_apply (hp : 0 < p) (x : 𝕜) :
    (equivIco p hp <| QuotientAddGroup.mk x : 𝕜) = fract (x / p) * p :=
  to_Ico_mod_eq_fract_mul hp x

@[continuity]
theorem continuous_equiv_Ico_symm (hp : 0 < p) : Continuous (equivIco p hp).symm :=
  continuous_coinduced_rng.comp continuous_induced_dom

/-- The image of the closed interval `[0, p]` under the quotient map `𝕜 → add_circle p` is the
entire space. -/
@[simp]
theorem coe_image_Icc_eq (hp : 0 < p) : (coe : 𝕜 → AddCircle p) '' Icc 0 p = univ := by
  refine' eq_univ_iff_forall.mpr fun x => _
  let y := equiv_Ico p hp x
  exact ⟨y, ⟨y.2.1, y.2.2.le⟩, (equiv_Ico p hp).symm_apply_apply x⟩

end LinearOrderedField

variable (p : ℝ)

theorem compact_space (hp : 0 < p) : CompactSpace <| AddCircle p := by
  rw [← is_compact_univ_iff, ← coe_image_Icc_eq p hp]
  exact is_compact_Icc.image (AddCircle.continuous_mk' p)

end AddCircle

/-- The unit circle `ℝ ⧸ ℤ`. -/
abbrev UnitAddCircle :=
  AddCircle (1 : ℝ)

namespace UnitAddCircle

instance : CompactSpace UnitAddCircle :=
  AddCircle.compact_space _ zero_lt_one

end UnitAddCircle

