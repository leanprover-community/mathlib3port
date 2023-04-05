/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module combinatorics.additive.e_transform
! leanprover-community/mathlib commit 207c92594599a06e7c134f8d00a030a83e6c7259
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Pointwise

/-!
# e-transforms

e-transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them, to be used
as internals of other proofs.

## Main declarations

* `finset.mul_dyson_e_transform`: The Dyson e-transform. Replaces `(s, t)` by
  `(s ∪ e • t, t ∩ e⁻¹ • s)`. The additive version preserves `|s ∩ [1, m]| + |t ∩ [1, m - e]|`.
* `finset.mul_e_transform_left`/`finset.mul_e_transform_right`: Replace `(s, t)` by
  `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `finset.mul_e_transform.card`). In particular, one of the two transforms
  increases the sum of the cardinalities and the other one decreases it. See
  `le_or_lt_of_add_le_add` and around.

## TODO

Prove the invariance property of the Dyson e-transform.
-/


open MulOpposite

open Pointwise

variable {α : Type _} [DecidableEq α]

namespace Finset

/-! ### Dyson e-transform -/


section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

#print Finset.mulDysonEtransform /-
/-- The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e • t, t ∩ e⁻¹ • s)`. This reduces the
product of the two sets. -/
@[to_additive
      "The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This\nreduces the sum of the two sets.",
  simps]
def mulDysonEtransform : Finset α × Finset α :=
  (x.1 ∪ e • x.2, x.2 ∩ e⁻¹ • x.1)
#align finset.mul_dyson_e_transform Finset.mulDysonEtransform
#align finset.add_dyson_e_transform Finset.addDysonEtransform
-/

/- warning: finset.mul_dyson_e_transform.subset -> Finset.mulDysonEtransform.subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align finset.mul_dyson_e_transform.subset Finset.mulDysonEtransform.subsetₓ'. -/
@[to_additive]
theorem mulDysonEtransform.subset :
    (mulDysonEtransform e x).1 * (mulDysonEtransform e x).2 ⊆ x.1 * x.2 :=
  by
  refine' union_mul_inter_subset_union.trans (union_subset subset.rfl _)
  rw [mul_smul_comm, smul_mul_assoc, inv_smul_smul, mul_comm]
  rfl
#align finset.mul_dyson_e_transform.subset Finset.mulDysonEtransform.subset
#align finset.add_dyson_e_transform.subset Finset.addDysonEtransform.subset

#print Finset.mulDysonEtransform.card /-
@[to_additive]
theorem mulDysonEtransform.card :
    (mulDysonEtransform e x).1.card + (mulDysonEtransform e x).2.card = x.1.card + x.2.card :=
  by
  dsimp
  rw [← card_smul_finset e (_ ∩ _), smul_finset_inter, smul_inv_smul, inter_comm,
    card_union_add_card_inter, card_smul_finset]
#align finset.mul_dyson_e_transform.card Finset.mulDysonEtransform.card
#align finset.add_dyson_e_transform.card Finset.addDysonEtransform.card
-/

#print Finset.mulDysonEtransform_idem /-
@[simp, to_additive]
theorem mulDysonEtransform_idem :
    mulDysonEtransform e (mulDysonEtransform e x) = mulDysonEtransform e x :=
  by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left_iff_subset]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left_iff_subset]
    exact inter_subset_union
#align finset.mul_dyson_e_transform_idem Finset.mulDysonEtransform_idem
#align finset.add_dyson_e_transform_idem Finset.addDysonEtransform_idem
-/

variable {e x}

/- warning: finset.mul_dyson_e_transform.smul_finset_snd_subset_fst -> Finset.mulDysonEtransform.smul_finset_snd_subset_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] {e : α} {x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (SMul.smul.{u1, u1} α (Finset.{u1} α) (Finset.smulFinset.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) e (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] {e : α} {x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)}, HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HSMul.hSMul.{u1, u1, u1} α (Finset.{u1} α) (Finset.{u1} α) (instHSMul.{u1, u1} α (Finset.{u1} α) (Finset.smulFinset.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))))))) e (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulDysonEtransform.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))
Case conversion may be inaccurate. Consider using '#align finset.mul_dyson_e_transform.smul_finset_snd_subset_fst Finset.mulDysonEtransform.smul_finset_snd_subset_fstₓ'. -/
@[to_additive]
theorem mulDysonEtransform.smul_finset_snd_subset_fst :
    e • (mulDysonEtransform e x).2 ⊆ (mulDysonEtransform e x).1 :=
  by
  dsimp
  rw [smul_finset_inter, smul_inv_smul, inter_comm]
  exact inter_subset_union
#align finset.mul_dyson_e_transform.smul_finset_snd_subset_fst Finset.mulDysonEtransform.smul_finset_snd_subset_fst
#align finset.add_dyson_e_transform.vadd_finset_snd_subset_fst Finset.addDysonEtransform.vadd_finset_snd_subset_fst

end CommGroup

/-!
### Two unnamed e-transforms

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).

This pair of transforms doesn't seem to be named in the literature. It is used by Sanders in his
bound on Roth numbers, and by DeVos in his proof of Cauchy-Davenport.
-/


section Group

variable [Group α] (e : α) (x : Finset α × Finset α)

#print Finset.mulEtransformLeft /-
/-- An **e-transform**. Turns `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive
      "An **e-transform**. Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This\nreduces the sum of the two sets.",
  simps]
def mulEtransformLeft : Finset α × Finset α :=
  (x.1 ∩ op e • x.1, x.2 ∪ e⁻¹ • x.2)
#align finset.mul_e_transform_left Finset.mulEtransformLeft
#align finset.add_e_transform_left Finset.addEtransformLeft
-/

#print Finset.mulEtransformRight /-
/-- An **e-transform**. Turns `(s, t)` into `(s ∪ s • e, t ∩ e⁻¹ • t)`. This reduces the product of
the two sets. -/
@[to_additive
      "An **e-transform**. Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the\nsum of the two sets.",
  simps]
def mulEtransformRight : Finset α × Finset α :=
  (x.1 ∪ op e • x.1, x.2 ∩ e⁻¹ • x.2)
#align finset.mul_e_transform_right Finset.mulEtransformRight
#align finset.add_e_transform_right Finset.addEtransformRight
-/

/- warning: finset.mul_e_transform_left_one -> Finset.mulEtransformLeft_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) x) x
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))) x) x
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_left_one Finset.mulEtransformLeft_oneₓ'. -/
@[simp, to_additive]
theorem mulEtransformLeft_one : mulEtransformLeft 1 x = x := by simp [mul_e_transform_left]
#align finset.mul_e_transform_left_one Finset.mulEtransformLeft_one
#align finset.add_e_transform_left_zero Finset.addEtransformLeft_zero

/- warning: finset.mul_e_transform_right_one -> Finset.mulEtransformRight_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2))))))) x) x
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_2)))))) x) x
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_right_one Finset.mulEtransformRight_oneₓ'. -/
@[simp, to_additive]
theorem mulEtransformRight_one : mulEtransformRight 1 x = x := by simp [mul_e_transform_right]
#align finset.mul_e_transform_right_one Finset.mulEtransformRight_one
#align finset.add_e_transform_right_zero Finset.addEtransformRight_zero

/- warning: finset.mul_e_transform_left.fst_mul_snd_subset -> Finset.mulEtransformLeft.fst_mul_snd_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_left.fst_mul_snd_subset Finset.mulEtransformLeft.fst_mul_snd_subsetₓ'. -/
@[to_additive]
theorem mulEtransformLeft.fst_mul_snd_subset :
    (mulEtransformLeft e x).1 * (mulEtransformLeft e x).2 ⊆ x.1 * x.2 :=
  by
  refine' inter_mul_union_subset_union.trans (union_subset subset.rfl _)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
  rfl
#align finset.mul_e_transform_left.fst_mul_snd_subset Finset.mulEtransformLeft.fst_mul_snd_subset
#align finset.add_e_transform_left.fst_add_snd_subset Finset.addEtransformLeft.fst_add_snd_subset

/- warning: finset.mul_e_transform_right.fst_mul_snd_subset -> Finset.mulEtransformRight.fst_mul_snd_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : Group.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.instHasSubsetFinset.{u1} α) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x)) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) _inst_2 e x))) (HMul.hMul.{u1, u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.{u1} α) (instHMul.{u1} (Finset.{u1} α) (Finset.mul.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_2)))))) (Prod.fst.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x) (Prod.snd.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x))
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_right.fst_mul_snd_subset Finset.mulEtransformRight.fst_mul_snd_subsetₓ'. -/
@[to_additive]
theorem mulEtransformRight.fst_mul_snd_subset :
    (mulEtransformRight e x).1 * (mulEtransformRight e x).2 ⊆ x.1 * x.2 :=
  by
  refine' union_mul_inter_subset_union.trans (union_subset subset.rfl _)
  rw [op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul]
  rfl
#align finset.mul_e_transform_right.fst_mul_snd_subset Finset.mulEtransformRight.fst_mul_snd_subset
#align finset.add_e_transform_right.fst_add_snd_subset Finset.addEtransformRight.fst_add_snd_subset

#print Finset.mulEtransformLeft.card /-
@[to_additive]
theorem mulEtransformLeft.card :
    (mulEtransformLeft e x).1.card + (mulEtransformRight e x).1.card = 2 * x.1.card :=
  (card_inter_add_card_union _ _).trans <| by rw [card_smul_finset, two_mul]
#align finset.mul_e_transform_left.card Finset.mulEtransformLeft.card
#align finset.add_e_transform_left.card Finset.addEtransformLeft.card
-/

#print Finset.mulEtransformRight.card /-
@[to_additive]
theorem mulEtransformRight.card :
    (mulEtransformLeft e x).2.card + (mulEtransformRight e x).2.card = 2 * x.2.card :=
  (card_union_add_card_inter _ _).trans <| by rw [card_smul_finset, two_mul]
#align finset.mul_e_transform_right.card Finset.mulEtransformRight.card
#align finset.add_e_transform_right.card Finset.addEtransformRight.card
-/

#print Finset.MulEtransform.card /-
/-- This statement is meant to be combined with `le_or_lt_of_add_le_add` and similar lemmas. -/
@[to_additive AddETransform.card
      "This statement is meant to be combined with\n`le_or_lt_of_add_le_add` and similar lemmas."]
protected theorem MulEtransform.card :
    (mulEtransformLeft e x).1.card + (mulEtransformLeft e x).2.card +
        ((mulEtransformRight e x).1.card + (mulEtransformRight e x).2.card) =
      x.1.card + x.2.card + (x.1.card + x.2.card) :=
  by
  rw [add_add_add_comm, mul_e_transform_left.card, mul_e_transform_right.card, ← mul_add, two_mul]
#align finset.mul_e_transform.card Finset.MulEtransform.card
#align finset.add_e_transform.card Finset.AddEtransform.card
-/

end Group

section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

/- warning: finset.mul_e_transform_left_inv -> Finset.mulEtransformLeft_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) e) x) (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) e (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) e) x) (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) e (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_left_inv Finset.mulEtransformLeft_invₓ'. -/
@[simp, to_additive]
theorem mulEtransformLeft_inv : mulEtransformLeft e⁻¹ x = (mulEtransformRight e x.symm).symm := by
  simp [-op_inv, op_smul_eq_smul, mul_e_transform_left, mul_e_transform_right]
#align finset.mul_e_transform_left_inv Finset.mulEtransformLeft_inv
#align finset.add_e_transform_left_neg Finset.addEtransformLeft_neg

/- warning: finset.mul_e_transform_right_inv -> Finset.mulEtransformRight_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_2))) e) x) (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) e (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : CommGroup.{u1} α] (e : α) (x : Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)), Eq.{succ u1} (Prod.{u1, u1} (Finset.{u1} α) (Finset.{u1} α)) (Finset.mulEtransformRight.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_2))))) e) x) (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Finset.mulEtransformLeft.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (CommGroup.toGroup.{u1} α _inst_2) e (Prod.swap.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align finset.mul_e_transform_right_inv Finset.mulEtransformRight_invₓ'. -/
@[simp, to_additive]
theorem mulEtransformRight_inv : mulEtransformRight e⁻¹ x = (mulEtransformLeft e x.symm).symm := by
  simp [-op_inv, op_smul_eq_smul, mul_e_transform_left, mul_e_transform_right]
#align finset.mul_e_transform_right_inv Finset.mulEtransformRight_inv
#align finset.add_e_transform_right_neg Finset.addEtransformRight_neg

end CommGroup

end Finset
