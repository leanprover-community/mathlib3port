/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Yaël Dillies

! This file was ported from Lean 3 source module analysis.normed.group.seminorm
! leanprover-community/mathlib commit 23c61a3ca8d0bc8e9309e0128fb40936d7a2c806
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Positivity
import Mathbin.Data.Real.Nnreal

/-!
# Group seminorms

This file defines norms and seminorms in a group. A group seminorm is a function to the reals which
is positive-semidefinite and subadditive. A norm further only maps zero to zero.

## Main declarations

* `add_group_seminorm`: A function `f` from an additive group `G` to the reals that preserves zero,
  takes nonnegative values, is subadditive and such that `f (-x) = f x` for all `x`.
* `nonarch_add_group_seminorm`: A function `f` from an additive group `G` to the reals that
  preserves zero, takes nonnegative values, is nonarchimedean and such that `f (-x) = f x`
  for all `x`.
* `group_seminorm`: A function `f` from a group `G` to the reals that sends one to zero, takes
  nonnegative values, is submultiplicative and such that `f x⁻¹ = f x` for all `x`.
* `add_group_norm`: A seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `nonarch_add_group_norm`: A nonarchimedean seminorm `f` such that `f x = 0 → x = 0` for all `x`.
* `group_norm`: A seminorm `f` such that `f x = 0 → x = 1` for all `x`.

## Notes

The corresponding hom classes are defined in `analysis.order.hom.basic` to be used by absolute
values.

We do not define `nonarch_add_group_seminorm` as an extension of `add_group_seminorm` to avoid
having a superfluous `add_le'` field in the resulting structure. The same applies to
`nonarch_add_group_norm`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

norm, seminorm
-/


open Set

open NNReal

variable {ι R R' E F G : Type _}

#print AddGroupSeminorm /-
/-- A seminorm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
subadditive and such that `f (-x) = f x` for all `x`. -/
@[protect_proj]
structure AddGroupSeminorm (G : Type _) [AddGroup G] extends ZeroHom G ℝ where
  add_le' : ∀ r s, to_fun (r + s) ≤ to_fun r + to_fun s
  neg' : ∀ r, to_fun (-r) = to_fun r
#align add_group_seminorm AddGroupSeminorm
-/

#print GroupSeminorm /-
/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` for all `x`. -/
@[to_additive, protect_proj]
structure GroupSeminorm (G : Type _) [Group G] where
  toFun : G → ℝ
  map_one' : to_fun 1 = 0
  mul_le' : ∀ x y, to_fun (x * y) ≤ to_fun x + to_fun y
  inv' : ∀ x, to_fun x⁻¹ = to_fun x
#align group_seminorm GroupSeminorm
#align add_group_seminorm AddGroupSeminorm
-/

#print NonarchAddGroupSeminorm /-
/-- A nonarchimedean seminorm on an additive group `G` is a function `f : G → ℝ` that preserves
zero, is nonarchimedean and such that `f (-x) = f x` for all `x`. -/
@[protect_proj]
structure NonarchAddGroupSeminorm (G : Type _) [AddGroup G] extends ZeroHom G ℝ where
  add_le_max' : ∀ r s, to_fun (r + s) ≤ max (to_fun r) (to_fun s)
  neg' : ∀ r, to_fun (-r) = to_fun r
#align nonarch_add_group_seminorm NonarchAddGroupSeminorm
-/

/-! NOTE: We do not define `nonarch_add_group_seminorm` as an extension of `add_group_seminorm`
  to avoid having a superfluous `add_le'` field in the resulting structure. The same applies to
  `nonarch_add_group_norm` below. -/


#print AddGroupNorm /-
/-- A norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is subadditive
and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
@[protect_proj]
structure AddGroupNorm (G : Type _) [AddGroup G] extends AddGroupSeminorm G where
  eq_zero_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 0
#align add_group_norm AddGroupNorm
-/

#print GroupNorm /-
/-- A seminorm on a group `G` is a function `f : G → ℝ` that sends one to zero, is submultiplicative
and such that `f x⁻¹ = f x` and `f x = 0 → x = 1` for all `x`. -/
@[protect_proj, to_additive]
structure GroupNorm (G : Type _) [Group G] extends GroupSeminorm G where
  eq_one_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 1
#align group_norm GroupNorm
#align add_group_norm AddGroupNorm
-/

#print NonarchAddGroupNorm /-
/-- A nonarchimedean norm on an additive group `G` is a function `f : G → ℝ` that preserves zero, is
nonarchimedean and such that `f (-x) = f x` and `f x = 0 → x = 0` for all `x`. -/
@[protect_proj]
structure NonarchAddGroupNorm (G : Type _) [AddGroup G] extends NonarchAddGroupSeminorm G where
  eq_zero_of_map_eq_zero' : ∀ x, to_fun x = 0 → x = 0
#align nonarch_add_group_norm NonarchAddGroupNorm
-/

attribute [nolint doc_blame]
  AddGroupSeminorm.toZeroHom AddGroupNorm.toAddGroupSeminorm GroupNorm.toGroupSeminorm NonarchAddGroupSeminorm.toZeroHom NonarchAddGroupNorm.toNonarchAddGroupSeminorm

attribute [to_additive] GroupNorm.toGroupSeminorm

#print NonarchAddGroupSeminormClass /-
/-- `nonarch_add_group_seminorm_class F α` states that `F` is a type of nonarchimedean seminorms on
the additive group `α`.

You should extend this class when you extend `nonarch_add_group_seminorm`. -/
@[protect_proj]
class NonarchAddGroupSeminormClass (F : Type _) (α : outParam <| Type _) [AddGroup α] extends
  NonarchimedeanHomClass F α ℝ where
  map_zero (f : F) : f 0 = 0
  map_neg_eq_map' (f : F) (a : α) : f (-a) = f a
#align nonarch_add_group_seminorm_class NonarchAddGroupSeminormClass
-/

#print NonarchAddGroupNormClass /-
/-- `nonarch_add_group_norm_class F α` states that `F` is a type of nonarchimedean norms on the
additive group `α`.

You should extend this class when you extend `nonarch_add_group_norm`. -/
@[protect_proj]
class NonarchAddGroupNormClass (F : Type _) (α : outParam <| Type _) [AddGroup α] extends
  NonarchAddGroupSeminormClass F α where
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0
#align nonarch_add_group_norm_class NonarchAddGroupNormClass
-/

section NonarchAddGroupSeminormClass

variable [AddGroup E] [NonarchAddGroupSeminormClass F E] (f : F) (x y : E)

include E

/- warning: map_sub_le_max -> map_sub_le_max is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : AddGroup.{u1} E] [_inst_2 : NonarchAddGroupSeminormClass.{u2, u1} F E _inst_1] (f : F) (x : E) (y : E), LE.le.{0} Real Real.hasLe (coeFn.{succ u2, succ u1} F (fun (_x : F) => E -> Real) (FunLike.hasCoeToFun.{succ u2, succ u1, 1} F E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u1, 0} F E Real (AddZeroClass.toHasAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u1} F E _inst_1 _inst_2))) f (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toHasSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1))) x y)) (LinearOrder.max.{0} Real Real.linearOrder (coeFn.{succ u2, succ u1} F (fun (_x : F) => E -> Real) (FunLike.hasCoeToFun.{succ u2, succ u1, 1} F E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u1, 0} F E Real (AddZeroClass.toHasAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u1} F E _inst_1 _inst_2))) f x) (coeFn.{succ u2, succ u1} F (fun (_x : F) => E -> Real) (FunLike.hasCoeToFun.{succ u2, succ u1, 1} F E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u1, 0} F E Real (AddZeroClass.toHasAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u1} F E _inst_1 _inst_2))) f y))
but is expected to have type
  forall {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : NonarchAddGroupSeminormClass.{u1, u2} F E _inst_1] (f : F) (x : E) (y : E), LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1))) x y)) Real.instLEReal (FunLike.coe.{succ u1, succ u2, 1} F E (fun (_x : E) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u2, 0} F E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u2} F E _inst_1 _inst_2)) f (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1))) x y)) (Max.max.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) x) (LinearOrderedRing.toMax.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) x) Real.instLinearOrderedRingReal) (FunLike.coe.{succ u1, succ u2, 1} F E (fun (_x : E) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u2, 0} F E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u2} F E _inst_1 _inst_2)) f x) (FunLike.coe.{succ u1, succ u2, 1} F E (fun (_x : E) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.291 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u2, 0} F E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u2} F E _inst_1 _inst_2)) f y))
Case conversion may be inaccurate. Consider using '#align map_sub_le_max map_sub_le_maxₓ'. -/
theorem map_sub_le_max : f (x - y) ≤ max (f x) (f y) :=
  by
  rw [sub_eq_add_neg, ← NonarchAddGroupSeminormClass.map_neg_eq_map' f y]
  exact map_add_le_max _ _ _
#align map_sub_le_max map_sub_le_max

end NonarchAddGroupSeminormClass

#print NonarchAddGroupSeminormClass.toAddGroupSeminormClass /-
-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupSeminormClass.toAddGroupSeminormClass [AddGroup E]
    [NonarchAddGroupSeminormClass F E] : AddGroupSeminormClass F E ℝ :=
  {
    ‹NonarchAddGroupSeminormClass F
        E› with
    map_add_le_add := fun f x y =>
      haveI h_nonneg : ∀ a, 0 ≤ f a := by
        intro a
        rw [← NonarchAddGroupSeminormClass.map_zero f, ← sub_self a]
        exact le_trans (map_sub_le_max _ _ _) (by rw [max_self (f a)])
      le_trans (map_add_le_max _ _ _)
        (max_le (le_add_of_nonneg_right (h_nonneg _)) (le_add_of_nonneg_left (h_nonneg _)))
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }
#align nonarch_add_group_seminorm_class.to_add_group_seminorm_class NonarchAddGroupSeminormClass.toAddGroupSeminormClass
-/

#print NonarchAddGroupNormClass.toAddGroupNormClass /-
-- See note [lower instance priority]
instance (priority := 100) NonarchAddGroupNormClass.toAddGroupNormClass [AddGroup E]
    [NonarchAddGroupNormClass F E] : AddGroupNormClass F E ℝ :=
  {
    ‹NonarchAddGroupNormClass F
        E› with
    map_add_le_add := map_add_le_add
    map_neg_eq_map := NonarchAddGroupSeminormClass.map_neg_eq_map' }
#align nonarch_add_group_norm_class.to_add_group_norm_class NonarchAddGroupNormClass.toAddGroupNormClass
-/

/-! ### Seminorms -/


namespace GroupSeminorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupSeminorm E}

#print GroupSeminorm.groupSeminormClass /-
@[to_additive]
instance groupSeminormClass : GroupSeminormClass (GroupSeminorm E) E ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
#align group_seminorm.group_seminorm_class GroupSeminorm.groupSeminormClass
#align add_group_seminorm.add_group_seminorm_class AddGroupSeminorm.addGroupSeminormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun`. "]
instance : CoeFun (GroupSeminorm E) fun _ => E → ℝ :=
  ⟨GroupSeminorm.toFun⟩

#print GroupSeminorm.toFun_eq_coe /-
@[simp, to_additive]
theorem toFun_eq_coe : p.toFun = p :=
  rfl
#align group_seminorm.to_fun_eq_coe GroupSeminorm.toFun_eq_coe
#align add_group_seminorm.to_fun_eq_coe AddGroupSeminorm.toFun_eq_coe
-/

#print GroupSeminorm.ext /-
@[ext, to_additive]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align group_seminorm.ext GroupSeminorm.ext
#align add_group_seminorm.ext AddGroupSeminorm.ext
-/

@[to_additive]
instance : PartialOrder (GroupSeminorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

/- warning: group_seminorm.le_def -> GroupSeminorm.le_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.partialOrder.{u1} E _inst_1))) p q) (LE.le.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instPartialOrderGroupSeminorm.{u1} E _inst_1))) p q) (LE.le.{u1} (E -> Real) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align group_seminorm.le_def GroupSeminorm.le_defₓ'. -/
@[to_additive]
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_seminorm.le_def GroupSeminorm.le_def
#align add_group_seminorm.le_def AddGroupSeminorm.le_def

/- warning: group_seminorm.lt_def -> GroupSeminorm.lt_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.partialOrder.{u1} E _inst_1))) p q) (LT.lt.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instPartialOrderGroupSeminorm.{u1} E _inst_1))) p q) (LT.lt.{u1} (E -> Real) (Preorder.toLT.{u1} (E -> Real) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align group_seminorm.lt_def GroupSeminorm.lt_defₓ'. -/
@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_seminorm.lt_def GroupSeminorm.lt_def
#align add_group_seminorm.lt_def AddGroupSeminorm.lt_def

/- warning: group_seminorm.coe_le_coe -> GroupSeminorm.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q)) (LE.le.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (E -> Real) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q)) (LE.le.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instPartialOrderGroupSeminorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_le_coe GroupSeminorm.coe_le_coeₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_seminorm.coe_le_coe GroupSeminorm.coe_le_coe
#align add_group_seminorm.coe_le_coe AddGroupSeminorm.coe_le_coe

/- warning: group_seminorm.coe_lt_coe -> GroupSeminorm.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q)) (LT.lt.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (E -> Real) (Preorder.toLT.{u1} (E -> Real) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q)) (LT.lt.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instPartialOrderGroupSeminorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_lt_coe GroupSeminorm.coe_lt_coeₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_seminorm.coe_lt_coe GroupSeminorm.coe_lt_coe
#align add_group_seminorm.coe_lt_coe AddGroupSeminorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance : Zero (GroupSeminorm E) :=
  ⟨{  toFun := 0
      map_one' := Pi.zero_apply _
      mul_le' := fun _ _ => (zero_add _).ge
      inv' := fun x => rfl }⟩

/- warning: group_seminorm.coe_zero -> GroupSeminorm.coe_zero is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E], Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (OfNat.mk.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.zero.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasZero.{u1} E _inst_1))))) (OfNat.ofNat.{u1} (E -> Real) 0 (OfNat.mk.{u1} (E -> Real) 0 (Zero.zero.{u1} (E -> Real) (Pi.instZero.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasZero)))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E], Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.toOfNat0.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instZeroGroupSeminorm.{u1} E _inst_1)))) (OfNat.ofNat.{u1} (E -> Real) 0 (Zero.toOfNat0.{u1} (E -> Real) (Pi.instZero.{u1, 0} E (fun (a : E) => Real) (fun (i : E) => Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_zero GroupSeminorm.coe_zeroₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_zero : ⇑(0 : GroupSeminorm E) = 0 :=
  rfl
#align group_seminorm.coe_zero GroupSeminorm.coe_zero
#align add_group_seminorm.coe_zero AddGroupSeminorm.coe_zero

/- warning: group_seminorm.zero_apply -> GroupSeminorm.zero_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (OfNat.mk.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.zero.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasZero.{u1} E _inst_1)))) x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.toOfNat0.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instZeroGroupSeminorm.{u1} E _inst_1))) x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align group_seminorm.zero_apply GroupSeminorm.zero_applyₓ'. -/
@[simp, to_additive]
theorem zero_apply (x : E) : (0 : GroupSeminorm E) x = 0 :=
  rfl
#align group_seminorm.zero_apply GroupSeminorm.zero_apply
#align add_group_seminorm.zero_apply AddGroupSeminorm.zero_apply

@[to_additive]
instance : Inhabited (GroupSeminorm E) :=
  ⟨0⟩

@[to_additive]
instance : Add (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => p x + q x
      map_one' := by rw [map_one_eq_zero p, map_one_eq_zero q, zero_add]
      mul_le' := fun _ _ =>
        (add_le_add (map_mul_le_add p _ _) <| map_mul_le_add q _ _).trans_eq <|
          add_add_add_comm _ _ _ _
      inv' := fun x => by rw [map_inv_eq_map p, map_inv_eq_map q] }⟩

/- warning: group_seminorm.coe_add -> GroupSeminorm.coe_add is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasAdd.{u1} E _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} (E -> Real) (E -> Real) (E -> Real) (instHAdd.{u1} (E -> Real) (Pi.instAdd.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasAdd))) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instAddGroupSeminorm.{u1} E _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} (E -> Real) (E -> Real) (E -> Real) (instHAdd.{u1} (E -> Real) (Pi.instAdd.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instAddReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_add GroupSeminorm.coe_addₓ'. -/
@[simp, to_additive]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_seminorm.coe_add GroupSeminorm.coe_add
#align add_group_seminorm.coe_add AddGroupSeminorm.coe_add

/- warning: group_seminorm.add_apply -> GroupSeminorm.add_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasAdd.{u1} E _inst_1)) p q) x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instAddGroupSeminorm.{u1} E _inst_1)) p q) x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p x) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q x))
Case conversion may be inaccurate. Consider using '#align group_seminorm.add_apply GroupSeminorm.add_applyₓ'. -/
@[simp, to_additive]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_seminorm.add_apply GroupSeminorm.add_apply
#align add_group_seminorm.add_apply AddGroupSeminorm.add_apply

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
@[to_additive]
instance : Sup (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_one' := by
        rw [Pi.sup_apply, ← map_one_eq_zero p, sup_eq_left, map_one_eq_zero p, map_one_eq_zero q]
      mul_le' := fun x y =>
        sup_le ((map_mul_le_add p x y).trans <| add_le_add le_sup_left le_sup_left)
          ((map_mul_le_add q x y).trans <| add_le_add le_sup_right le_sup_right)
      inv' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_inv_eq_map p, map_inv_eq_map q] }⟩

/- warning: group_seminorm.coe_sup -> GroupSeminorm.coe_sup is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasSup.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.hasSup.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasSup)) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (Sup.sup.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instSupGroupSeminorm.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.instSupForAll.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instSupReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_sup GroupSeminorm.coe_supₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align group_seminorm.coe_sup GroupSeminorm.coe_sup
#align add_group_seminorm.coe_sup AddGroupSeminorm.coe_sup

/- warning: group_seminorm.sup_apply -> GroupSeminorm.sup_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasSup.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.hasSup (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (Sup.sup.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instSupGroupSeminorm.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.instSupReal (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p x) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) q x))
Case conversion may be inaccurate. Consider using '#align group_seminorm.sup_apply GroupSeminorm.sup_applyₓ'. -/
@[simp, to_additive]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_seminorm.sup_apply GroupSeminorm.sup_apply
#align add_group_seminorm.sup_apply AddGroupSeminorm.sup_apply

@[to_additive]
instance : SemilatticeSup (GroupSeminorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

#print GroupSeminorm.comp /-
/-- Composition of a group seminorm with a monoid homomorphism as a group seminorm. -/
@[to_additive
      "Composition of an additive group seminorm with an additive monoid homomorphism as an\nadditive group seminorm."]
def comp (p : GroupSeminorm E) (f : F →* E) : GroupSeminorm F
    where
  toFun x := p (f x)
  map_one' := by rw [f.map_one, map_one_eq_zero p]
  mul_le' _ _ := (congr_arg p <| f.map_mul _ _).trans_le <| map_mul_le_add p _ _
  inv' x := by rw [map_inv, map_inv_eq_map p]
#align group_seminorm.comp GroupSeminorm.comp
#align add_group_seminorm.comp AddGroupSeminorm.comp
-/

/- warning: group_seminorm.coe_comp -> GroupSeminorm.coe_comp is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (F -> Real) (coeFn.{succ u2, succ u2} (GroupSeminorm.{u2} F _inst_2) (fun (_x : GroupSeminorm.{u2} F _inst_2) => F -> Real) (GroupSeminorm.hasCoeToFun.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f)) (Function.comp.{succ u2, succ u1, 1} F E Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (fun (_x : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) => F -> E) (MonoidHom.hasCoeToFun.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) f))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (F -> Real) (FunLike.coe.{succ u2, succ u2, 1} (GroupSeminorm.{u2} F _inst_2) F (fun (_x : F) => Real) (MulLEAddHomClass.toFunLike.{u2, u2, 0} (GroupSeminorm.{u2} F _inst_2) F Real (MulOneClass.toMul.{u2} F (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u2, 0} (GroupSeminorm.{u2} F _inst_2) F Real _inst_2 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u2} F _inst_2))) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f)) (Function.comp.{succ u2, succ u1, 1} F E Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F (fun (_x : F) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : F) => E) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F E (MulOneClass.toMul.{u2} F (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2)))) (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1))) (MonoidHom.monoidHomClass.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))) f))
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_comp GroupSeminorm.coe_compₓ'. -/
@[simp, to_additive]
theorem coe_comp : ⇑(p.comp f) = p ∘ f :=
  rfl
#align group_seminorm.coe_comp GroupSeminorm.coe_comp
#align add_group_seminorm.coe_comp AddGroupSeminorm.coe_comp

/- warning: group_seminorm.comp_apply -> GroupSeminorm.comp_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (x : F), Eq.{1} Real (coeFn.{succ u2, succ u2} (GroupSeminorm.{u2} F _inst_2) (fun (_x : GroupSeminorm.{u2} F _inst_2) => F -> Real) (GroupSeminorm.hasCoeToFun.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f) x) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) p (coeFn.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (fun (_x : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) => F -> E) (MonoidHom.hasCoeToFun.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) f x))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (x : F), Eq.{1} Real (FunLike.coe.{succ u2, succ u2, 1} (GroupSeminorm.{u2} F _inst_2) F (fun (_x : F) => Real) (MulLEAddHomClass.toFunLike.{u2, u2, 0} (GroupSeminorm.{u2} F _inst_2) F Real (MulOneClass.toMul.{u2} F (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u2, 0} (GroupSeminorm.{u2} F _inst_2) F Real _inst_2 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u2} F _inst_2))) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f) x) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) p (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F (fun (_x : F) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : F) => E) _x) (MulHomClass.toFunLike.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F E (MulOneClass.toMul.{u2} F (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2)))) (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, u1} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1))) (MonoidHom.monoidHomClass.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))) f x))
Case conversion may be inaccurate. Consider using '#align group_seminorm.comp_apply GroupSeminorm.comp_applyₓ'. -/
@[simp, to_additive]
theorem comp_apply (x : F) : (p.comp f) x = p (f x) :=
  rfl
#align group_seminorm.comp_apply GroupSeminorm.comp_apply
#align add_group_seminorm.comp_apply AddGroupSeminorm.comp_apply

#print GroupSeminorm.comp_id /-
@[simp, to_additive]
theorem comp_id : p.comp (MonoidHom.id _) = p :=
  ext fun _ => rfl
#align group_seminorm.comp_id GroupSeminorm.comp_id
#align add_group_seminorm.comp_id AddGroupSeminorm.comp_id
-/

/- warning: group_seminorm.comp_zero -> GroupSeminorm.comp_zero is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p (OfNat.ofNat.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) 1 (OfNat.mk.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) 1 (One.one.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (MonoidHom.hasOne.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (OfNat.mk.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (Zero.zero.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.hasZero.{u2} F _inst_2))))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p (OfNat.ofNat.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) 1 (One.toOfNat1.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (instOneMonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (Zero.toOfNat0.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.instZeroGroupSeminorm.{u2} F _inst_2)))
Case conversion may be inaccurate. Consider using '#align group_seminorm.comp_zero GroupSeminorm.comp_zeroₓ'. -/
@[simp, to_additive]
theorem comp_zero : p.comp (1 : F →* E) = 0 :=
  ext fun _ => map_one_eq_zero p
#align group_seminorm.comp_zero GroupSeminorm.comp_zero
#align add_group_seminorm.comp_zero AddGroupSeminorm.comp_zero

/- warning: group_seminorm.zero_comp -> GroupSeminorm.zero_comp is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (OfNat.mk.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.zero.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasZero.{u1} E _inst_1)))) f) (OfNat.ofNat.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (OfNat.mk.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (Zero.zero.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.hasZero.{u2} F _inst_2))))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 0 (Zero.toOfNat0.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instZeroGroupSeminorm.{u1} E _inst_1))) f) (OfNat.ofNat.{u2} (GroupSeminorm.{u2} F _inst_2) 0 (Zero.toOfNat0.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.instZeroGroupSeminorm.{u2} F _inst_2)))
Case conversion may be inaccurate. Consider using '#align group_seminorm.zero_comp GroupSeminorm.zero_compₓ'. -/
@[simp, to_additive]
theorem zero_comp : (0 : GroupSeminorm E).comp f = 0 :=
  ext fun _ => rfl
#align group_seminorm.zero_comp GroupSeminorm.zero_comp
#align add_group_seminorm.zero_comp AddGroupSeminorm.zero_comp

/- warning: group_seminorm.comp_assoc -> GroupSeminorm.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} {G : Type.{u3}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] [_inst_3 : Group.{u3} G] (p : GroupSeminorm.{u1} E _inst_1) (g : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (f : MonoidHom.{u3, u2} G F (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2)))), Eq.{succ u3} (GroupSeminorm.{u3} G _inst_3) (GroupSeminorm.comp.{u1, u3} E G _inst_1 _inst_3 p (MonoidHom.comp.{u3, u2, u1} G F E (Monoid.toMulOneClass.{u3} G (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_3))) (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1))) g f)) (GroupSeminorm.comp.{u2, u3} F G _inst_2 _inst_3 (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p g) f)
but is expected to have type
  forall {E : Type.{u2}} {F : Type.{u3}} {G : Type.{u1}} [_inst_1 : Group.{u2} E] [_inst_2 : Group.{u3} F] [_inst_3 : Group.{u1} G] (p : GroupSeminorm.{u2} E _inst_1) (g : MonoidHom.{u3, u2} F E (Monoid.toMulOneClass.{u3} F (DivInvMonoid.toMonoid.{u3} F (Group.toDivInvMonoid.{u3} F _inst_2))) (Monoid.toMulOneClass.{u2} E (DivInvMonoid.toMonoid.{u2} E (Group.toDivInvMonoid.{u2} E _inst_1)))) (f : MonoidHom.{u1, u3} G F (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u3} F (DivInvMonoid.toMonoid.{u3} F (Group.toDivInvMonoid.{u3} F _inst_2)))), Eq.{succ u1} (GroupSeminorm.{u1} G _inst_3) (GroupSeminorm.comp.{u2, u1} E G _inst_1 _inst_3 p (MonoidHom.comp.{u1, u3, u2} G F E (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_3))) (Monoid.toMulOneClass.{u3} F (DivInvMonoid.toMonoid.{u3} F (Group.toDivInvMonoid.{u3} F _inst_2))) (Monoid.toMulOneClass.{u2} E (DivInvMonoid.toMonoid.{u2} E (Group.toDivInvMonoid.{u2} E _inst_1))) g f)) (GroupSeminorm.comp.{u3, u1} F G _inst_2 _inst_3 (GroupSeminorm.comp.{u2, u3} E F _inst_1 _inst_2 p g) f)
Case conversion may be inaccurate. Consider using '#align group_seminorm.comp_assoc GroupSeminorm.comp_assocₓ'. -/
@[to_additive]
theorem comp_assoc (g : F →* E) (f : G →* F) : p.comp (g.comp f) = (p.comp g).comp f :=
  ext fun _ => rfl
#align group_seminorm.comp_assoc GroupSeminorm.comp_assoc
#align add_group_seminorm.comp_assoc AddGroupSeminorm.comp_assoc

/- warning: group_seminorm.add_comp -> GroupSeminorm.add_comp is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasAdd.{u1} E _inst_1)) p q) f) (HAdd.hAdd.{u2, u2, u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.{u2} F _inst_2) (instHAdd.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.hasAdd.{u2} F _inst_2)) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 q f))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] (p : GroupSeminorm.{u1} E _inst_1) (q : GroupSeminorm.{u1} E _inst_1) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), Eq.{succ u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.{u1} E _inst_1) (instHAdd.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.instAddGroupSeminorm.{u1} E _inst_1)) p q) f) (HAdd.hAdd.{u2, u2, u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.{u2} F _inst_2) (instHAdd.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.instAddGroupSeminorm.{u2} F _inst_2)) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 q f))
Case conversion may be inaccurate. Consider using '#align group_seminorm.add_comp GroupSeminorm.add_compₓ'. -/
@[to_additive]
theorem add_comp (f : F →* E) : (p + q).comp f = p.comp f + q.comp f :=
  ext fun _ => rfl
#align group_seminorm.add_comp GroupSeminorm.add_comp
#align add_group_seminorm.add_comp AddGroupSeminorm.add_comp

variable {p q}

/- warning: group_seminorm.comp_mono -> GroupSeminorm.comp_mono is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : Group.{u1} E] [_inst_2 : Group.{u2} F] {p : GroupSeminorm.{u1} E _inst_1} {q : GroupSeminorm.{u1} E _inst_1} (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F _inst_2))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))), (LE.le.{u1} (GroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.partialOrder.{u1} E _inst_1))) p q) -> (LE.le.{u2} (GroupSeminorm.{u2} F _inst_2) (Preorder.toLE.{u2} (GroupSeminorm.{u2} F _inst_2) (PartialOrder.toPreorder.{u2} (GroupSeminorm.{u2} F _inst_2) (GroupSeminorm.partialOrder.{u2} F _inst_2))) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 p f) (GroupSeminorm.comp.{u1, u2} E F _inst_1 _inst_2 q f))
but is expected to have type
  forall {E : Type.{u2}} {F : Type.{u1}} [_inst_1 : Group.{u2} E] [_inst_2 : Group.{u1} F] {p : GroupSeminorm.{u2} E _inst_1} {q : GroupSeminorm.{u2} E _inst_1} (f : MonoidHom.{u1, u2} F E (Monoid.toMulOneClass.{u1} F (DivInvMonoid.toMonoid.{u1} F (Group.toDivInvMonoid.{u1} F _inst_2))) (Monoid.toMulOneClass.{u2} E (DivInvMonoid.toMonoid.{u2} E (Group.toDivInvMonoid.{u2} E _inst_1)))), (LE.le.{u2} (GroupSeminorm.{u2} E _inst_1) (Preorder.toLE.{u2} (GroupSeminorm.{u2} E _inst_1) (PartialOrder.toPreorder.{u2} (GroupSeminorm.{u2} E _inst_1) (GroupSeminorm.instPartialOrderGroupSeminorm.{u2} E _inst_1))) p q) -> (LE.le.{u1} (GroupSeminorm.{u1} F _inst_2) (Preorder.toLE.{u1} (GroupSeminorm.{u1} F _inst_2) (PartialOrder.toPreorder.{u1} (GroupSeminorm.{u1} F _inst_2) (GroupSeminorm.instPartialOrderGroupSeminorm.{u1} F _inst_2))) (GroupSeminorm.comp.{u2, u1} E F _inst_1 _inst_2 p f) (GroupSeminorm.comp.{u2, u1} E F _inst_1 _inst_2 q f))
Case conversion may be inaccurate. Consider using '#align group_seminorm.comp_mono GroupSeminorm.comp_monoₓ'. -/
@[to_additive]
theorem comp_mono (hp : p ≤ q) : p.comp f ≤ q.comp f := fun _ => hp _
#align group_seminorm.comp_mono GroupSeminorm.comp_mono
#align add_group_seminorm.comp_mono AddGroupSeminorm.comp_mono

end Group

section CommGroup

variable [CommGroup E] [CommGroup F] (p q : GroupSeminorm E) (x y : E)

/- warning: group_seminorm.comp_mul_le -> GroupSeminorm.comp_mul_le is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : CommGroup.{u1} E] [_inst_2 : CommGroup.{u2} F] (p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (g : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))), LE.le.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (Preorder.toLE.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (PartialOrder.toPreorder.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.partialOrder.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (instHMul.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.hasMul.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (CommGroup.toCommMonoid.{u1} E _inst_1))) f g)) (HAdd.hAdd.{u2, u2, u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (instHAdd.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.hasAdd.{u2} F (CommGroup.toGroup.{u2} F _inst_2))) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p f) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p g))
but is expected to have type
  forall {E : Type.{u1}} {F : Type.{u2}} [_inst_1 : CommGroup.{u1} E] [_inst_2 : CommGroup.{u2} F] (p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (f : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (g : MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))), LE.le.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (Preorder.toLE.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (PartialOrder.toPreorder.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.instPartialOrderGroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (instHMul.{max u1 u2} (MonoidHom.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (MonoidHom.mul.{u2, u1} F E (Monoid.toMulOneClass.{u2} F (DivInvMonoid.toMonoid.{u2} F (Group.toDivInvMonoid.{u2} F (CommGroup.toGroup.{u2} F _inst_2)))) (CommGroup.toCommMonoid.{u1} E _inst_1))) f g)) (HAdd.hAdd.{u2, u2, u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (instHAdd.{u2} (GroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2)) (GroupSeminorm.instAddGroupSeminorm.{u2} F (CommGroup.toGroup.{u2} F _inst_2))) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p f) (GroupSeminorm.comp.{u1, u2} E F (CommGroup.toGroup.{u1} E _inst_1) (CommGroup.toGroup.{u2} F _inst_2) p g))
Case conversion may be inaccurate. Consider using '#align group_seminorm.comp_mul_le GroupSeminorm.comp_mul_leₓ'. -/
@[to_additive]
theorem comp_mul_le (f g : F →* E) : p.comp (f * g) ≤ p.comp f + p.comp g := fun _ =>
  map_mul_le_add p _ _
#align group_seminorm.comp_mul_le GroupSeminorm.comp_mul_le
#align add_group_seminorm.comp_add_le AddGroupSeminorm.comp_add_le

/- warning: group_seminorm.mul_bdd_below_range_add -> GroupSeminorm.mul_bddBelow_range_add is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : CommGroup.{u1} E] {p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)} {q : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)} {x : E}, BddBelow.{0} Real Real.preorder (Set.range.{0, succ u1} Real E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (fun (_x : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) p y) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (fun (_x : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) q (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) x y))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : CommGroup.{u1} E] {p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)} {q : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)} {x : E}, BddBelow.{0} Real Real.instPreorderReal (Set.range.{0, succ u1} Real E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (CommGroup.toGroup.{u1} E _inst_1) Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) p y) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (CommGroup.toGroup.{u1} E _inst_1) Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) q (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) x y))))
Case conversion may be inaccurate. Consider using '#align group_seminorm.mul_bdd_below_range_add GroupSeminorm.mul_bddBelow_range_addₓ'. -/
@[to_additive]
theorem mul_bddBelow_range_add {p q : GroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x / y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
#align group_seminorm.mul_bdd_below_range_add GroupSeminorm.mul_bddBelow_range_add
#align add_group_seminorm.add_bdd_below_range_add AddGroupSeminorm.add_bddBelow_range_add

@[to_additive]
noncomputable instance : Inf (GroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := fun x => ⨅ y, p y + q (x / y)
      map_one' :=
        cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt (fun x => by positivity) fun r hr =>
          ⟨1, by rwa [div_one, map_one_eq_zero p, map_one_eq_zero q, add_zero]⟩
      mul_le' := fun x y =>
        le_cinfᵢ_add_cinfᵢ fun u v =>
          by
          refine' cinfᵢ_le_of_le mul_bdd_below_range_add (u * v) _
          rw [mul_div_mul_comm, add_add_add_comm]
          exact add_le_add (map_mul_le_add p _ _) (map_mul_le_add q _ _)
      inv' := fun x =>
        (inv_surjective.infᵢ_comp _).symm.trans <| by
          simp_rw [map_inv_eq_map p, ← inv_div', map_inv_eq_map q] }⟩

/- warning: group_seminorm.inf_apply -> GroupSeminorm.inf_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : CommGroup.{u1} E] (p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (q : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (fun (_x : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (Inf.inf.{u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (GroupSeminorm.hasInf.{u1} E _inst_1) p q) x) (infᵢ.{0, succ u1} Real Real.hasInf E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (fun (_x : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) p y) (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (fun (_x : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) q (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toHasDiv.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) x y))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : CommGroup.{u1} E] (p : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (q : GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (CommGroup.toGroup.{u1} E _inst_1) Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) (Inf.inf.{u1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) (GroupSeminorm.instInfGroupSeminormToGroup.{u1} E _inst_1) p q) x) (infᵢ.{0, succ u1} Real Real.instInfSetReal E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (CommGroup.toGroup.{u1} E _inst_1) Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) p y) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1))))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E (CommGroup.toGroup.{u1} E _inst_1)) E Real (CommGroup.toGroup.{u1} E _inst_1) Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) q (HDiv.hDiv.{u1, u1, u1} E E E (instHDiv.{u1} E (DivInvMonoid.toDiv.{u1} E (Group.toDivInvMonoid.{u1} E (CommGroup.toGroup.{u1} E _inst_1)))) x y))))
Case conversion may be inaccurate. Consider using '#align group_seminorm.inf_apply GroupSeminorm.inf_applyₓ'. -/
@[simp, to_additive]
theorem inf_apply : (p ⊓ q) x = ⨅ y, p y + q (x / y) :=
  rfl
#align group_seminorm.inf_apply GroupSeminorm.inf_apply
#align add_group_seminorm.inf_apply AddGroupSeminorm.inf_apply

@[to_additive]
noncomputable instance : Lattice (GroupSeminorm E) :=
  { GroupSeminorm.semilatticeSup with
    inf := (· ⊓ ·)
    inf_le_left := fun p q x =>
      cinfᵢ_le_of_le mul_bddBelow_range_add x <| by rw [div_self', map_one_eq_zero q, add_zero]
    inf_le_right := fun p q x =>
      cinfᵢ_le_of_le mul_bddBelow_range_add (1 : E) <| by
        simp only [div_one, map_one_eq_zero p, zero_add]
    le_inf := fun a b c hb hc x =>
      le_cinfᵢ fun u => (le_map_add_map_div a _ _).trans <| add_le_add (hb _) (hc _) }

end CommGroup

end GroupSeminorm

/- TODO: All the following ought to be automated using `to_additive`. The problem is that it doesn't
see that `has_smul R ℝ` should be fixed because `ℝ` is fixed. -/
namespace AddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ] (p : AddGroupSeminorm E)

instance [DecidableEq E] : One (AddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add, zero_add]
        · rw [if_neg hx]
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

/- warning: add_group_seminorm.apply_one -> AddGroupSeminorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (AddGroupSeminorm.{u1} E _inst_1) (fun (_x : AddGroupSeminorm.{u1} E _inst_1) => E -> Real) (AddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (AddGroupSeminorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (AddGroupSeminorm.{u1} E _inst_1) 1 (One.one.{u1} (AddGroupSeminorm.{u1} E _inst_1) (AddGroupSeminorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (_inst_5 x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (AddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (SubadditiveHomClass.toFunLike.{u1, u1, 0} (AddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u1, u1, 0} (AddGroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (AddGroupSeminorm.addGroupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (AddGroupSeminorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (AddGroupSeminorm.{u1} E _inst_1) (AddGroupSeminorm.toOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b)))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (_inst_5 x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align add_group_seminorm.apply_one AddGroupSeminorm.apply_oneₓ'. -/
@[simp]
theorem apply_one [DecidableEq E] (x : E) : (1 : AddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_seminorm.apply_one AddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
instance : SMul R (AddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero,
          MulZeroClass.mul_zero]
      add_le' := fun _ _ =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        exact
          (mul_le_mul_of_nonneg_left (map_add_le_add _ _ _) <| NNReal.coe_nonneg _).trans_eq
            (mul_add _ _ _)
      neg' := fun x => by rw [map_neg_eq_map] }⟩

/- warning: add_group_seminorm.coe_smul -> AddGroupSeminorm.coe_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (SMulZeroClass.toHasSmul.{0, 0} NNReal Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (SMulWithZero.toSmulZeroClass.{0, 0} NNReal Real (MulZeroClass.toHasZero.{0} NNReal (MulZeroOneClass.toMulZeroClass.{0} NNReal (MonoidWithZero.toMulZeroOneClass.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (MulActionWithZero.toSMulWithZero.{0, 0} NNReal Real (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (Module.toMulActionWithZero.{0, 0} NNReal Real NNReal.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (NNReal.module.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (Semiring.toModule.{0} Real Real.semiring)))))) _inst_2] (r : R) (p : AddGroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (coeFn.{succ u2, succ u2} (AddGroupSeminorm.{u2} E _inst_1) (fun (_x : AddGroupSeminorm.{u2} E _inst_1) => E -> Real) (AddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) (SMul.smul.{u1, u2} R (AddGroupSeminorm.{u2} E _inst_1) (AddGroupSeminorm.hasSmul.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4) r p)) (SMul.smul.{u1, u2} R (E -> Real) (Function.hasSMul.{u2, u1, 0} E R Real _inst_2) r (coeFn.{succ u2, succ u2} (AddGroupSeminorm.{u2} E _inst_1) (fun (_x : AddGroupSeminorm.{u2} E _inst_1) => E -> Real) (AddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) p))
but is expected to have type
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (Algebra.toSMul.{0, 0} NNReal Real instNNRealCommSemiring Real.semiring (NNReal.instAlgebraNNRealInstNNRealCommSemiring.{0} Real Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) _inst_2] (r : R) (p : AddGroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (FunLike.coe.{succ u2, succ u2, 1} (AddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (SubadditiveHomClass.toFunLike.{u2, u2, 0} (AddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u2, u2, 0} (AddGroupSeminorm.{u2} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (AddGroupSeminorm.addGroupSeminormClass.{u2} E _inst_1))) (HSMul.hSMul.{u1, u2, u2} R (AddGroupSeminorm.{u2} E _inst_1) (AddGroupSeminorm.{u2} E _inst_1) (instHSMul.{u1, u2} R (AddGroupSeminorm.{u2} E _inst_1) (AddGroupSeminorm.toSMul.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4)) r p)) (HSMul.hSMul.{u1, u2, u2} R (E -> Real) (E -> Real) (instHSMul.{u1, u2} R (E -> Real) (Pi.instSMul.{u2, 0, u1} E R (fun (a : E) => Real) (fun (i : E) => _inst_2))) r (FunLike.coe.{succ u2, succ u2, 1} (AddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (SubadditiveHomClass.toFunLike.{u2, u2, 0} (AddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u2, u2, 0} (AddGroupSeminorm.{u2} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (AddGroupSeminorm.addGroupSeminormClass.{u2} E _inst_1))) p))
Case conversion may be inaccurate. Consider using '#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smulₓ'. -/
@[simp, norm_cast]
theorem coe_smul (r : R) (p : AddGroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smul

#print AddGroupSeminorm.smul_apply /-
@[simp]
theorem smul_apply (r : R) (p : AddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align add_group_seminorm.smul_apply AddGroupSeminorm.smul_apply
-/

instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (AddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a (p x)⟩

#print AddGroupSeminorm.smul_sup /-
theorem smul_sup (r : R) (p q : AddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align add_group_seminorm.smul_sup AddGroupSeminorm.smul_sup
-/

end AddGroupSeminorm

namespace NonarchAddGroupSeminorm

section AddGroup

variable [AddGroup E] [AddGroup F] [AddGroup G] {p q : NonarchAddGroupSeminorm E}

#print NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass /-
instance nonarchAddGroupSeminormClass : NonarchAddGroupSeminormClass (NonarchAddGroupSeminorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
#align nonarch_add_group_seminorm.nonarch_add_group_seminorm_class NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
instance : CoeFun (NonarchAddGroupSeminorm E) fun _ => E → ℝ :=
  ⟨NonarchAddGroupSeminorm.toFun⟩

/- warning: nonarch_add_group_seminorm.to_fun_eq_coe -> NonarchAddGroupSeminorm.toZeroHom_eq_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1}, Eq.{succ u1} (E -> Real) (NonarchAddGroupSeminorm.toFun.{u1} E _inst_1 p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1}, Eq.{succ u1} (forall (ᾰ : E), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : E) => Real) ᾰ) (FunLike.coe.{succ u1, succ u1, 1} (ZeroHom.{u1, 0} E Real (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1)))) Real.instZeroReal) E (fun (a : E) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.124 : E) => Real) a) (ZeroHomClass.toFunLike.{u1, u1, 0} (ZeroHom.{u1, 0} E Real (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1)))) Real.instZeroReal) E Real (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1)))) Real.instZeroReal (ZeroHom.zeroHomClass.{u1, 0} E Real (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1)))) Real.instZeroReal)) (NonarchAddGroupSeminorm.toZeroHom.{u1} E _inst_1 p)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.to_fun_eq_coe NonarchAddGroupSeminorm.toZeroHom_eq_coeₓ'. -/
@[simp]
theorem toZeroHom_eq_coe : p.toFun = p :=
  rfl
#align nonarch_add_group_seminorm.to_fun_eq_coe NonarchAddGroupSeminorm.toZeroHom_eq_coe

/- warning: nonarch_add_group_seminorm.ext -> NonarchAddGroupSeminorm.ext is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q x)) -> (Eq.{succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q x)) -> (Eq.{succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.ext NonarchAddGroupSeminorm.extₓ'. -/
@[ext]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align nonarch_add_group_seminorm.ext NonarchAddGroupSeminorm.ext

noncomputable instance : PartialOrder (NonarchAddGroupSeminorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

/- warning: nonarch_add_group_seminorm.le_def -> NonarchAddGroupSeminorm.le_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.partialOrder.{u1} E _inst_1))) p q) (LE.le.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instPartialOrderNonarchAddGroupSeminorm.{u1} E _inst_1))) p q) (LE.le.{u1} (E -> Real) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.le_def NonarchAddGroupSeminorm.le_defₓ'. -/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_seminorm.le_def NonarchAddGroupSeminorm.le_def

/- warning: nonarch_add_group_seminorm.lt_def -> NonarchAddGroupSeminorm.lt_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.partialOrder.{u1} E _inst_1))) p q) (LT.lt.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instPartialOrderNonarchAddGroupSeminorm.{u1} E _inst_1))) p q) (LT.lt.{u1} (E -> Real) (Preorder.toLT.{u1} (E -> Real) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.lt_def NonarchAddGroupSeminorm.lt_defₓ'. -/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_seminorm.lt_def NonarchAddGroupSeminorm.lt_def

/- warning: nonarch_add_group_seminorm.coe_le_coe -> NonarchAddGroupSeminorm.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q)) (LE.le.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LE.le.{u1} (E -> Real) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q)) (LE.le.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instPartialOrderNonarchAddGroupSeminorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.coe_le_coe NonarchAddGroupSeminorm.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nonarch_add_group_seminorm.coe_le_coe NonarchAddGroupSeminorm.coe_le_coe

/- warning: nonarch_add_group_seminorm.coe_lt_coe -> NonarchAddGroupSeminorm.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q)) (LT.lt.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E _inst_1} {q : NonarchAddGroupSeminorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (E -> Real) (Preorder.toLT.{u1} (E -> Real) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q)) (LT.lt.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instPartialOrderNonarchAddGroupSeminorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.coe_lt_coe NonarchAddGroupSeminorm.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align nonarch_add_group_seminorm.coe_lt_coe NonarchAddGroupSeminorm.coe_lt_coe

variable (p q) (f : F →+ E)

instance : Zero (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := 0
      map_zero' := Pi.zero_apply _
      add_le_max' := fun r s => by simp only [Pi.zero_apply, max_eq_right]
      neg' := fun x => rfl }⟩

/- warning: nonarch_add_group_seminorm.coe_zero -> NonarchAddGroupSeminorm.coe_zero is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E], Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (OfNat.mk.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (Zero.zero.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.hasZero.{u1} E _inst_1))))) (OfNat.ofNat.{u1} (E -> Real) 0 (OfNat.mk.{u1} (E -> Real) 0 (Zero.zero.{u1} (E -> Real) (Pi.instZero.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasZero)))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E], Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (Zero.toOfNat0.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instZeroNonarchAddGroupSeminorm.{u1} E _inst_1)))) (OfNat.ofNat.{u1} (E -> Real) 0 (Zero.toOfNat0.{u1} (E -> Real) (Pi.instZero.{u1, 0} E (fun (a : E) => Real) (fun (i : E) => Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.coe_zero NonarchAddGroupSeminorm.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ⇑(0 : NonarchAddGroupSeminorm E) = 0 :=
  rfl
#align nonarch_add_group_seminorm.coe_zero NonarchAddGroupSeminorm.coe_zero

/- warning: nonarch_add_group_seminorm.zero_apply -> NonarchAddGroupSeminorm.zero_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (OfNat.mk.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (Zero.zero.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.hasZero.{u1} E _inst_1)))) x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 0 (Zero.toOfNat0.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instZeroNonarchAddGroupSeminorm.{u1} E _inst_1))) x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.zero_apply NonarchAddGroupSeminorm.zero_applyₓ'. -/
@[simp]
theorem zero_apply (x : E) : (0 : NonarchAddGroupSeminorm E) x = 0 :=
  rfl
#align nonarch_add_group_seminorm.zero_apply NonarchAddGroupSeminorm.zero_apply

instance : Inhabited (NonarchAddGroupSeminorm E) :=
  ⟨0⟩

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
instance : Sup (NonarchAddGroupSeminorm E) :=
  ⟨fun p q =>
    { toFun := p ⊔ q
      map_zero' := by rw [Pi.sup_apply, ← map_zero p, sup_eq_left, map_zero p, map_zero q]
      add_le_max' := fun x y =>
        sup_le ((map_add_le_max p x y).trans <| max_le_max le_sup_left le_sup_left)
          ((map_add_le_max q x y).trans <| max_le_max le_sup_right le_sup_right)
      neg' := fun x => by rw [Pi.sup_apply, Pi.sup_apply, map_neg_eq_map p, map_neg_eq_map q] }⟩

/- warning: nonarch_add_group_seminorm.coe_sup -> NonarchAddGroupSeminorm.coe_sup is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupSeminorm.{u1} E _inst_1) (q : NonarchAddGroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.hasSup.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.hasSup.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasSup)) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupSeminorm.{u1} E _inst_1) (q : NonarchAddGroupSeminorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (Sup.sup.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instSupNonarchAddGroupSeminorm.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.instSupForAll.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.instSupReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.coe_sup NonarchAddGroupSeminorm.coe_supₓ'. -/
@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align nonarch_add_group_seminorm.coe_sup NonarchAddGroupSeminorm.coe_sup

/- warning: nonarch_add_group_seminorm.sup_apply -> NonarchAddGroupSeminorm.sup_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupSeminorm.{u1} E _inst_1) (q : NonarchAddGroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.hasSup.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.hasSup (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupSeminorm.{u1} E _inst_1) (q : NonarchAddGroupSeminorm.{u1} E _inst_1) (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (Sup.sup.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instSupNonarchAddGroupSeminorm.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.instSupReal (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) p x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) q x))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.sup_apply NonarchAddGroupSeminorm.sup_applyₓ'. -/
@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_seminorm.sup_apply NonarchAddGroupSeminorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupSeminorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

end AddGroup

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] (p q : NonarchAddGroupSeminorm E) (x y : E)

/- warning: nonarch_add_group_seminorm.add_bdd_below_range_add -> NonarchAddGroupSeminorm.add_bddBelow_range_add is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)} {q : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)} {x : E}, BddBelow.{0} Real Real.preorder (Set.range.{0, succ u1} Real E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) (fun (_x : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) p y) (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) (fun (_x : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) q (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toHasSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) x y))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddCommGroup.{u1} E] {p : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)} {q : NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)} {x : E}, BddBelow.{0} Real Real.instPreorderReal (Set.range.{0, succ u1} Real E (fun (y : E) => HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1))))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E (AddCommGroup.toAddGroup.{u1} E _inst_1) (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) p y) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1))))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)) E (AddCommGroup.toAddGroup.{u1} E _inst_1) (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) q (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (AddCommGroup.toAddGroup.{u1} E _inst_1)))) x y))))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.add_bdd_below_range_add NonarchAddGroupSeminorm.add_bddBelow_range_addₓ'. -/
theorem add_bddBelow_range_add {p q : NonarchAddGroupSeminorm E} {x : E} :
    BddBelow (range fun y => p y + q (x - y)) :=
  ⟨0, by
    rintro _ ⟨x, rfl⟩
    dsimp
    positivity⟩
#align nonarch_add_group_seminorm.add_bdd_below_range_add NonarchAddGroupSeminorm.add_bddBelow_range_add

end AddCommGroup

end NonarchAddGroupSeminorm

namespace GroupSeminorm

variable [Group E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

@[to_additive AddGroupSeminorm.hasOne]
instance [DecidableEq E] : One (GroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 1 then 0 else 1
      map_one' := if_pos rfl
      mul_le' := fun x y => by
        by_cases hx : x = 1
        · rw [if_pos hx, hx, one_mul, zero_add]
        · rw [if_neg hx]
          refine' le_add_of_le_of_nonneg _ _ <;> split_ifs <;> norm_num
      inv' := fun x => by simp_rw [inv_eq_one] }⟩

/- warning: group_seminorm.apply_one -> GroupSeminorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupSeminorm.{u1} E _inst_1) (fun (_x : GroupSeminorm.{u1} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (GroupSeminorm.{u1} E _inst_1) 1 (One.one.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))))) (_inst_5 x (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (GroupSeminorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (GroupSeminorm.{u1} E _inst_1) (GroupSeminorm.toOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b)))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (Group.toDivisionMonoid.{u1} E _inst_1))))))) (_inst_5 x (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (Group.toDivisionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align group_seminorm.apply_one GroupSeminorm.apply_oneₓ'. -/
@[simp, to_additive AddGroupSeminorm.apply_one]
theorem apply_one [DecidableEq E] (x : E) : (1 : GroupSeminorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_seminorm.apply_one GroupSeminorm.apply_one
#align add_group_seminorm.apply_one AddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to an `add_group_seminorm`. -/
@[to_additive AddGroupSeminorm.hasSmul]
instance : SMul R (GroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_one' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_one_eq_zero p,
          MulZeroClass.mul_zero]
      mul_le' := fun _ _ =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul]
        exact
          (mul_le_mul_of_nonneg_left (map_mul_le_add p _ _) <| NNReal.coe_nonneg _).trans_eq
            (mul_add _ _ _)
      inv' := fun x => by rw [map_inv_eq_map p] }⟩

@[to_additive AddGroupSeminorm.isScalarTower]
instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (GroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

/- warning: group_seminorm.coe_smul -> GroupSeminorm.coe_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : Group.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (SMulZeroClass.toHasSmul.{0, 0} NNReal Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (SMulWithZero.toSmulZeroClass.{0, 0} NNReal Real (MulZeroClass.toHasZero.{0} NNReal (MulZeroOneClass.toMulZeroClass.{0} NNReal (MonoidWithZero.toMulZeroOneClass.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (MulActionWithZero.toSMulWithZero.{0, 0} NNReal Real (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (Module.toMulActionWithZero.{0, 0} NNReal Real NNReal.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (NNReal.module.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (Semiring.toModule.{0} Real Real.semiring)))))) _inst_2] (r : R) (p : GroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (coeFn.{succ u2, succ u2} (GroupSeminorm.{u2} E _inst_1) (fun (_x : GroupSeminorm.{u2} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u2} E _inst_1) (SMul.smul.{u1, u2} R (GroupSeminorm.{u2} E _inst_1) (GroupSeminorm.hasSmul.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4) r p)) (SMul.smul.{u1, u2} R (E -> Real) (Function.hasSMul.{u2, u1, 0} E R Real _inst_2) r (coeFn.{succ u2, succ u2} (GroupSeminorm.{u2} E _inst_1) (fun (_x : GroupSeminorm.{u2} E _inst_1) => E -> Real) (GroupSeminorm.hasCoeToFun.{u2} E _inst_1) p))
but is expected to have type
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : Group.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (Algebra.toSMul.{0, 0} NNReal Real instNNRealCommSemiring Real.semiring (NNReal.instAlgebraNNRealInstNNRealCommSemiring.{0} Real Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) _inst_2] (r : R) (p : GroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (FunLike.coe.{succ u2, succ u2, 1} (GroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u2, u2, 0} (GroupSeminorm.{u2} E _inst_1) E Real (MulOneClass.toMul.{u2} E (Monoid.toMulOneClass.{u2} E (DivInvMonoid.toMonoid.{u2} E (Group.toDivInvMonoid.{u2} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u2, 0} (GroupSeminorm.{u2} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u2} E _inst_1))) (HSMul.hSMul.{u1, u2, u2} R (GroupSeminorm.{u2} E _inst_1) (GroupSeminorm.{u2} E _inst_1) (instHSMul.{u1, u2} R (GroupSeminorm.{u2} E _inst_1) (GroupSeminorm.instSMulGroupSeminorm.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4)) r p)) (HSMul.hSMul.{u1, u2, u2} R (E -> Real) (E -> Real) (instHSMul.{u1, u2} R (E -> Real) (Pi.instSMul.{u2, 0, u1} E R (fun (a : E) => Real) (fun (i : E) => _inst_2))) r (FunLike.coe.{succ u2, succ u2, 1} (GroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (MulLEAddHomClass.toFunLike.{u2, u2, 0} (GroupSeminorm.{u2} E _inst_1) E Real (MulOneClass.toMul.{u2} E (Monoid.toMulOneClass.{u2} E (DivInvMonoid.toMonoid.{u2} E (Group.toDivInvMonoid.{u2} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u2, u2, 0} (GroupSeminorm.{u2} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u2} E _inst_1))) p))
Case conversion may be inaccurate. Consider using '#align group_seminorm.coe_smul GroupSeminorm.coe_smulₓ'. -/
@[simp, to_additive AddGroupSeminorm.coe_smul, norm_cast]
theorem coe_smul (r : R) (p : GroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align group_seminorm.coe_smul GroupSeminorm.coe_smul
#align add_group_seminorm.coe_smul AddGroupSeminorm.coe_smul

#print GroupSeminorm.smul_apply /-
@[simp, to_additive AddGroupSeminorm.smul_apply]
theorem smul_apply (r : R) (p : GroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align group_seminorm.smul_apply GroupSeminorm.smul_apply
#align add_group_seminorm.smul_apply AddGroupSeminorm.smul_apply
-/

#print GroupSeminorm.smul_sup /-
@[to_additive AddGroupSeminorm.smul_sup]
theorem smul_sup (r : R) (p q : GroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align group_seminorm.smul_sup GroupSeminorm.smul_sup
#align add_group_seminorm.smul_sup AddGroupSeminorm.smul_sup
-/

end GroupSeminorm

namespace NonarchAddGroupSeminorm

variable [AddGroup E] [SMul R ℝ] [SMul R ℝ≥0] [IsScalarTower R ℝ≥0 ℝ]

instance [DecidableEq E] : One (NonarchAddGroupSeminorm E) :=
  ⟨{  toFun := fun x => if x = 0 then 0 else 1
      map_zero' := if_pos rfl
      add_le_max' := fun x y => by
        by_cases hx : x = 0
        · rw [if_pos hx, hx, zero_add]
          exact le_max_of_le_right (le_refl _)
        · rw [if_neg hx]
          split_ifs <;> norm_num
      neg' := fun x => by simp_rw [neg_eq_zero] }⟩

/- warning: nonarch_add_group_seminorm.apply_one -> NonarchAddGroupSeminorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 1 (One.one.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (_inst_5 x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_5 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (OfNat.ofNat.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) (NonarchAddGroupSeminorm.instOneNonarchAddGroupSeminorm.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_5 a b)))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (_inst_5 x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.apply_one NonarchAddGroupSeminorm.apply_oneₓ'. -/
@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupSeminorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_seminorm.apply_one NonarchAddGroupSeminorm.apply_one

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a `nonarch_add_group_seminorm`. -/
instance : SMul R (NonarchAddGroupSeminorm E) :=
  ⟨fun r p =>
    { toFun := fun x => r • p x
      map_zero' := by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, map_zero p,
          MulZeroClass.mul_zero]
      add_le_max' := fun x y =>
        by
        simp only [← smul_one_smul ℝ≥0 r (_ : ℝ), NNReal.smul_def, smul_eq_mul, ←
          mul_max_of_nonneg _ _ NNReal.zero_le_coe]
        exact mul_le_mul_of_nonneg_left (map_add_le_max p _ _) NNReal.zero_le_coe
      neg' := fun x => by rw [map_neg_eq_map p] }⟩

instance [SMul R' ℝ] [SMul R' ℝ≥0] [IsScalarTower R' ℝ≥0 ℝ] [SMul R R'] [IsScalarTower R R' ℝ] :
    IsScalarTower R R' (NonarchAddGroupSeminorm E) :=
  ⟨fun r a p => ext fun x => smul_assoc r a <| p x⟩

/- warning: nonarch_add_group_seminorm.coe_smul -> NonarchAddGroupSeminorm.coe_smul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (SMulZeroClass.toHasSmul.{0, 0} NNReal Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (SMulWithZero.toSmulZeroClass.{0, 0} NNReal Real (MulZeroClass.toHasZero.{0} NNReal (MulZeroOneClass.toMulZeroClass.{0} NNReal (MonoidWithZero.toMulZeroOneClass.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (MulActionWithZero.toSMulWithZero.{0, 0} NNReal Real (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (Module.toMulActionWithZero.{0, 0} NNReal Real NNReal.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (NNReal.module.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (Semiring.toModule.{0} Real Real.semiring)))))) _inst_2] (r : R) (p : NonarchAddGroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (coeFn.{succ u2, succ u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u2} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) (SMul.smul.{u1, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.hasSmul.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4) r p)) (SMul.smul.{u1, u2} R (E -> Real) (Function.hasSMul.{u2, u1, 0} E R Real _inst_2) r (coeFn.{succ u2, succ u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u2} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) p))
but is expected to have type
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (Algebra.toSMul.{0, 0} NNReal Real instNNRealCommSemiring Real.semiring (NNReal.instAlgebraNNRealInstNNRealCommSemiring.{0} Real Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) _inst_2] (r : R) (p : NonarchAddGroupSeminorm.{u2} E _inst_1), Eq.{succ u2} (E -> Real) (FunLike.coe.{succ u2, succ u2, 1} (NonarchAddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u2, 0} (NonarchAddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u2} E _inst_1))) (HSMul.hSMul.{u1, u2, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.{u2} E _inst_1) (instHSMul.{u1, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.instSMulNonarchAddGroupSeminorm.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4)) r p)) (HSMul.hSMul.{u1, u2, u2} R (E -> Real) (E -> Real) (instHSMul.{u1, u2} R (E -> Real) (Pi.instSMul.{u2, 0, u1} E R (fun (a : E) => Real) (fun (i : E) => _inst_2))) r (FunLike.coe.{succ u2, succ u2, 1} (NonarchAddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u2, 0} (NonarchAddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u2} E _inst_1))) p))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.coe_smul NonarchAddGroupSeminorm.coe_smulₓ'. -/
@[simp, norm_cast]
theorem coe_smul (r : R) (p : NonarchAddGroupSeminorm E) : ⇑(r • p) = r • p :=
  rfl
#align nonarch_add_group_seminorm.coe_smul NonarchAddGroupSeminorm.coe_smul

/- warning: nonarch_add_group_seminorm.smul_apply -> NonarchAddGroupSeminorm.smul_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (SMulZeroClass.toHasSmul.{0, 0} NNReal Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (SMulWithZero.toSmulZeroClass.{0, 0} NNReal Real (MulZeroClass.toHasZero.{0} NNReal (MulZeroOneClass.toMulZeroClass.{0} NNReal (MonoidWithZero.toMulZeroOneClass.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (MulActionWithZero.toSMulWithZero.{0, 0} NNReal Real (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring) (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring)))))) (Module.toMulActionWithZero.{0, 0} NNReal Real NNReal.semiring (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (NNReal.module.{0} Real (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real Real.semiring))) (Semiring.toModule.{0} Real Real.semiring)))))) _inst_2] (r : R) (p : NonarchAddGroupSeminorm.{u2} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u2, succ u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u2} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) (SMul.smul.{u1, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.hasSmul.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4) r p) x) (SMul.smul.{u1, 0} R Real _inst_2 r (coeFn.{succ u2, succ u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) (fun (_x : NonarchAddGroupSeminorm.{u2} E _inst_1) => E -> Real) (NonarchAddGroupSeminorm.hasCoeToFun.{u2} E _inst_1) p x))
but is expected to have type
  forall {R : Type.{u1}} {E : Type.{u2}} [_inst_1 : AddGroup.{u2} E] [_inst_2 : SMul.{u1, 0} R Real] [_inst_3 : SMul.{u1, 0} R NNReal] [_inst_4 : IsScalarTower.{u1, 0, 0} R NNReal Real _inst_3 (Algebra.toSMul.{0, 0} NNReal Real instNNRealCommSemiring Real.semiring (NNReal.instAlgebraNNRealInstNNRealCommSemiring.{0} Real Real.semiring (Algebra.id.{0} Real Real.instCommSemiringReal))) _inst_2] (r : R) (p : NonarchAddGroupSeminorm.{u2} E _inst_1) (x : E), Eq.{1} Real (FunLike.coe.{succ u2, succ u2, 1} (NonarchAddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u2, 0} (NonarchAddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u2} E _inst_1))) (HSMul.hSMul.{u1, u2, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.{u2} E _inst_1) (instHSMul.{u1, u2} R (NonarchAddGroupSeminorm.{u2} E _inst_1) (NonarchAddGroupSeminorm.instSMulNonarchAddGroupSeminorm.{u1, u2} R E _inst_1 _inst_2 _inst_3 _inst_4)) r p) x) (HSMul.hSMul.{u1, 0, 0} R Real Real (instHSMul.{u1, 0} R Real _inst_2) r (FunLike.coe.{succ u2, succ u2, 1} (NonarchAddGroupSeminorm.{u2} E _inst_1) E (fun (_x : E) => Real) (NonarchimedeanHomClass.toFunLike.{u2, u2, 0} (NonarchAddGroupSeminorm.{u2} E _inst_1) E Real (AddZeroClass.toAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u2, u2} (NonarchAddGroupSeminorm.{u2} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u2} E _inst_1))) p x))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_seminorm.smul_apply NonarchAddGroupSeminorm.smul_applyₓ'. -/
@[simp]
theorem smul_apply (r : R) (p : NonarchAddGroupSeminorm E) (x : E) : (r • p) x = r • p x :=
  rfl
#align nonarch_add_group_seminorm.smul_apply NonarchAddGroupSeminorm.smul_apply

#print NonarchAddGroupSeminorm.smul_sup /-
theorem smul_sup (r : R) (p q : NonarchAddGroupSeminorm E) : r • (p ⊔ q) = r • p ⊔ r • q :=
  have real.smul_max : ∀ x y : ℝ, r • max x y = max (r • x) (r • y) := fun x y => by
    simpa only [← smul_eq_mul, ← NNReal.smul_def, smul_one_smul ℝ≥0 r (_ : ℝ)] using
      mul_max_of_nonneg x y (r • 1 : ℝ≥0).Prop
  ext fun x => real.smul_max _ _
#align nonarch_add_group_seminorm.smul_sup NonarchAddGroupSeminorm.smul_sup
-/

end NonarchAddGroupSeminorm

/-! ### Norms -/


namespace GroupNorm

section Group

variable [Group E] [Group F] [Group G] {p q : GroupNorm E}

#print GroupNorm.groupNormClass /-
@[to_additive]
instance groupNormClass : GroupNormClass (GroupNorm E) E ℝ
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_one_eq_zero f := f.map_one'
  map_mul_le_add f := f.mul_le'
  map_inv_eq_map f := f.inv'
  eq_one_of_map_eq_zero f := f.eq_one_of_map_eq_zero'
#align group_norm.group_norm_class GroupNorm.groupNormClass
#align add_group_norm.add_group_norm_class AddGroupNorm.addGroupNormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
@[to_additive
      "Helper instance for when there's too many metavariables to apply\n`fun_like.has_coe_to_fun` directly. "]
instance : CoeFun (GroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

/- warning: group_norm.to_fun_eq_coe -> GroupNorm.toGroupSeminorm_eq_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1}, Eq.{succ u1} (E -> Real) (GroupNorm.toFun.{u1} E _inst_1 p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1}, Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (GroupSeminorm.{u1} E _inst_1) E (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.956 : E) => Real) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupSeminorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupSeminorm.groupSeminormClass.{u1} E _inst_1))) (GroupNorm.toGroupSeminorm.{u1} E _inst_1 p)) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p)
Case conversion may be inaccurate. Consider using '#align group_norm.to_fun_eq_coe GroupNorm.toGroupSeminorm_eq_coeₓ'. -/
@[simp, to_additive]
theorem toGroupSeminorm_eq_coe : p.toFun = p :=
  rfl
#align group_norm.to_fun_eq_coe GroupNorm.toGroupSeminorm_eq_coe
#align add_group_norm.to_fun_eq_coe AddGroupNorm.toAddGroupSeminorm_eq_coe

/- warning: group_norm.ext -> GroupNorm.ext is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q x)) -> (Eq.{succ u1} (GroupNorm.{u1} E _inst_1) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q x)) -> (Eq.{succ u1} (GroupNorm.{u1} E _inst_1) p q)
Case conversion may be inaccurate. Consider using '#align group_norm.ext GroupNorm.extₓ'. -/
@[ext, to_additive]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align group_norm.ext GroupNorm.ext
#align add_group_norm.ext AddGroupNorm.ext

@[to_additive]
instance : PartialOrder (GroupNorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

/- warning: group_norm.le_def -> GroupNorm.le_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.partialOrder.{u1} E _inst_1))) p q) (LE.le.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instPartialOrderGroupNorm.{u1} E _inst_1))) p q) (LE.le.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align group_norm.le_def GroupNorm.le_defₓ'. -/
@[to_additive]
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align group_norm.le_def GroupNorm.le_def
#align add_group_norm.le_def AddGroupNorm.le_def

/- warning: group_norm.lt_def -> GroupNorm.lt_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.partialOrder.{u1} E _inst_1))) p q) (LT.lt.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instPartialOrderGroupNorm.{u1} E _inst_1))) p q) (LT.lt.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Preorder.toLT.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align group_norm.lt_def GroupNorm.lt_defₓ'. -/
@[to_additive]
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align group_norm.lt_def GroupNorm.lt_def
#align add_group_norm.lt_def AddGroupNorm.lt_def

/- warning: group_norm.coe_le_coe -> GroupNorm.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q)) (LE.le.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q)) (LE.le.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instPartialOrderGroupNorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align group_norm.coe_le_coe GroupNorm.coe_le_coeₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align group_norm.coe_le_coe GroupNorm.coe_le_coe
#align add_group_norm.coe_le_coe AddGroupNorm.coe_le_coe

/- warning: group_norm.coe_lt_coe -> GroupNorm.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q)) (LT.lt.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] {p : GroupNorm.{u1} E _inst_1} {q : GroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Preorder.toLT.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) a) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q)) (LT.lt.{u1} (GroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (GroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instPartialOrderGroupNorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align group_norm.coe_lt_coe GroupNorm.coe_lt_coeₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align group_norm.coe_lt_coe GroupNorm.coe_lt_coe
#align add_group_norm.coe_lt_coe AddGroupNorm.coe_lt_coe

variable (p q) (f : F →* E)

@[to_additive]
instance : Add (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm + q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| add_pos (map_pos_of_ne_one p h) (map_pos_of_ne_one q h) }⟩

/- warning: group_norm.coe_add -> GroupNorm.coe_add is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (instHAdd.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.hasAdd.{u1} E _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} (E -> Real) (E -> Real) (E -> Real) (instHAdd.{u1} (E -> Real) (Pi.instAdd.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasAdd))) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1), Eq.{succ u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) (HAdd.hAdd.{u1, u1, u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (instHAdd.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instAddGroupNorm.{u1} E _inst_1)) p q)) (HAdd.hAdd.{u1, u1, u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (instHAdd.{u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (Pi.instAdd.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instAddReal))) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align group_norm.coe_add GroupNorm.coe_addₓ'. -/
@[simp, to_additive]
theorem coe_add : ⇑(p + q) = p + q :=
  rfl
#align group_norm.coe_add GroupNorm.coe_add
#align add_group_norm.coe_add AddGroupNorm.coe_add

/- warning: group_norm.add_apply -> GroupNorm.add_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) (HAdd.hAdd.{u1, u1, u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (instHAdd.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.hasAdd.{u1} E _inst_1)) p q) x) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1) (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) (HAdd.hAdd.{u1, u1, u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (GroupNorm.{u1} E _inst_1) (instHAdd.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instAddGroupNorm.{u1} E _inst_1)) p q) x) (HAdd.hAdd.{0, 0, 0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (instHAdd.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instAddReal) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q x))
Case conversion may be inaccurate. Consider using '#align group_norm.add_apply GroupNorm.add_applyₓ'. -/
@[simp, to_additive]
theorem add_apply (x : E) : (p + q) x = p x + q x :=
  rfl
#align group_norm.add_apply GroupNorm.add_apply
#align add_group_norm.add_apply AddGroupNorm.add_apply

-- TODO: define `has_Sup`
@[to_additive]
instance : Sup (GroupNorm E) :=
  ⟨fun p q =>
    { p.toGroupSeminorm ⊔ q.toGroupSeminorm with
      eq_one_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_one p h }⟩

/- warning: group_norm.coe_sup -> GroupNorm.coe_sup is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.hasSup.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.hasSup.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasSup)) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1), Eq.{succ u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) (Sup.sup.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instSupGroupNorm.{u1} E _inst_1) p q)) (Sup.sup.{u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (Pi.instSupForAll.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) ᾰ) (fun (i : E) => Real.instSupReal)) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align group_norm.coe_sup GroupNorm.coe_supₓ'. -/
@[simp, to_additive, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align group_norm.coe_sup GroupNorm.coe_sup
#align add_group_norm.coe_sup AddGroupNorm.coe_sup

/- warning: group_norm.sup_apply -> GroupNorm.sup_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.hasSup.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.hasSup (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] (p : GroupNorm.{u1} E _inst_1) (q : GroupNorm.{u1} E _inst_1) (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) (Sup.sup.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.instSupGroupNorm.{u1} E _inst_1) p q) x) (Sup.sup.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instSupReal (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) q x))
Case conversion may be inaccurate. Consider using '#align group_norm.sup_apply GroupNorm.sup_applyₓ'. -/
@[simp, to_additive]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align group_norm.sup_apply GroupNorm.sup_apply
#align add_group_norm.sup_apply AddGroupNorm.sup_apply

@[to_additive]
instance : SemilatticeSup (GroupNorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

end Group

end GroupNorm

namespace AddGroupNorm

variable [AddGroup E] [DecidableEq E]

instance : One (AddGroupNorm E) :=
  ⟨{ (1 : AddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

/- warning: add_group_norm.apply_one -> AddGroupNorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_2 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (AddGroupNorm.{u1} E _inst_1) (fun (_x : AddGroupNorm.{u1} E _inst_1) => E -> Real) (AddGroupNorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (AddGroupNorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (AddGroupNorm.{u1} E _inst_1) 1 (One.one.{u1} (AddGroupNorm.{u1} E _inst_1) (AddGroupNorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_2 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_2 : DecidableEq.{succ u1} E] (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (AddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (SubadditiveHomClass.toFunLike.{u1, u1, 0} (AddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (AddGroupSeminormClass.toSubadditiveHomClass.{u1, u1, 0} (AddGroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (AddGroupNormClass.toAddGroupSeminormClass.{u1, u1, 0} (AddGroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (AddGroupNorm.addGroupNormClass.{u1} E _inst_1)))) (OfNat.ofNat.{u1} (AddGroupNorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (AddGroupNorm.{u1} E _inst_1) (AddGroupNorm.instOneAddGroupNorm.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_2 a b)))) x) (ite.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (_inst_2 x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instZeroReal)) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align add_group_norm.apply_one AddGroupNorm.apply_oneₓ'. -/
@[simp]
theorem apply_one (x : E) : (1 : AddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align add_group_norm.apply_one AddGroupNorm.apply_one

instance : Inhabited (AddGroupNorm E) :=
  ⟨1⟩

end AddGroupNorm

namespace GroupNorm

variable [Group E] [DecidableEq E]

@[to_additive AddGroupNorm.hasOne]
instance : One (GroupNorm E) :=
  ⟨{ (1 : GroupSeminorm E) with eq_one_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

/- warning: group_norm.apply_one -> GroupNorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] [_inst_2 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (GroupNorm.{u1} E _inst_1) (fun (_x : GroupNorm.{u1} E _inst_1) => E -> Real) (GroupNorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (GroupNorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (GroupNorm.{u1} E _inst_1) 1 (One.one.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_2 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))))) (_inst_2 x (OfNat.ofNat.{u1} E 1 (OfNat.mk.{u1} E 1 (One.one.{u1} E (MulOneClass.toHasOne.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : Group.{u1} E] [_inst_2 : DecidableEq.{succ u1} E] (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (GroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) _x) (MulLEAddHomClass.toFunLike.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real (MulOneClass.toMul.{u1} E (Monoid.toMulOneClass.{u1} E (DivInvMonoid.toMonoid.{u1} E (Group.toDivInvMonoid.{u1} E _inst_1)))) (AddZeroClass.toAdd.{0} Real (AddMonoid.toAddZeroClass.{0} Real (AddCommMonoid.toAddMonoid.{0} Real (OrderedAddCommMonoid.toAddCommMonoid.{0} Real Real.orderedAddCommMonoid)))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedAddCommMonoid.toPartialOrder.{0} Real Real.orderedAddCommMonoid))) (GroupSeminormClass.toMulLEAddHomClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNormClass.toGroupSeminormClass.{u1, u1, 0} (GroupNorm.{u1} E _inst_1) E Real _inst_1 Real.orderedAddCommMonoid (GroupNorm.groupNormClass.{u1} E _inst_1)))) (OfNat.ofNat.{u1} (GroupNorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (GroupNorm.{u1} E _inst_1) (GroupNorm.toOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_2 a b)))) x) (ite.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (Group.toDivisionMonoid.{u1} E _inst_1))))))) (_inst_2 x (OfNat.ofNat.{u1} E 1 (One.toOfNat1.{u1} E (InvOneClass.toOne.{u1} E (DivInvOneMonoid.toInvOneClass.{u1} E (DivisionMonoid.toDivInvOneMonoid.{u1} E (Group.toDivisionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instZeroReal)) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.6773 : E) => Real) x) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align group_norm.apply_one GroupNorm.apply_oneₓ'. -/
@[simp, to_additive AddGroupNorm.apply_one]
theorem apply_one (x : E) : (1 : GroupNorm E) x = if x = 1 then 0 else 1 :=
  rfl
#align group_norm.apply_one GroupNorm.apply_one
#align add_group_norm.apply_one AddGroupNorm.apply_one

@[to_additive]
instance : Inhabited (GroupNorm E) :=
  ⟨1⟩

end GroupNorm

namespace NonarchAddGroupNorm

section AddGroup

variable [AddGroup E] [AddGroup F] {p q : NonarchAddGroupNorm E}

#print NonarchAddGroupNorm.nonarchAddGroupNormClass /-
instance nonarchAddGroupNormClass : NonarchAddGroupNormClass (NonarchAddGroupNorm E) E
    where
  coe f := f.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_add_le_max f := f.add_le_max'
  map_zero f := f.map_zero'
  map_neg_eq_map' f := f.neg'
  eq_zero_of_map_eq_zero f := f.eq_zero_of_map_eq_zero'
#align nonarch_add_group_norm.nonarch_add_group_norm_class NonarchAddGroupNorm.nonarchAddGroupNormClass
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`. -/
noncomputable instance : CoeFun (NonarchAddGroupNorm E) fun _ => E → ℝ :=
  FunLike.hasCoeToFun

/- warning: nonarch_add_group_norm.to_fun_eq_coe -> NonarchAddGroupNorm.toNonarchAddGroupSeminorm_eq_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1}, Eq.{succ u1} (E -> Real) (NonarchAddGroupNorm.toFun.{u1} E _inst_1 p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1}, Eq.{succ u1} (E -> Real) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.4075 : E) => Real) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupSeminorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupSeminorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupSeminorm.nonarchAddGroupSeminormClass.{u1} E _inst_1))) (NonarchAddGroupNorm.toNonarchAddGroupSeminorm.{u1} E _inst_1 p)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.to_fun_eq_coe NonarchAddGroupNorm.toNonarchAddGroupSeminorm_eq_coeₓ'. -/
@[simp]
theorem toNonarchAddGroupSeminorm_eq_coe : p.toFun = p :=
  rfl
#align nonarch_add_group_norm.to_fun_eq_coe NonarchAddGroupNorm.toNonarchAddGroupSeminorm_eq_coe

/- warning: nonarch_add_group_norm.ext -> NonarchAddGroupNorm.ext is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q x)) -> (Eq.{succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, (forall (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q x)) -> (Eq.{succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.ext NonarchAddGroupNorm.extₓ'. -/
@[ext]
theorem ext : (∀ x, p x = q x) → p = q :=
  FunLike.ext p q
#align nonarch_add_group_norm.ext NonarchAddGroupNorm.ext

noncomputable instance : PartialOrder (NonarchAddGroupNorm E) :=
  PartialOrder.lift _ FunLike.coe_injective

/- warning: nonarch_add_group_norm.le_def -> NonarchAddGroupNorm.le_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.partialOrder.{u1} E _inst_1))) p q) (LE.le.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instPartialOrderNonarchAddGroupNorm.{u1} E _inst_1))) p q) (LE.le.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.le_def NonarchAddGroupNorm.le_defₓ'. -/
theorem le_def : p ≤ q ↔ (p : E → ℝ) ≤ q :=
  Iff.rfl
#align nonarch_add_group_norm.le_def NonarchAddGroupNorm.le_def

/- warning: nonarch_add_group_norm.lt_def -> NonarchAddGroupNorm.lt_def is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.partialOrder.{u1} E _inst_1))) p q) (LT.lt.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instPartialOrderNonarchAddGroupNorm.{u1} E _inst_1))) p q) (LT.lt.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Preorder.toLT.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.lt_def NonarchAddGroupNorm.lt_defₓ'. -/
theorem lt_def : p < q ↔ (p : E → ℝ) < q :=
  Iff.rfl
#align nonarch_add_group_norm.lt_def NonarchAddGroupNorm.lt_def

/- warning: nonarch_add_group_norm.coe_le_coe -> NonarchAddGroupNorm.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasLe)) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q)) (LE.le.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LE.le.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Pi.hasLe.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (fun (i : E) => Real.instLEReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q)) (LE.le.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLE.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instPartialOrderNonarchAddGroupNorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.coe_le_coe NonarchAddGroupNorm.coe_le_coeₓ'. -/
@[simp, norm_cast]
theorem coe_le_coe : (p : E → ℝ) ≤ q ↔ p ≤ q :=
  Iff.rfl
#align nonarch_add_group_norm.coe_le_coe NonarchAddGroupNorm.coe_le_coe

/- warning: nonarch_add_group_norm.coe_lt_coe -> NonarchAddGroupNorm.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Preorder.toLT.{u1} ((fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) p) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.preorder))) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q)) (LT.lt.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.partialOrder.{u1} E _inst_1))) p q)
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] {p : NonarchAddGroupNorm.{u1} E _inst_1} {q : NonarchAddGroupNorm.{u1} E _inst_1}, Iff (LT.lt.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Preorder.toLT.{u1} (forall (a : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) a) (Pi.preorder.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (fun (i : E) => Real.instPreorderReal))) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q)) (LT.lt.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (Preorder.toLT.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (PartialOrder.toPreorder.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instPartialOrderNonarchAddGroupNorm.{u1} E _inst_1))) p q)
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.coe_lt_coe NonarchAddGroupNorm.coe_lt_coeₓ'. -/
@[simp, norm_cast]
theorem coe_lt_coe : (p : E → ℝ) < q ↔ p < q :=
  Iff.rfl
#align nonarch_add_group_norm.coe_lt_coe NonarchAddGroupNorm.coe_lt_coe

variable (p q) (f : F →+ E)

instance : Sup (NonarchAddGroupNorm E) :=
  ⟨fun p q =>
    { p.toNonarchAddGroupSeminorm ⊔ q.toNonarchAddGroupSeminorm with
      eq_zero_of_map_eq_zero' := fun x hx =>
        of_not_not fun h => hx.not_gt <| lt_sup_iff.2 <| Or.inl <| map_pos_of_ne_zero p h }⟩

/- warning: nonarch_add_group_norm.coe_sup -> NonarchAddGroupNorm.coe_sup is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupNorm.{u1} E _inst_1) (q : NonarchAddGroupNorm.{u1} E _inst_1), Eq.{succ u1} (E -> Real) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.hasSup.{u1} E _inst_1) p q)) (Sup.sup.{u1} (E -> Real) (Pi.hasSup.{u1, 0} E (fun (ᾰ : E) => Real) (fun (i : E) => Real.hasSup)) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupNorm.{u1} E _inst_1) (q : NonarchAddGroupNorm.{u1} E _inst_1), Eq.{succ u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) (Sup.sup.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instSupNonarchAddGroupNorm.{u1} E _inst_1) p q)) (Sup.sup.{u1} (forall (ᾰ : E), (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (Pi.instSupForAll.{u1, 0} E (fun (ᾰ : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) ᾰ) (fun (i : E) => Real.instSupReal)) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.coe_sup NonarchAddGroupNorm.coe_supₓ'. -/
@[simp, norm_cast]
theorem coe_sup : ⇑(p ⊔ q) = p ⊔ q :=
  rfl
#align nonarch_add_group_norm.coe_sup NonarchAddGroupNorm.coe_sup

/- warning: nonarch_add_group_norm.sup_apply -> NonarchAddGroupNorm.sup_apply is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupNorm.{u1} E _inst_1) (q : NonarchAddGroupNorm.{u1} E _inst_1) (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) (Sup.sup.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.hasSup.{u1} E _inst_1) p q) x) (Sup.sup.{0} Real Real.hasSup (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) p x) (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) q x))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] (p : NonarchAddGroupNorm.{u1} E _inst_1) (q : NonarchAddGroupNorm.{u1} E _inst_1) (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) (Sup.sup.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instSupNonarchAddGroupNorm.{u1} E _inst_1) p q) x) (Sup.sup.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) Real.instSupReal (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) p x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) q x))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.sup_apply NonarchAddGroupNorm.sup_applyₓ'. -/
@[simp]
theorem sup_apply (x : E) : (p ⊔ q) x = p x ⊔ q x :=
  rfl
#align nonarch_add_group_norm.sup_apply NonarchAddGroupNorm.sup_apply

noncomputable instance : SemilatticeSup (NonarchAddGroupNorm E) :=
  FunLike.coe_injective.SemilatticeSup _ coe_sup

instance [DecidableEq E] : One (NonarchAddGroupNorm E) :=
  ⟨{ (1 : NonarchAddGroupSeminorm E) with
      eq_zero_of_map_eq_zero' := fun x => zero_ne_one.ite_eq_left_iff.1 }⟩

/- warning: nonarch_add_group_norm.apply_one -> NonarchAddGroupNorm.apply_one is a dubious translation:
lean 3 declaration is
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_3 : DecidableEq.{succ u1} E] (x : E), Eq.{1} Real (coeFn.{succ u1, succ u1} (NonarchAddGroupNorm.{u1} E _inst_1) (fun (_x : NonarchAddGroupNorm.{u1} E _inst_1) => E -> Real) (NonarchAddGroupNorm.hasCoeToFun.{u1} E _inst_1) (OfNat.ofNat.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) 1 (OfNat.mk.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) 1 (One.one.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.hasOne.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_3 a b))))) x) (ite.{1} Real (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (_inst_3 x (OfNat.ofNat.{u1} E 0 (OfNat.mk.{u1} E 0 (Zero.zero.{u1} E (AddZeroClass.toHasZero.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {E : Type.{u1}} [_inst_1 : AddGroup.{u1} E] [_inst_3 : DecidableEq.{succ u1} E] (x : E), Eq.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) (FunLike.coe.{succ u1, succ u1, 1} (NonarchAddGroupNorm.{u1} E _inst_1) E (fun (_x : E) => (fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) _x) (NonarchimedeanHomClass.toFunLike.{u1, u1, 0} (NonarchAddGroupNorm.{u1} E _inst_1) E Real (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E _inst_1)))) Real.linearOrder (NonarchAddGroupSeminormClass.toNonarchimedeanHomClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNormClass.toNonarchAddGroupSeminormClass.{u1, u1} (NonarchAddGroupNorm.{u1} E _inst_1) E _inst_1 (NonarchAddGroupNorm.nonarchAddGroupNormClass.{u1} E _inst_1)))) (OfNat.ofNat.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) 1 (One.toOfNat1.{u1} (NonarchAddGroupNorm.{u1} E _inst_1) (NonarchAddGroupNorm.instOneNonarchAddGroupNorm.{u1} E _inst_1 (fun (a : E) (b : E) => _inst_3 a b)))) x) (ite.{1} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (_inst_3 x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (AddGroup.toSubtractionMonoid.{u1} E _inst_1))))))) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) 0 (Zero.toOfNat0.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) Real.instZeroReal)) (OfNat.ofNat.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) 1 (One.toOfNat1.{0} ((fun (a._@.Mathlib.Analysis.Normed.Group.Seminorm._hyg.7934 : E) => Real) x) Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align nonarch_add_group_norm.apply_one NonarchAddGroupNorm.apply_oneₓ'. -/
@[simp]
theorem apply_one [DecidableEq E] (x : E) :
    (1 : NonarchAddGroupNorm E) x = if x = 0 then 0 else 1 :=
  rfl
#align nonarch_add_group_norm.apply_one NonarchAddGroupNorm.apply_one

instance [DecidableEq E] : Inhabited (NonarchAddGroupNorm E) :=
  ⟨1⟩

end AddGroup

end NonarchAddGroupNorm

