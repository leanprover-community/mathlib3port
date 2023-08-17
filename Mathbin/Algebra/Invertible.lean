/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.Group.Units
import Mathbin.Algebra.GroupWithZero.Units.Lemmas
import Mathbin.Algebra.Ring.Defs

#align_import algebra.invertible from "leanprover-community/mathlib"@"722b3b152ddd5e0cf21c0a29787c76596cb6b422"

/-!
# Invertible elements

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a typeclass `invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `is_unit`.

For constructions of the invertible element given a characteristic, see
`algebra/char_p/invertible` and other lemmas in that file.

## Notation

 * `⅟a` is `invertible.inv_of a`, the inverse of `a`

## Implementation notes

The `invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `invertible a` is not a `Prop` (but it is a `subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `invertible a` in the
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `invertible 1` instance:
```lean
variables {α : Type*} [monoid α]

def something_that_needs_inverses (x : α) [invertible x] := sorry

section
local attribute [instance] invertible_one
def something_one := something_that_needs_inverses 1
end
```

## Tags

invertible, inverse element, inv_of, a half, one half, a third, one third, ½, ⅓

-/


universe u

variable {α : Type u}

#print Invertible /-
/-- `invertible a` gives a two-sided multiplicative inverse of `a`. -/
class Invertible [Mul α] [One α] (a : α) : Type u where
  invOf : α
  invOf_hMul_self : inv_of * a = 1
  hMul_invOf_self : a * inv_of = 1
#align invertible Invertible
-/

notation:1034
  "⅟" =>-- This notation has the same precedence as `has_inv.inv`.
  Invertible.invOf

#print invOf_mul_self /-
@[simp]
theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟ a * a = 1 :=
  Invertible.invOf_hMul_self
#align inv_of_mul_self invOf_mul_self
-/

#print mul_invOf_self /-
@[simp]
theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟ a = 1 :=
  Invertible.hMul_invOf_self
#align mul_inv_of_self mul_invOf_self
-/

#print invOf_mul_self_assoc /-
@[simp]
theorem invOf_mul_self_assoc [Monoid α] (a b : α) [Invertible a] : ⅟ a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
#align inv_of_mul_self_assoc invOf_mul_self_assoc
-/

#print mul_invOf_self_assoc /-
@[simp]
theorem mul_invOf_self_assoc [Monoid α] (a b : α) [Invertible a] : a * (⅟ a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
#align mul_inv_of_self_assoc mul_invOf_self_assoc
-/

#print mul_invOf_mul_self_cancel /-
@[simp]
theorem mul_invOf_mul_self_cancel [Monoid α] (a b : α) [Invertible b] : a * ⅟ b * b = a := by
  simp [mul_assoc]
#align mul_inv_of_mul_self_cancel mul_invOf_mul_self_cancel
-/

#print mul_mul_invOf_self_cancel /-
@[simp]
theorem mul_mul_invOf_self_cancel [Monoid α] (a b : α) [Invertible b] : a * b * ⅟ b = a := by
  simp [mul_assoc]
#align mul_mul_inv_of_self_cancel mul_mul_invOf_self_cancel
-/

#print invOf_eq_right_inv /-
theorem invOf_eq_right_inv [Monoid α] {a b : α} [Invertible a] (hac : a * b = 1) : ⅟ a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac
#align inv_of_eq_right_inv invOf_eq_right_inv
-/

#print invOf_eq_left_inv /-
theorem invOf_eq_left_inv [Monoid α] {a b : α} [Invertible a] (hac : b * a = 1) : ⅟ a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm
#align inv_of_eq_left_inv invOf_eq_left_inv
-/

#print invertible_unique /-
theorem invertible_unique {α : Type u} [Monoid α] (a b : α) [Invertible a] [Invertible b]
    (h : a = b) : ⅟ a = ⅟ b := by apply invOf_eq_right_inv; rw [h, mul_invOf_self]
#align invertible_unique invertible_unique
-/

instance [Monoid α] (a : α) : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, hca, hac⟩ => by congr; exact left_inv_eq_right_inv hba hac⟩

#print Invertible.copy' /-
/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟ r) : Invertible s where
  invOf := si
  invOf_hMul_self := by rw [hs, hsi, invOf_mul_self]
  hMul_invOf_self := by rw [hs, hsi, mul_invOf_self]
#align invertible.copy' Invertible.copy'
-/

#print Invertible.copy /-
/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
@[reducible]
def Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl
#align invertible.copy Invertible.copy
-/

#print unitOfInvertible /-
/-- An `invertible` element is a unit. -/
@[simps]
def unitOfInvertible [Monoid α] (a : α) [Invertible a] : αˣ
    where
  val := a
  inv := ⅟ a
  val_inv := by simp
  inv_val := by simp
#align unit_of_invertible unitOfInvertible
-/

#print isUnit_of_invertible /-
theorem isUnit_of_invertible [Monoid α] (a : α) [Invertible a] : IsUnit a :=
  ⟨unitOfInvertible a, rfl⟩
#align is_unit_of_invertible isUnit_of_invertible
-/

#print Units.invertible /-
/-- Units are invertible in their associated monoid. -/
def Units.invertible [Monoid α] (u : αˣ) : Invertible (u : α)
    where
  invOf := ↑u⁻¹
  invOf_hMul_self := u.inv_mul
  hMul_invOf_self := u.mul_inv
#align units.invertible Units.invertible
-/

#print invOf_units /-
@[simp]
theorem invOf_units [Monoid α] (u : αˣ) [Invertible (u : α)] : ⅟ (u : α) = ↑u⁻¹ :=
  invOf_eq_right_inv u.mul_inv
#align inv_of_units invOf_units
-/

#print IsUnit.nonempty_invertible /-
theorem IsUnit.nonempty_invertible [Monoid α] {a : α} (h : IsUnit a) : Nonempty (Invertible a) :=
  let ⟨x, hx⟩ := h
  ⟨x.Invertible.copy _ hx.symm⟩
#align is_unit.nonempty_invertible IsUnit.nonempty_invertible
-/

#print IsUnit.invertible /-
/-- Convert `is_unit` to `invertible` using `classical.choice`.

Prefer `casesI h.nonempty_invertible` over `letI := h.invertible` if you want to avoid choice. -/
noncomputable def IsUnit.invertible [Monoid α] {a : α} (h : IsUnit a) : Invertible a :=
  Classical.choice h.nonempty_invertible
#align is_unit.invertible IsUnit.invertible
-/

#print nonempty_invertible_iff_isUnit /-
@[simp]
theorem nonempty_invertible_iff_isUnit [Monoid α] (a : α) : Nonempty (Invertible a) ↔ IsUnit a :=
  ⟨Nonempty.ndrec <| @isUnit_of_invertible _ _ _, IsUnit.nonempty_invertible⟩
#align nonempty_invertible_iff_is_unit nonempty_invertible_iff_isUnit
-/

#print invertibleOfGroup /-
/-- Each element of a group is invertible. -/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_self a, mul_inv_self a⟩
#align invertible_of_group invertibleOfGroup
-/

#print invOf_eq_group_inv /-
@[simp]
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_self a)
#align inv_of_eq_group_inv invOf_eq_group_inv
-/

#print invertibleOne /-
/-- `1` is the inverse of itself -/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩
#align invertible_one invertibleOne
-/

#print invOf_one /-
@[simp]
theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟ (1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)
#align inv_of_one invOf_one
-/

#print invertibleNeg /-
/-- `-⅟a` is the inverse of `-a` -/
def invertibleNeg [Mul α] [One α] [HasDistribNeg α] (a : α) [Invertible a] : Invertible (-a) :=
  ⟨-⅟ a, by simp, by simp⟩
#align invertible_neg invertibleNeg
-/

#print invOf_neg /-
@[simp]
theorem invOf_neg [Monoid α] [HasDistribNeg α] (a : α) [Invertible a] [Invertible (-a)] :
    ⅟ (-a) = -⅟ a :=
  invOf_eq_right_inv (by simp)
#align inv_of_neg invOf_neg
-/

#print one_sub_invOf_two /-
@[simp]
theorem one_sub_invOf_two [Ring α] [Invertible (2 : α)] : 1 - (⅟ 2 : α) = ⅟ 2 :=
  (isUnit_of_invertible (2 : α)).mul_right_inj.1 <| by
    rw [mul_sub, mul_invOf_self, mul_one, bit0, add_sub_cancel]
#align one_sub_inv_of_two one_sub_invOf_two
-/

#print invOf_two_add_invOf_two /-
@[simp]
theorem invOf_two_add_invOf_two [NonAssocSemiring α] [Invertible (2 : α)] :
    (⅟ 2 : α) + (⅟ 2 : α) = 1 := by rw [← two_mul, mul_invOf_self]
#align inv_of_two_add_inv_of_two invOf_two_add_invOf_two
-/

#print invertibleInvOf /-
/-- `a` is the inverse of `⅟a`. -/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟ a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩
#align invertible_inv_of invertibleInvOf
-/

#print invOf_invOf /-
@[simp]
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟ a)] : ⅟ (⅟ a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)
#align inv_of_inv_of invOf_invOf
-/

#print invOf_inj /-
@[simp]
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟ a = ⅟ b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩
#align inv_of_inj invOf_inj
-/

#print invertibleMul /-
/-- `⅟b * ⅟a` is the inverse of `a * b` -/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟ b * ⅟ a, by simp [← mul_assoc], by simp [← mul_assoc]⟩
#align invertible_mul invertibleMul
-/

#print invOf_mul /-
@[simp]
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟ (a * b) = ⅟ b * ⅟ a :=
  invOf_eq_right_inv (by simp [← mul_assoc])
#align inv_of_mul invOf_mul
-/

#print Invertible.mul /-
/-- A copy of `invertible_mul` for dot notation. -/
@[reducible]
def Invertible.mul [Monoid α] {a b : α} (ha : Invertible a) (hb : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _
#align invertible.mul Invertible.mul
-/

#print Commute.invOf_right /-
theorem Commute.invOf_right [Monoid α] {a b : α} [Invertible b] (h : Commute a b) :
    Commute a (⅟ b) :=
  calc
    a * ⅟ b = ⅟ b * (b * a * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (a * b * ⅟ b) := by rw [h.eq]
    _ = ⅟ b * a := by simp [mul_assoc]
#align commute.inv_of_right Commute.invOf_right
-/

#print Commute.invOf_left /-
theorem Commute.invOf_left [Monoid α] {a b : α} [Invertible b] (h : Commute b a) :
    Commute (⅟ b) a :=
  calc
    ⅟ b * a = ⅟ b * (a * b * ⅟ b) := by simp [mul_assoc]
    _ = ⅟ b * (b * a * ⅟ b) := by rw [h.eq]
    _ = a * ⅟ b := by simp [mul_assoc]
#align commute.inv_of_left Commute.invOf_left
-/

#print commute_invOf /-
theorem commute_invOf {M : Type _} [One M] [Mul M] (m : M) [Invertible m] : Commute m (⅟ m) :=
  calc
    m * ⅟ m = 1 := mul_invOf_self m
    _ = ⅟ m * m := (invOf_mul_self m).symm
#align commute_inv_of commute_invOf
-/

#print nonzero_of_invertible /-
theorem nonzero_of_invertible [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 :=
  fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟ a * a := by simp [ha]
      _ = 1 := invOf_mul_self a
#align nonzero_of_invertible nonzero_of_invertible
-/

#print Invertible.ne_zero /-
instance (priority := 100) Invertible.ne_zero [MulZeroOneClass α] [Nontrivial α] (a : α)
    [Invertible a] : NeZero a :=
  ⟨nonzero_of_invertible a⟩
#align invertible.ne_zero Invertible.ne_zero
-/

section Monoid

variable [Monoid α]

#print invertibleOfInvertibleMul /-
/-- This is the `invertible` version of `units.is_unit_units_mul` -/
@[reducible]
def invertibleOfInvertibleMul (a b : α) [Invertible a] [Invertible (a * b)] : Invertible b
    where
  invOf := ⅟ (a * b) * a
  invOf_hMul_self := by rw [mul_assoc, invOf_mul_self]
  hMul_invOf_self := by
    rw [← (isUnit_of_invertible a).mul_right_inj, ← mul_assoc, ← mul_assoc, mul_invOf_self, mul_one,
      one_mul]
#align invertible_of_invertible_mul invertibleOfInvertibleMul
-/

#print invertibleOfMulInvertible /-
/-- This is the `invertible` version of `units.is_unit_mul_units` -/
@[reducible]
def invertibleOfMulInvertible (a b : α) [Invertible (a * b)] [Invertible b] : Invertible a
    where
  invOf := b * ⅟ (a * b)
  invOf_hMul_self := by
    rw [← (isUnit_of_invertible b).mul_left_inj, mul_assoc, mul_assoc, invOf_mul_self, mul_one,
      one_mul]
  hMul_invOf_self := by rw [← mul_assoc, mul_invOf_self]
#align invertible_of_mul_invertible invertibleOfMulInvertible
-/

#print Invertible.mulLeft /-
/-- `invertible_of_invertible_mul` and `invertible_mul` as an equivalence. -/
@[simps]
def Invertible.mulLeft {a : α} (ha : Invertible a) (b : α) : Invertible b ≃ Invertible (a * b)
    where
  toFun hb := invertibleMul a b
  invFun hab := invertibleOfInvertibleMul a _
  left_inv hb := Subsingleton.elim _ _
  right_inv hab := Subsingleton.elim _ _
#align invertible.mul_left Invertible.mulLeft
-/

#print Invertible.mulRight /-
/-- `invertible_of_mul_invertible` and `invertible_mul` as an equivalence. -/
@[simps]
def Invertible.mulRight (a : α) {b : α} (ha : Invertible b) : Invertible a ≃ Invertible (a * b)
    where
  toFun hb := invertibleMul a b
  invFun hab := invertibleOfMulInvertible _ b
  left_inv hb := Subsingleton.elim _ _
  right_inv hab := Subsingleton.elim _ _
#align invertible.mul_right Invertible.mulRight
-/

end Monoid

section MonoidWithZero

variable [MonoidWithZero α]

#print Ring.inverse_invertible /-
/-- A variant of `ring.inverse_unit`. -/
@[simp]
theorem Ring.inverse_invertible (x : α) [Invertible x] : Ring.inverse x = ⅟ x :=
  Ring.inverse_unit (unitOfInvertible _)
#align ring.inverse_invertible Ring.inverse_invertible
-/

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero α]

#print invertibleOfNonzero /-
/-- `a⁻¹` is an inverse of `a` if `a ≠ 0` -/
def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel h, mul_inv_cancel h⟩
#align invertible_of_nonzero invertibleOfNonzero
-/

#print invOf_eq_inv /-
@[simp]
theorem invOf_eq_inv (a : α) [Invertible a] : ⅟ a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel (nonzero_of_invertible a))
#align inv_of_eq_inv invOf_eq_inv
-/

#print inv_mul_cancel_of_invertible /-
@[simp]
theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 :=
  inv_mul_cancel (nonzero_of_invertible a)
#align inv_mul_cancel_of_invertible inv_mul_cancel_of_invertible
-/

#print mul_inv_cancel_of_invertible /-
@[simp]
theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 :=
  mul_inv_cancel (nonzero_of_invertible a)
#align mul_inv_cancel_of_invertible mul_inv_cancel_of_invertible
-/

#print div_mul_cancel_of_invertible /-
@[simp]
theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a :=
  div_mul_cancel a (nonzero_of_invertible b)
#align div_mul_cancel_of_invertible div_mul_cancel_of_invertible
-/

#print mul_div_cancel_of_invertible /-
@[simp]
theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a :=
  mul_div_cancel a (nonzero_of_invertible b)
#align mul_div_cancel_of_invertible mul_div_cancel_of_invertible
-/

#print div_self_of_invertible /-
@[simp]
theorem div_self_of_invertible (a : α) [Invertible a] : a / a = 1 :=
  div_self (nonzero_of_invertible a)
#align div_self_of_invertible div_self_of_invertible
-/

#print invertibleDiv /-
/-- `b / a` is the inverse of `a / b` -/
def invertibleDiv (a b : α) [Invertible a] [Invertible b] : Invertible (a / b) :=
  ⟨b / a, by simp [← mul_div_assoc], by simp [← mul_div_assoc]⟩
#align invertible_div invertibleDiv
-/

#print invOf_div /-
@[simp]
theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟ (a / b) = b / a :=
  invOf_eq_right_inv (by simp [← mul_div_assoc])
#align inv_of_div invOf_div
-/

#print invertibleInv /-
/-- `a` is the inverse of `a⁻¹` -/
def invertibleInv {a : α} [Invertible a] : Invertible a⁻¹ :=
  ⟨a, by simp, by simp⟩
#align invertible_inv invertibleInv
-/

end GroupWithZero

#print Invertible.map /-
/-- Monoid homs preserve invertibility. -/
def Invertible.map {R : Type _} {S : Type _} {F : Type _} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] : Invertible (f r)
    where
  invOf := f (⅟ r)
  invOf_hMul_self := by rw [← map_mul, invOf_mul_self, map_one]
  hMul_invOf_self := by rw [← map_mul, mul_invOf_self, map_one]
#align invertible.map Invertible.map
-/

#print map_invOf /-
/-- Note that the `invertible (f r)` argument can be satisfied by using `letI := invertible.map f r`
before applying this lemma. -/
theorem map_invOf {R : Type _} {S : Type _} {F : Type _} [MulOneClass R] [Monoid S]
    [MonoidHomClass F R S] (f : F) (r : R) [Invertible r] [Invertible (f r)] : f (⅟ r) = ⅟ (f r) :=
  by letI := Invertible.map f r; convert rfl
#align map_inv_of map_invOf
-/

#print Invertible.ofLeftInverse /-
/-- If a function `f : R → S` has a left-inverse that is a monoid hom,
  then `r : R` is invertible if `f r` is.

The inverse is computed as `g (⅟(f r))` -/
@[simps (config := { attrs := [] })]
def Invertible.ofLeftInverse {R : Type _} {S : Type _} {G : Type _} [MulOneClass R] [MulOneClass S]
    [MonoidHomClass G S R] (f : R → S) (g : G) (r : R) (h : Function.LeftInverse g f)
    [Invertible (f r)] : Invertible r :=
  (Invertible.map g (f r)).copy _ (h r).symm
#align invertible.of_left_inverse Invertible.ofLeftInverse
-/

#print invertibleEquivOfLeftInverse /-
/-- Invertibility on either side of a monoid hom with a left-inverse is equivalent. -/
@[simps]
def invertibleEquivOfLeftInverse {R : Type _} {S : Type _} {F G : Type _} [Monoid R] [Monoid S]
    [MonoidHomClass F R S] [MonoidHomClass G S R] (f : F) (g : G) (r : R)
    (h : Function.LeftInverse g f) : Invertible (f r) ≃ Invertible r
    where
  toFun _ := Invertible.ofLeftInverse f _ _ h
  invFun _ := Invertible.map f _
  left_inv x := Subsingleton.elim _ _
  right_inv x := Subsingleton.elim _ _
#align invertible_equiv_of_left_inverse invertibleEquivOfLeftInverse
-/

