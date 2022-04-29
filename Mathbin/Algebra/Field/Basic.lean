/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Algebra.Ring.Basic

/-!
# Fields and division rings

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `field_theory` folder.

## Main definitions

* `division_ring`: introduces the notion of a division ring as a `ring` such that `0 ≠ 1` and
  `a * a⁻¹ = 1` for `a ≠ 0`
* `field`: a division ring which is also a commutative ring.
* `is_field`: a predicate on a ring that it is a field, i.e. that the multiplication is commutative,
  that it has more than one element and that all non-zero elements have a multiplicative inverse.
  In contrast to `field`, which contains the data of a function associating to an element of the
  field its multiplicative inverse, this predicate only assumes the existence and can therefore more
  easily be used to e.g. transfer along ring isomorphisms.

## Implementation details

By convention `0⁻¹ = 0` in a field or division ring. This is due to the fact that working with total
functions has the advantage of not constantly having to check that `x ≠ 0` when writing `x⁻¹`. With
this convention in place, some statements like `(a + b) * c⁻¹ = a * c⁻¹ + b * c⁻¹` still remain
true, while others like the defining property `a * a⁻¹ = 1` need the assumption `a ≠ 0`. If you are
a beginner in using Lean and are confused by that, you can read more about why this convention is
taken in Kevin Buzzard's
[blogpost](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)

A division ring or field is an example of a `group_with_zero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `group_with_zero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/


open Set

universe u

variable {K : Type u}

/-- A `division_ring` is a `ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor Ringₓ DivInvMonoidₓ Nontrivial]
class DivisionRing (K : Type u) extends Ringₓ K, DivInvMonoidₓ K, Nontrivial K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0

section DivisionRing

variable [DivisionRing K] {a b : K}

/-- Every division ring is a `group_with_zero`. -/
-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toGroupWithZero : GroupWithZeroₓ K :=
  { ‹DivisionRing K›, (inferInstance : Semiringₓ K) with }

attribute [local simp] division_def mul_comm mul_assoc mul_left_commₓ mul_inv_cancel inv_mul_cancel

theorem one_div_neg_one_eq_neg_one : (1 : K) / -1 = -1 :=
  have : -1 * -1 = (1 : K) := by
    rw [neg_mul_neg, one_mulₓ]
  Eq.symm (eq_one_div_of_mul_eq_one this)

theorem one_div_neg_eq_neg_one_div (a : K) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by
      rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by
      rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by
      rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by
      rw [mul_neg, mul_oneₓ]
    

theorem div_neg_eq_neg_div (a b : K) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by
      rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by
      rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by
      rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by
      rw [mul_one_div]
    

theorem neg_div (a b : K) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul, mul_div_assoc, ← neg_eq_neg_one_mul]

@[field_simps]
theorem neg_div' (a b : K) : -(b / a) = -b / a := by
  simp [neg_div]

theorem neg_div_neg_eq (a b : K) : -a / -b = a / b := by
  rw [div_neg_eq_neg_div, neg_div, neg_negₓ]

@[simp]
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by
  rw [div_neg_eq_neg_div, div_self h]

@[simp]
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by
  rw [neg_div, div_self h]

@[field_simps]
theorem div_add_div_same (a b c : K) : a / c + b / c = (a + b) / c := by
  simpa only [div_eq_mul_inv] using (right_distrib a b c⁻¹).symm

theorem same_add_div {a b : K} (h : b ≠ 0) : (b + a) / b = 1 + a / b := by
  simpa only [← @div_self _ _ b h] using (div_add_div_same b a b).symm

theorem one_add_div {a b : K} (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm

theorem div_add_same {a b : K} (h : b ≠ 0) : (a + b) / b = a / b + 1 := by
  simpa only [← @div_self _ _ b h] using (div_add_div_same a b b).symm

theorem div_add_one {a b : K} (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm

theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, div_add_div_same, sub_eq_add_neg]

theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm

theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm

theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm

theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm

theorem neg_inv : -a⁻¹ = (-a)⁻¹ := by
  rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

theorem add_div (a b c : K) : (a + b) / c = a / c + b / c :=
  (div_add_div_same _ _ _).symm

theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

theorem div_neg (a : K) : a / -b = -(a / b) := by
  rw [← div_neg_eq_neg_div]

theorem inv_neg : (-a)⁻¹ = -a⁻¹ := by
  rw [neg_inv]

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  rw [left_distrib (1 / a), one_div_mul_cancel ha, right_distrib, one_mulₓ, mul_assoc, mul_one_div_cancel hb, mul_oneₓ,
    add_commₓ]

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  rw [mul_sub_left_distrib (1 / a), one_div_mul_cancel ha, mul_sub_right_distrib, one_mulₓ, mul_assoc,
    mul_one_div_cancel hb, mul_oneₓ]

theorem add_div_eq_mul_add_div (a b : K) {c : K} (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  (eq_div_iff_mul_eq hc).2 <| by
    rw [right_distrib, div_mul_cancel _ hc]

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.is_domain : IsDomain K :=
  { ‹DivisionRing K›,
    (by
      infer_instance : NoZeroDivisors K) with }

end DivisionRing

/-- A `field` is a `comm_ring` with multiplicative inverses for nonzero elements -/
@[protect_proj, ancestor CommRingₓ DivInvMonoidₓ Nontrivial]
class Field (K : Type u) extends CommRingₓ K, DivInvMonoidₓ K, Nontrivial K where
  mul_inv_cancel : ∀ {a : K}, a ≠ 0 → a * a⁻¹ = 1
  inv_zero : (0 : K)⁻¹ = 0

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.toDivisionRing : DivisionRing K :=
  { show Field K by
      infer_instance with }

/-- Every field is a `comm_group_with_zero`. -/
-- see Note [lower instance priority]
instance (priority := 100) Field.toCommGroupWithZero : CommGroupWithZero K :=
  { (_ : GroupWithZeroₓ K), ‹Field K› with }

attribute [local simp] mul_assoc mul_comm mul_left_commₓ

theorem div_add_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [← mul_div_mul_right _ b hd, ← mul_div_mul_left c d hb, div_add_div_same]

theorem one_div_add_one_div {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) := by
  rw [div_add_div _ _ ha hb, one_mulₓ, mul_oneₓ, add_commₓ]

@[field_simps]
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) := by
  simp only [sub_eq_add_neg]
  rw [neg_eq_neg_one_mul, ← mul_div_assoc, div_add_div _ _ hb hd, ← mul_assoc, mul_comm b, mul_assoc, ←
    neg_eq_neg_one_mul]

theorem inv_add_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, one_div_add_one_div ha hb]

theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mulₓ, mul_oneₓ]

@[field_simps]
theorem add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  simpa using div_add_div b a one_ne_zero hc

@[field_simps]
theorem sub_div' (a b c : K) (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc

@[field_simps]
theorem div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_commₓ, add_div', add_commₓ]

@[field_simps]
theorem div_sub' (a b c : K) (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]
instance (priority := 100) Field.is_domain : IsDomain K :=
  { DivisionRing.is_domain with }

end Field

section IsField

/-- A predicate to express that a ring is a field.

This is mainly useful because such a predicate does not contain data,
and can therefore be easily transported along ring isomorphisms.
Additionaly, this is useful when trying to prove that
a particular ring structure extends to a field. -/
structure IsField (R : Type u) [Ringₓ R] : Prop where
  exists_pair_ne : ∃ x y : R, x ≠ y
  mul_comm : ∀ x y : R, x * y = y * x
  mul_inv_cancel : ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1

/-- Transferring from field to is_field -/
theorem Field.to_is_field (R : Type u) [Field R] : IsField R :=
  { ‹Field R› with mul_inv_cancel := fun a ha => ⟨a⁻¹, Field.mul_inv_cancel ha⟩ }

@[simp]
theorem IsField.nontrivial {R : Type u} [Ringₓ R] (h : IsField R) : Nontrivial R :=
  ⟨h.exists_pair_ne⟩

@[simp]
theorem not_is_field_of_subsingleton (R : Type u) [Ringₓ R] [Subsingleton R] : ¬IsField R := fun h =>
  let ⟨x, y, h⟩ := h.exists_pair_ne
  h (Subsingleton.elimₓ _ _)

open Classical

/-- Transferring from is_field to field -/
noncomputable def IsField.toField {R : Type u} [Ringₓ R] (h : IsField R) : Field R :=
  { ‹Ringₓ R›, h with inv := fun a => if ha : a = 0 then 0 else Classical.some (IsField.mul_inv_cancel h ha),
    inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a ha => by
      convert Classical.some_spec (IsField.mul_inv_cancel h ha)
      exact dif_neg ha }

/-- For each field, and for each nonzero element of said field, there is a unique inverse.
Since `is_field` doesn't remember the data of an `inv` function and as such,
a lemma that there is a unique inverse could be useful.
-/
theorem uniq_inv_of_is_field (R : Type u) [Ringₓ R] (hf : IsField R) : ∀ x : R, x ≠ 0 → ∃! y : R, x * y = 1 := by
  intro x hx
  apply exists_unique_of_exists_of_unique
  · exact hf.mul_inv_cancel hx
    
  · intro y z hxy hxz
    calc y = y * (x * z) := by
        rw [hxz, mul_oneₓ]_ = x * y * z := by
        rw [← mul_assoc, hf.mul_comm y x]_ = z := by
        rw [hxy, one_mulₓ]
    

end IsField

namespace RingHom

section

variable {R : Type _} [Semiringₓ R] [DivisionRing K] (f : R →+* K)

@[simp]
theorem map_units_inv (u : Rˣ) : f ↑u⁻¹ = (f ↑u)⁻¹ :=
  (f : R →* K).map_units_inv u

end

section

variable {R K' : Type _} [DivisionRing K] [Semiringₓ R] [Nontrivial R] [DivisionRing K'] (f : K →+* R) (g : K →+* K')
  {x y : K}

theorem map_ne_zero : f x ≠ 0 ↔ x ≠ 0 :=
  f.toMonoidWithZeroHom.map_ne_zero

@[simp]
theorem map_eq_zero : f x = 0 ↔ x = 0 :=
  f.toMonoidWithZeroHom.map_eq_zero

variable (x y)

theorem map_inv : g x⁻¹ = (g x)⁻¹ :=
  g.toMonoidWithZeroHom.map_inv x

theorem map_div : g (x / y) = g x / g y :=
  g.toMonoidWithZeroHom.map_div x y

protected theorem injective : Function.Injective f :=
  (injective_iff_map_eq_zero f).2 fun x => f.map_eq_zero.1

end

end RingHom

section NoncomputableDefs

variable {R : Type _} [Nontrivial R]

/-- Constructs a `division_ring` structure on a `ring` consisting only of units and 0. -/
noncomputable def divisionRingOfIsUnitOrEqZero [hR : Ringₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : DivisionRing R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

/-- Constructs a `field` structure on a `comm_ring` consisting only of units and 0.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def fieldOfIsUnitOrEqZero [hR : CommRingₓ R] (h : ∀ a : R, IsUnit a ∨ a = 0) : Field R :=
  { groupWithZeroOfIsUnitOrEqZero h, hR with }

end NoncomputableDefs

/-- Pullback a `division_ring` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.divisionRing [DivisionRing K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K']
    [One K'] [Inv K'] [Div K'] [HasScalar ℕ K'] [HasScalar ℤ K'] [Pow K' ℕ] [Pow K' ℤ] (f : K' → K)
    (hf : Function.Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n)
    (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : DivisionRing K' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.Ring f zero one add mul neg sub nsmul zsmul npow with }

/-- Pullback a `field` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.field [Field K] {K'} [Zero K'] [Mul K'] [Add K'] [Neg K'] [Sub K'] [One K'] [Inv K']
    [Div K'] [HasScalar ℕ K'] [HasScalar ℤ K'] [Pow K' ℕ] [Pow K' ℤ] (f : K' → K) (hf : Function.Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n)
    (zpow : ∀ x n : ℤ, f (x ^ n) = f x ^ n) : Field K' :=
  { hf.CommGroupWithZero f zero one mul inv div npow zpow,
    hf.CommRing f zero one add mul neg sub nsmul zsmul npow with }

