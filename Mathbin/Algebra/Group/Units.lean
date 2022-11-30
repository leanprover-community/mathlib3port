/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathbin.Algebra.Group.Basic
import Mathbin.Logic.Unique
import Mathbin.Tactic.Nontriviality

/-!
# Units (i.e., invertible elements) of a monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/549
> Any changes to this file require a corresponding PR to mathlib4.

An element of a `monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `units M`: the group of units (i.e., invertible elements) of a monoid.
* `is_unit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `add_units` and `is_add_unit`.

## Notation

We provide `Mˣ` as notation for `units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/


open Function

universe u

variable {α : Type u}

#print Units /-
/-- Units of a `monoid`, bundled version. Notation: `αˣ`.

An element of a `monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_unit`. -/
structure Units (α : Type u) [Monoid α] where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1
#align units Units
-/

-- mathport name: «expr ˣ»
postfix:1024 "ˣ" => Units

#print AddUnits /-
-- We don't provide notation for the additive version, because its use is somewhat rare.
/-- Units of an `add_monoid`, bundled version.

An element of an `add_monoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_add_unit`. -/
structure AddUnits (α : Type u) [AddMonoid α] where
  val : α
  neg : α
  val_neg : val + neg = 0
  neg_val : neg + val = 0
#align add_units AddUnits
-/

attribute [to_additive] Units

section HasElem

#print unique_one /-
@[to_additive]
theorem unique_one {α : Type _} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1
#align unique_has_one unique_one
-/

end HasElem

namespace Units

variable [Monoid α]

@[to_additive]
instance : Coe αˣ α :=
  ⟨val⟩

@[to_additive]
instance : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩

/- warning: units.simps.coe clashes with [anonymous] -> [anonymous]
warning: units.simps.coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α], (Units.{u} α _inst_1) -> α
but is expected to have type
  forall {B : Sort.{u}} {n : Nat}, ((Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> B) -> (forall (m : Nat), (Eq.{1} Nat n (Nat.succ m)) -> B) -> B
Case conversion may be inaccurate. Consider using '#align units.simps.coe [anonymous]ₓ'. -/
/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection] "]
def [anonymous] (u : αˣ) : α :=
  u
#align units.simps.coe[anonymous]

/- warning: units.simps.coe_inv clashes with [anonymous] -> [anonymous]
warning: units.simps.coe_inv -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α], (Units.{u} α _inst_1) -> α
but is expected to have type
  forall {B : Sort.{u}} {n : Nat}, ((Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> B) -> (forall (m : Nat), (Eq.{1} Nat n (Nat.succ m)) -> B) -> B
Case conversion may be inaccurate. Consider using '#align units.simps.coe_inv [anonymous]ₓ'. -/
/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection] "]
def [anonymous] (u : αˣ) : α :=
  ↑u⁻¹
#align units.simps.coe_inv[anonymous]

initialize_simps_projections Units (val → coe as_prefix, inv → CoeInv as_prefix)

initialize_simps_projections AddUnits (val → coe as_prefix, neg → CoeNeg as_prefix)

/- warning: units.coe_mk -> Units.val_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (b : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a b) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) b a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Units.mk.{u} α _inst_1 a b h₁ h₂)) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.809 : Monoid.{u} α] (a : α) (b : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809))) a b) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809)))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809))) b a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809)))), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809 (Units.mk.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.809 a b h₁ h₂)) a
Case conversion may be inaccurate. Consider using '#align units.coe_mk Units.val_mkₓ'. -/
@[simp, to_additive]
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl
#align units.coe_mk Units.val_mk

#print Units.ext /-
@[ext, to_additive]
theorem ext : Function.Injective (coe : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    change v = v' at e <;> subst v' <;> congr <;>
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁
#align units.ext Units.ext
-/

#print Units.eq_iff /-
@[norm_cast, to_additive]
theorem eq_iff {a b : αˣ} : (a : α) = b ↔ a = b :=
  ext.eq_iff
#align units.eq_iff Units.eq_iff
-/

#print Units.ext_iff /-
@[to_additive]
theorem ext_iff {a b : αˣ} : a = b ↔ (a : α) = b :=
  eq_iff.symm
#align units.ext_iff Units.ext_iff
-/

@[to_additive]
instance [DecidableEq α] : DecidableEq αˣ := fun a b => decidable_of_iff' _ ext_iff

/- warning: units.mk_coe -> Units.mk_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u : Units.{u} α _inst_1) (y : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) y) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) y ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))), Eq.{succ u} (Units.{u} α _inst_1) (Units.mk.{u} α _inst_1 ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) y h₁ h₂) u
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1051 : Monoid.{u} α] (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051) (y : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051 u) y) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051)))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051))) y (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051 u)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051)))), Eq.{succ u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051) (Units.mk.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051 (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1051 u) y h₁ h₂) u
Case conversion may be inaccurate. Consider using '#align units.mk_coe Units.mk_valₓ'. -/
@[simp, to_additive]
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl
#align units.mk_coe Units.mk_val

#print Units.copy /-
/-- Copy a unit, adjusting definition equalities. -/
@[to_additive "Copy an `add_unit`, adjusting definitional equalities.", simps]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val, inv, inv_val := hv.symm ▸ hi.symm ▸ u.inv_val, val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }
#align units.copy Units.copy
-/

#print Units.copy_eq /-
@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv
#align units.copy_eq Units.copy_eq
-/

@[to_additive]
instance :
    MulOneClass
      αˣ where 
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv, by
      rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv], by
      rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩
  one := ⟨1, 1, one_mul 1, one_mul 1⟩
  one_mul u := ext <| one_mul u
  mul_one u := ext <| mul_one u

/-- Units of a monoid form a group. -/
@[to_additive "Additive units of an additive monoid form an additive group."]
instance : Group αˣ :=
  { Units.mulOneClass with mul := (· * ·), one := 1,
    mul_assoc := fun u₁ u₂ u₃ => ext <| mul_assoc u₁ u₂ u₃, inv := Inv.inv,
    mul_left_inv := fun u => ext u.inv_val }

@[to_additive]
instance {α} [CommMonoid α] : CommGroup αˣ :=
  { Units.group with mul_comm := fun u₁ u₂ => ext <| mul_comm _ _ }

@[to_additive]
instance : Inhabited αˣ :=
  ⟨1⟩

@[to_additive]
instance [Repr α] : Repr αˣ :=
  ⟨repr ∘ val⟩

variable (a b c : αˣ) {u : αˣ}

/- warning: units.coe_mul -> Units.val_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) (b : Units.{u} α _inst_1), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (HMul.hMul.{u, u, u} (Units.{u} α _inst_1) (Units.{u} α _inst_1) (Units.{u} α _inst_1) (instHMul.{u} (Units.{u} α _inst_1) (MulOneClass.toHasMul.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1))) a b)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1546 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (b : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546 (HMul.hMul.{u, u, u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (instHMul.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (MulOneClass.toMul.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546) (Units.instMulOneClassUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546))) a b)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546 a) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1546 b))
Case conversion may be inaccurate. Consider using '#align units.coe_mul Units.val_mulₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl
#align units.coe_mul Units.val_mul

/- warning: units.coe_one -> Units.val_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α], Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (OfNat.ofNat.{u} (Units.{u} α _inst_1) 1 (OfNat.mk.{u} (Units.{u} α _inst_1) 1 (One.one.{u} (Units.{u} α _inst_1) (MulOneClass.toHasOne.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1)))))) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1588 : Monoid.{u} α], Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588 (OfNat.ofNat.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) 1 (One.toOfNat1.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) (InvOneClass.toOne.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) (DivInvOneMonoid.toInvOneClass.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) (DivisionMonoid.toDivInvOneMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) (Group.toDivisionMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588)))))))) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1588)))
Case conversion may be inaccurate. Consider using '#align units.coe_one Units.val_oneₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl
#align units.coe_one Units.val_one

/- warning: units.coe_eq_one -> Units.val_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {a : Units.{u} α _inst_1}, Iff (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} (Units.{u} α _inst_1) a (OfNat.ofNat.{u} (Units.{u} α _inst_1) 1 (OfNat.mk.{u} (Units.{u} α _inst_1) 1 (One.one.{u} (Units.{u} α _inst_1) (MulOneClass.toHasOne.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1627 : Monoid.{u} α] {a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627}, Iff (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627 a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627)))) (Eq.{succ u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) a (OfNat.ofNat.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) 1 (One.toOfNat1.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) (InvOneClass.toOne.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) (DivInvOneMonoid.toInvOneClass.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) (DivisionMonoid.toDivInvOneMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) (Group.toDivisionMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1627))))))))
Case conversion may be inaccurate. Consider using '#align units.coe_eq_one Units.val_eq_oneₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, eq_iff]
#align units.coe_eq_one Units.val_eq_one

/- warning: units.inv_mk -> Units.inv_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (x : α) (y : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) x y) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) y x) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))), Eq.{succ u} (Units.{u} α _inst_1) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) (Units.mk.{u} α _inst_1 x y h₁ h₂)) (Units.mk.{u} α _inst_1 y x h₂ h₁)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1700 : Monoid.{u} α] (x : α) (y : α) (h₁ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700))) x y) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700)))) (h₂ : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700))) y x) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700)))), Eq.{succ u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700) (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700) (Units.mk.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700 x y h₁ h₂)) (Units.mk.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1700 y x h₂ h₁)
Case conversion may be inaccurate. Consider using '#align units.inv_mk Units.inv_mkₓ'. -/
@[simp, to_additive]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl
#align units.inv_mk Units.inv_mk

/- warning: units.val_eq_coe clashes with [anonymous] -> [anonymous]
warning: units.val_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1), Eq.{succ u} α (Units.val.{u} α _inst_1 a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a)
but is expected to have type
  forall {B : Sort.{u}} {n : Nat}, ((Eq.{1} Nat n (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> B) -> (forall (m : Nat), (Eq.{1} Nat n (Nat.succ m)) -> B) -> B
Case conversion may be inaccurate. Consider using '#align units.val_eq_coe [anonymous]ₓ'. -/
@[simp, to_additive]
theorem [anonymous] : a.val = (↑a : α) :=
  rfl
#align units.val_eq_coe[anonymous]

#print Units.inv_eq_val_inv /-
@[simp, to_additive]
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl
#align units.inv_eq_coe_inv Units.inv_eq_val_inv
-/

/- warning: units.inv_mul -> Units.inv_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) a)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1791 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791) a)) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791 a)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1791)))
Case conversion may be inaccurate. Consider using '#align units.inv_mul Units.inv_mulₓ'. -/
@[simp, to_additive]
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _
#align units.inv_mul Units.inv_mul

/- warning: units.mul_inv -> Units.mul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) a))) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1835 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835 a) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835) a))) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1835)))
Case conversion may be inaccurate. Consider using '#align units.mul_inv Units.mul_invₓ'. -/
@[simp, to_additive]
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _
#align units.mul_inv Units.mul_inv

/- warning: units.inv_mul_of_eq -> Units.inv_mul_of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a) -> (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1879 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879} {a : α}, (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879 u) a) -> (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879) u)) a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1879))))
Case conversion may be inaccurate. Consider using '#align units.inv_mul_of_eq Units.inv_mul_of_eqₓ'. -/
@[to_additive]
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]
#align units.inv_mul_of_eq Units.inv_mul_of_eq

/- warning: units.mul_inv_of_eq -> Units.mul_inv_of_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a) -> (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u))) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.1956 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956} {a : α}, (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956 u) a) -> (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956) u))) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.1956))))
Case conversion may be inaccurate. Consider using '#align units.mul_inv_of_eq Units.mul_inv_of_eqₓ'. -/
@[to_additive]
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]
#align units.mul_inv_of_eq Units.mul_inv_of_eq

/- warning: units.mul_inv_cancel_left -> Units.mul_inv_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) (b : α), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) a)) b)) b
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2033 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033) (b : α), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033 a) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2033) a)) b)) b
Case conversion may be inaccurate. Consider using '#align units.mul_inv_cancel_left Units.mul_inv_cancel_leftₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]
#align units.mul_inv_cancel_left Units.mul_inv_cancel_left

/- warning: units.inv_mul_cancel_left -> Units.inv_mul_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) (b : α), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) a)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) b)) b
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2112 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112) (b : α), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112) a)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2112 a) b)) b
Case conversion may be inaccurate. Consider using '#align units.inv_mul_cancel_left Units.inv_mul_cancel_leftₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]
#align units.inv_mul_cancel_left Units.inv_mul_cancel_left

/- warning: units.mul_inv_cancel_right -> Units.mul_inv_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (b : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) b)) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) b))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2188 : Monoid.{u} α] (a : α) (b : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188 b)) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2188) b))) a
Case conversion may be inaccurate. Consider using '#align units.mul_inv_cancel_right Units.mul_inv_cancel_rightₓ'. -/
@[simp, to_additive]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]
#align units.mul_inv_cancel_right Units.mul_inv_cancel_right

/- warning: units.inv_mul_cancel_right -> Units.inv_mul_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (b : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) b))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) b)) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2263 : Monoid.{u} α] (a : α) (b : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263))) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263) b))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2263 b)) a
Case conversion may be inaccurate. Consider using '#align units.inv_mul_cancel_right Units.inv_mul_cancel_rightₓ'. -/
@[simp, to_additive]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]
#align units.inv_mul_cancel_right Units.inv_mul_cancel_right

/- warning: units.mul_right_inj -> Units.mul_right_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) b) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) c)) (Eq.{succ u} α b c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2338 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2338) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2338))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2338 a) b) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2338))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2338 a) c)) (Eq.{succ u} α b c)
Case conversion may be inaccurate. Consider using '#align units.mul_right_inj Units.mul_right_injₓ'. -/
@[simp, to_additive]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg ((· * ·) ↑(a⁻¹ : αˣ)) h,
    congr_arg _⟩
#align units.mul_right_inj Units.mul_right_inj

/- warning: units.mul_left_inj -> Units.mul_left_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) b ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) c ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a))) (Eq.{succ u} α b c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2448 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2448) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2448))) b (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2448 a)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2448))) c (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2448 a))) (Eq.{succ u} α b c)
Case conversion may be inaccurate. Consider using '#align units.mul_left_inj Units.mul_left_injₓ'. -/
@[simp, to_additive]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (· * ↑(a⁻¹ : αˣ)) h, congr_arg _⟩
#align units.mul_left_inj Units.mul_left_inj

/- warning: units.eq_mul_inv_iff_mul_eq -> Units.eq_mul_inv_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (c : Units.{u} α _inst_1) {a : α} {b : α}, Iff (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) b ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) c)))) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) c)) b)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2565 : Monoid.{u} α] (c : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565) {a : α} {b : α}, Iff (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565))) b (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565) c)))) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2565 c)) b)
Case conversion may be inaccurate. Consider using '#align units.eq_mul_inv_iff_mul_eq Units.eq_mul_inv_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩
#align units.eq_mul_inv_iff_mul_eq Units.eq_mul_inv_iff_mul_eq

/- warning: units.eq_inv_mul_iff_mul_eq -> Units.eq_inv_mul_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (b : Units.{u} α _inst_1) {a : α} {c : α}, Iff (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) b)) c)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) b) a) c)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2679 : Monoid.{u} α] (b : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679) {a : α} {c : α}, Iff (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679) b)) c)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2679 b) a) c)
Case conversion may be inaccurate. Consider using '#align units.eq_inv_mul_iff_mul_eq Units.eq_inv_mul_iff_mul_eqₓ'. -/
@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩
#align units.eq_inv_mul_iff_mul_eq Units.eq_inv_mul_iff_mul_eq

/- warning: units.inv_mul_eq_iff_eq_mul -> Units.inv_mul_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : Units.{u} α _inst_1) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) a)) b) c) (Eq.{succ u} α b (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) a) c))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2797 : Monoid.{u} α] (a : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797) {b : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797) a)) b) c) (Eq.{succ u} α b (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2797 a) c))
Case conversion may be inaccurate. Consider using '#align units.inv_mul_eq_iff_eq_mul Units.inv_mul_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩
#align units.inv_mul_eq_iff_eq_mul Units.inv_mul_eq_iff_eq_mul

/- warning: units.mul_inv_eq_iff_eq_mul -> Units.mul_inv_eq_iff_eq_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (b : Units.{u} α _inst_1) {a : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) b))) c) (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) c ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) b)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.2912 : Monoid.{u} α] (b : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912) {a : α} {c : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912) b))) c) (Eq.{succ u} α a (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912))) c (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.2912 b)))
Case conversion may be inaccurate. Consider using '#align units.mul_inv_eq_iff_eq_mul Units.mul_inv_eq_iff_eq_mulₓ'. -/
@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩
#align units.mul_inv_eq_iff_eq_mul Units.mul_inv_eq_iff_eq_mul

/- warning: units.inv_eq_of_mul_eq_one_left -> Units.inv_eq_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) -> (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3027 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027 u)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027)))) -> (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3027) u)) a)
Case conversion may be inaccurate. Consider using '#align units.inv_eq_of_mul_eq_one_left Units.inv_eq_of_mul_eq_one_leftₓ'. -/
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]
    
#align units.inv_eq_of_mul_eq_one_left Units.inv_eq_of_mul_eq_one_left

/- warning: units.inv_eq_of_mul_eq_one_right -> Units.inv_eq_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) -> (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3159 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159 u) a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159)))) -> (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3159) u)) a)
Case conversion may be inaccurate. Consider using '#align units.inv_eq_of_mul_eq_one_right Units.inv_eq_of_mul_eq_one_rightₓ'. -/
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]
    
#align units.inv_eq_of_mul_eq_one_right Units.inv_eq_of_mul_eq_one_right

/- warning: units.eq_inv_of_mul_eq_one_left -> Units.eq_inv_of_mul_eq_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) -> (Eq.{succ u} α a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3295 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295 u) a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295)))) -> (Eq.{succ u} α a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3295) u)))
Case conversion may be inaccurate. Consider using '#align units.eq_inv_of_mul_eq_one_left Units.eq_inv_of_mul_eq_one_leftₓ'. -/
@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm
#align units.eq_inv_of_mul_eq_one_left Units.eq_inv_of_mul_eq_one_left

/- warning: units.eq_inv_of_mul_eq_one_right -> Units.eq_inv_of_mul_eq_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) -> (Eq.{succ u} α a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3344 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344} {a : α}, (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344 u)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344)))) -> (Eq.{succ u} α a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3344) u)))
Case conversion may be inaccurate. Consider using '#align units.eq_inv_of_mul_eq_one_right Units.eq_inv_of_mul_eq_one_rightₓ'. -/
@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm
#align units.eq_inv_of_mul_eq_one_right Units.eq_inv_of_mul_eq_one_right

/- warning: units.mul_inv_eq_one -> Units.mul_inv_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u))) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} α a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3389 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389) u))) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389)))) (Eq.{succ u} α a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3389 u))
Case conversion may be inaccurate. Consider using '#align units.mul_inv_eq_one Units.mul_inv_eq_oneₓ'. -/
@[simp, to_additive]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩
#align units.mul_inv_eq_one Units.mul_inv_eq_one

/- warning: units.inv_mul_eq_one -> Units.inv_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3446 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446) u)) a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446)))) (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3446 u) a)
Case conversion may be inaccurate. Consider using '#align units.inv_mul_eq_one Units.inv_mul_eq_oneₓ'. -/
@[simp, to_additive]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩
#align units.inv_mul_eq_one Units.inv_mul_eq_one

/- warning: units.mul_eq_one_iff_eq_inv -> Units.mul_eq_one_iff_eq_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} α a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3503 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503 u)) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503)))) (Eq.{succ u} α a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3503) u)))
Case conversion may be inaccurate. Consider using '#align units.mul_eq_one_iff_eq_inv Units.mul_eq_one_iff_eq_invₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]
#align units.mul_eq_one_iff_eq_inv Units.mul_eq_one_iff_eq_inv

/- warning: units.mul_eq_one_iff_inv_eq -> Units.mul_eq_one_iff_inv_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {u : Units.{u} α _inst_1} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) a) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) a)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3575 : Monoid.{u} α] {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575} {a : α}, Iff (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575))) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575 u) a) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575)))) (Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3575) u)) a)
Case conversion may be inaccurate. Consider using '#align units.mul_eq_one_iff_inv_eq Units.mul_eq_one_iff_inv_eqₓ'. -/
@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]
#align units.mul_eq_one_iff_inv_eq Units.mul_eq_one_iff_inv_eq

#print Units.inv_unique /-
@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]
#align units.inv_unique Units.inv_unique
-/

/- warning: units.coe_inv -> Units.val_inv_eq_inv_val is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_2 : DivisionMonoid.{u_1} M] (u : Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))), Eq.{succ u_1} M ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (Units.val.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2)))))) (Inv.inv.{u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) (Units.hasInv.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) u)) (Inv.inv.{u_1} M (DivInvMonoid.toHasInv.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2)) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2))) M (Units.val.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_2)))))) u))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3766 : DivisionMonoid.{u_1} M] (u : Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766))), Eq.{succ u_1} M (Units.val.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766)) (Inv.inv.{u_1} (Units.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766))) (Units.instInvUnits.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766))) u)) (Inv.inv.{u_1} M (InvOneClass.toInv.{u_1} M (DivInvOneMonoid.toInvOneClass.{u_1} M (DivisionMonoid.toDivInvOneMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766))) (Units.val.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.3766)) u))
Case conversion may be inaccurate. Consider using '#align units.coe_inv Units.val_inv_eq_inv_valₓ'. -/
@[simp, to_additive]
theorem val_inv_eq_inv_val {M : Type _} [DivisionMonoid M] (u : Units M) : ↑u⁻¹ = (u⁻¹ : M) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv
#align units.coe_inv Units.val_inv_eq_inv_val

end Units

/- warning: units.mk_of_mul_eq_one -> Units.mkOfMulEqOne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommMonoid.{u} α] (a : α) (b : α), (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) a b) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1))))))) -> (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3802 : CommMonoid.{u} α] (a : α) (b : α), (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3802)))) a b) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3802))))) -> (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3802))
Case conversion may be inaccurate. Consider using '#align units.mk_of_mul_eq_one Units.mkOfMulEqOneₓ'. -/
/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive
      "For `a, b` in an `add_comm_monoid` such that `a + b = 0`, makes an add_unit\nout of `a`."]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩
#align units.mk_of_mul_eq_one Units.mkOfMulEqOne

/- warning: units.coe_mk_of_mul_eq_one -> Units.val_mkOfMulEqOne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommMonoid.{u} α] {a : α} {b : α} (h : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) a b) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1))))))), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (CommMonoid.toMonoid.{u} α _inst_1))))) (Units.mkOfMulEqOne.{u} α _inst_1 a b h)) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.3836 : CommMonoid.{u} α] {a : α} {b : α} (h : Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3836)))) a b) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3836))))), Eq.{succ u} α (Units.val.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3836) (Units.mkOfMulEqOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.3836 a b h)) a
Case conversion may be inaccurate. Consider using '#align units.coe_mk_of_mul_eq_one Units.val_mkOfMulEqOneₓ'. -/
@[simp, to_additive]
theorem Units.val_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl
#align units.coe_mk_of_mul_eq_one Units.val_mkOfMulEqOne

section Monoid

variable [Monoid α] {a b c : α}

#print divp /-
/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `division_ring` it is not totalized at zero. -/
def divp (a : α) (u) : α :=
  a * (u⁻¹ : αˣ)
#align divp divp
-/

-- mathport name: «expr /ₚ »
infixl:70 " /ₚ " => divp

/- warning: divp_self -> divp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u) u) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4539 : Monoid.{u} α] (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4539), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4539 (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4539 u) u) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4539)))
Case conversion may be inaccurate. Consider using '#align divp_self divp_selfₓ'. -/
@[simp]
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _
#align divp_self divp_self

/- warning: divp_one -> divp_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α), Eq.{succ u} α (divp.{u} α _inst_1 a (OfNat.ofNat.{u} (Units.{u} α _inst_1) 1 (OfNat.mk.{u} (Units.{u} α _inst_1) 1 (One.one.{u} (Units.{u} α _inst_1) (MulOneClass.toHasOne.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1)))))) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4566 : Monoid.{u} α] (a : α), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566 a (OfNat.ofNat.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) 1 (One.toOfNat1.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) (InvOneClass.toOne.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) (DivInvOneMonoid.toInvOneClass.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) (DivisionMonoid.toDivInvOneMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) (Group.toDivisionMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4566)))))))) a
Case conversion may be inaccurate. Consider using '#align divp_one divp_oneₓ'. -/
@[simp]
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _
#align divp_one divp_one

/- warning: divp_assoc -> divp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (b : α) (u : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a b) u) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a (divp.{u} α _inst_1 b u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4587 : Monoid.{u} α] (a : α) (b : α) (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4587), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4587 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4587))) a b) u) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4587))) a (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4587 b u))
Case conversion may be inaccurate. Consider using '#align divp_assoc divp_assocₓ'. -/
theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _
#align divp_assoc divp_assoc

/- warning: divp_assoc' -> divp_assoc' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (x : α) (y : α) (u : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) x (divp.{u} α _inst_1 y u)) (divp.{u} α _inst_1 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) x y) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4626 : Monoid.{u} α] (x : α) (y : α) (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4626), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4626))) x (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4626 y u)) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4626 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4626))) x y) u)
Case conversion may be inaccurate. Consider using '#align divp_assoc' divp_assoc'ₓ'. -/
/-- `field_simp` needs the reverse direction of `divp_assoc` to move all `/ₚ` to the right. -/
@[field_simps]
theorem divp_assoc' (x y : α) (u : αˣ) : x * (y /ₚ u) = x * y /ₚ u :=
  (divp_assoc _ _ _).symm
#align divp_assoc' divp_assoc'

/- warning: divp_inv -> divp_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {a : α} (u : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 a (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4668 : Monoid.{u} α] {a : α} (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668 a (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668) u)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4668 u))
Case conversion may be inaccurate. Consider using '#align divp_inv divp_invₓ'. -/
@[simp]
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl
#align divp_inv divp_inv

/- warning: divp_mul_cancel -> divp_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (u : Units.{u} α _inst_1), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) (divp.{u} α _inst_1 a u) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4696 : Monoid.{u} α] (a : α) (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4696), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4696))) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4696 a u) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4696 u)) a
Case conversion may be inaccurate. Consider using '#align divp_mul_cancel divp_mul_cancelₓ'. -/
@[simp]
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]
#align divp_mul_cancel divp_mul_cancel

/- warning: mul_divp_cancel -> mul_divp_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (a : α) (u : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) u) a
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4760 : Monoid.{u} α] (a : α) (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4760), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4760 (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4760))) a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4760 u)) u) a
Case conversion may be inaccurate. Consider using '#align mul_divp_cancel mul_divp_cancelₓ'. -/
@[simp]
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]
#align mul_divp_cancel mul_divp_cancel

#print divp_left_inj /-
@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _
#align divp_left_inj divp_left_inj
-/

/- warning: divp_divp_eq_divp_mul -> divp_divp_eq_divp_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (x : α) (u₁ : Units.{u} α _inst_1) (u₂ : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 (divp.{u} α _inst_1 x u₁) u₂) (divp.{u} α _inst_1 x (HMul.hMul.{u, u, u} (Units.{u} α _inst_1) (Units.{u} α _inst_1) (Units.{u} α _inst_1) (instHMul.{u} (Units.{u} α _inst_1) (MulOneClass.toHasMul.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1))) u₂ u₁))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4865 : Monoid.{u} α] (x : α) (u₁ : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (u₂ : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865 (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865 x u₁) u₂) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865 x (HMul.hMul.{u, u, u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (instHMul.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (MulOneClass.toMul.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865) (Units.instMulOneClassUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4865))) u₂ u₁))
Case conversion may be inaccurate. Consider using '#align divp_divp_eq_divp_mul divp_divp_eq_divp_mulₓ'. -/
@[field_simps]
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]
#align divp_divp_eq_divp_mul divp_divp_eq_divp_mul

/- warning: divp_eq_iff_mul_eq -> divp_eq_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {x : α} {u : Units.{u} α _inst_1} {y : α}, Iff (Eq.{succ u} α (divp.{u} α _inst_1 x u) y) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) y ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) x)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4911 : Monoid.{u} α] {x : α} {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4911} {y : α}, Iff (Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4911 x u) y) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4911))) y (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4911 u)) x)
Case conversion may be inaccurate. Consider using '#align divp_eq_iff_mul_eq divp_eq_iff_mul_eqₓ'. -/
@[field_simps]
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel] <;> exact ⟨Eq.symm, Eq.symm⟩
#align divp_eq_iff_mul_eq divp_eq_iff_mul_eq

/- warning: eq_divp_iff_mul_eq -> eq_divp_iff_mul_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {x : α} {u : Units.{u} α _inst_1} {y : α}, Iff (Eq.{succ u} α x (divp.{u} α _inst_1 y u)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α _inst_1))) x ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u)) y)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.4985 : Monoid.{u} α] {x : α} {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4985} {y : α}, Iff (Eq.{succ u} α x (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4985 y u)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4985))) x (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.4985 u)) y)
Case conversion may be inaccurate. Consider using '#align eq_divp_iff_mul_eq eq_divp_iff_mul_eqₓ'. -/
@[field_simps]
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]
#align eq_divp_iff_mul_eq eq_divp_iff_mul_eq

/- warning: divp_eq_one_iff_eq -> divp_eq_one_iff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] {a : α} {u : Units.{u} α _inst_1}, Iff (Eq.{succ u} α (divp.{u} α _inst_1 a u) (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1)))))) (Eq.{succ u} α a ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5048 : Monoid.{u} α] {a : α} {u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5048}, Iff (Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5048 a u) (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5048)))) (Eq.{succ u} α a (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5048 u))
Case conversion may be inaccurate. Consider using '#align divp_eq_one_iff_eq divp_eq_one_iff_eqₓ'. -/
theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]
#align divp_eq_one_iff_eq divp_eq_one_iff_eq

/- warning: one_divp -> one_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u : Units.{u} α _inst_1), Eq.{succ u} α (divp.{u} α _inst_1 (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))) u) ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5115 : Monoid.{u} α] (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115), Eq.{succ u} α (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115 (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115))) u) (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5115) u))
Case conversion may be inaccurate. Consider using '#align one_divp one_divpₓ'. -/
@[simp]
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _
#align one_divp one_divp

/- warning: inv_eq_one_divp -> inv_eq_one_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u : Units.{u} α _inst_1), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (Inv.inv.{u} (Units.{u} α _inst_1) (Units.hasInv.{u} α _inst_1) u)) (divp.{u} α _inst_1 (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5145 : Monoid.{u} α] (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145 (Inv.inv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145) (Units.instInvUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145) u)) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145 (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5145))) u)
Case conversion may be inaccurate. Consider using '#align inv_eq_one_divp inv_eq_one_divpₓ'. -/
/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps]
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]
#align inv_eq_one_divp inv_eq_one_divp

/- warning: inv_eq_one_divp' -> inv_eq_one_divp' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u : Units.{u} α _inst_1), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (HDiv.hDiv.{u, u, u} (Units.{u} α _inst_1) (Units.{u} α _inst_1) (Units.{u} α _inst_1) (instHDiv.{u} (Units.{u} α _inst_1) (DivInvMonoid.toHasDiv.{u} (Units.{u} α _inst_1) (Group.toDivInvMonoid.{u} (Units.{u} α _inst_1) (Units.group.{u} α _inst_1)))) (OfNat.ofNat.{u} (Units.{u} α _inst_1) 1 (OfNat.mk.{u} (Units.{u} α _inst_1) 1 (One.one.{u} (Units.{u} α _inst_1) (MulOneClass.toHasOne.{u} (Units.{u} α _inst_1) (Units.mulOneClass.{u} α _inst_1))))) u)) (divp.{u} α _inst_1 (OfNat.ofNat.{u} α 1 (OfNat.mk.{u} α 1 (One.one.{u} α (MulOneClass.toHasOne.{u} α (Monoid.toMulOneClass.{u} α _inst_1))))) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5204 : Monoid.{u} α] (u : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204 (HDiv.hDiv.{u, u, u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (instHDiv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (DivInvMonoid.toDiv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Group.toDivInvMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204)))) (OfNat.ofNat.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) 1 (One.toOfNat1.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (InvOneClass.toOne.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (DivInvOneMonoid.toInvOneClass.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (DivisionMonoid.toDivInvOneMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Group.toDivisionMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204))))))) u)) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204 (OfNat.ofNat.{u} α 1 (One.toOfNat1.{u} α (Monoid.toOne.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5204))) u)
Case conversion may be inaccurate. Consider using '#align inv_eq_one_divp' inv_eq_one_divp'ₓ'. -/
/-- Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`.
-/
@[field_simps]
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by rw [one_div, one_divp]
#align inv_eq_one_divp' inv_eq_one_divp'

/- warning: coe_div_eq_divp -> val_div_eq_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Monoid.{u} α] (u₁ : Units.{u} α _inst_1) (u₂ : Units.{u} α _inst_1), Eq.{succ u} α ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) (HDiv.hDiv.{u, u, u} (Units.{u} α _inst_1) (Units.{u} α _inst_1) (Units.{u} α _inst_1) (instHDiv.{u} (Units.{u} α _inst_1) (DivInvMonoid.toHasDiv.{u} (Units.{u} α _inst_1) (Group.toDivInvMonoid.{u} (Units.{u} α _inst_1) (Units.group.{u} α _inst_1)))) u₁ u₂)) (divp.{u} α _inst_1 ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α _inst_1) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α _inst_1) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α _inst_1) α (Units.val.{u} α _inst_1)))) u₁) u₂)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5270 : Monoid.{u} α] (u₁ : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (u₂ : Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270), Eq.{succ u} α (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270 (HDiv.hDiv.{u, u, u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (instHDiv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (DivInvMonoid.toDiv.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (Group.toDivInvMonoid.{u} (Units.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270) (Units.instGroupUnits.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270)))) u₁ u₂)) (divp.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270 (Units.val.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5270 u₁) u₂)
Case conversion may be inaccurate. Consider using '#align coe_div_eq_divp val_div_eq_divpₓ'. -/
/-- `field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps]
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]
#align coe_div_eq_divp val_div_eq_divp

end Monoid

section CommMonoid

variable [CommMonoid α]

/- warning: divp_mul_eq_mul_divp -> divp_mul_eq_mul_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommMonoid.{u} α] (x : α) (y : α) (u : Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) x u) y) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) x y) u)
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5349 : CommMonoid.{u} α] (x : α) (y : α) (u : Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5349)), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5349)))) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5349) x u) y) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5349) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5349)))) x y) u)
Case conversion may be inaccurate. Consider using '#align divp_mul_eq_mul_divp divp_mul_eq_mul_divpₓ'. -/
@[field_simps]
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  simp_rw [divp, mul_assoc, mul_comm]
#align divp_mul_eq_mul_divp divp_mul_eq_mul_divp

/- warning: divp_eq_divp_iff -> divp_eq_divp_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommMonoid.{u} α] {x : α} {y : α} {ux : Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)} {uy : Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)}, Iff (Eq.{succ u} α (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) x ux) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) y uy)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) x ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (CommMonoid.toMonoid.{u} α _inst_1))))) uy)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) y ((fun (a : Type.{u}) (b : Type.{u}) [self : HasLiftT.{succ u, succ u} a b] => self.0) (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (HasLiftT.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.coe.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (CoeTCₓ.mk.{succ u, succ u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) α (Units.val.{u} α (CommMonoid.toMonoid.{u} α _inst_1))))) ux)))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5412 : CommMonoid.{u} α] {x : α} {y : α} {ux : Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412)} {uy : Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412)}, Iff (Eq.{succ u} α (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412) x ux) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412) y uy)) (Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412)))) x (Units.val.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412) uy)) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412)))) y (Units.val.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5412) ux)))
Case conversion may be inaccurate. Consider using '#align divp_eq_divp_iff divp_eq_divp_iffₓ'. -/
-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
#align divp_eq_divp_iff divp_eq_divp_iff

/- warning: divp_mul_divp -> divp_mul_divp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : CommMonoid.{u} α] (x : α) (y : α) (ux : Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (uy : Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) x ux) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) y uy)) (divp.{u} α (CommMonoid.toMonoid.{u} α _inst_1) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toHasMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) x y) (HMul.hMul.{u, u, u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (instHMul.{u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (MulOneClass.toHasMul.{u} (Units.{u} α (CommMonoid.toMonoid.{u} α _inst_1)) (Units.mulOneClass.{u} α (CommMonoid.toMonoid.{u} α _inst_1)))) ux uy))
but is expected to have type
  forall {α : Type.{u}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5484 : CommMonoid.{u} α] (x : α) (y : α) (ux : Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (uy : Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)), Eq.{succ u} α (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)))) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484) x ux) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484) y uy)) (divp.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484) (HMul.hMul.{u, u, u} α α α (instHMul.{u} α (MulOneClass.toMul.{u} α (Monoid.toMulOneClass.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)))) x y) (HMul.hMul.{u, u, u} (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (instHMul.{u} (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (MulOneClass.toMul.{u} (Units.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)) (Units.instMulOneClassUnits.{u} α (CommMonoid.toMonoid.{u} α inst._@.Mathlib.Algebra.Group.Units._hyg.5484)))) ux uy))
Case conversion may be inaccurate. Consider using '#align divp_mul_divp divp_mul_divpₓ'. -/
-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]
#align divp_mul_divp divp_mul_divp

end CommMonoid

/-!
# `is_unit` predicate

In this file we define the `is_unit` predicate on a `monoid`, and
prove a few basic properties. For the bundled version see `units`. See
also `prime`, `associated`, and `irreducible` in `algebra/associated`.

-/


section IsUnit

variable {M : Type _} {N : Type _}

#print IsUnit /-
/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `is_unit`. -/
@[to_additive
      "An element `a : M` of an add_monoid is an `add_unit` if it has\na two-sided additive inverse. The actual definition says that `a` is equal to some\n`u : add_units M`, where `add_units M` is a bundled version of `is_add_unit`."]
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a
#align is_unit IsUnit
-/

#print isUnit_of_subsingleton /-
@[nontriviality, to_additive]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩
#align is_unit_of_subsingleton isUnit_of_subsingleton
-/

attribute [nontriviality] isAddUnit_of_subsingleton

@[to_additive]
instance [Monoid M] : CanLift M Mˣ coe IsUnit where prf _ := id

@[to_additive]
instance [Monoid M] [Subsingleton M] :
    Unique Mˣ where 
  default := 1
  uniq a := Units.val_eq_one.mp <| Subsingleton.elim (a : M) 1

#print Units.isUnit /-
@[simp, to_additive AddUnits.isAddUnit]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩
#align units.is_unit Units.isUnit
-/

/- warning: is_unit_one -> isUnit_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M], IsUnit.{u_1} M _inst_1 (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5689 : Monoid.{u_1} M], IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5689 (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5689)))
Case conversion may be inaccurate. Consider using '#align is_unit_one isUnit_oneₓ'. -/
@[simp, to_additive]
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩
#align is_unit_one isUnit_one

/- warning: is_unit_of_mul_eq_one -> isUnit_of_mul_eq_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] (a : M) (b : M), (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) a b) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1))))))) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) a)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5707 : CommMonoid.{u_1} M] (a : M) (b : M), (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5707)))) a b) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5707))))) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5707) a)
Case conversion may be inaccurate. Consider using '#align is_unit_of_mul_eq_one isUnit_of_mul_eq_oneₓ'. -/
@[to_additive]
theorem isUnit_of_mul_eq_one [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨Units.mkOfMulEqOne a b h, rfl⟩
#align is_unit_of_mul_eq_one isUnit_of_mul_eq_one

/- warning: is_unit.exists_right_inv -> IsUnit.exists_right_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M _inst_1 a) -> (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a b) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5737 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5737 a) -> (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5737))) a b) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5737)))))
Case conversion may be inaccurate. Consider using '#align is_unit.exists_right_inv IsUnit.exists_right_invₓ'. -/
@[to_additive IsAddUnit.exists_neg]
theorem IsUnit.exists_right_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩
  exact ⟨b, hab⟩
#align is_unit.exists_right_inv IsUnit.exists_right_inv

/- warning: is_unit.exists_left_inv -> IsUnit.exists_left_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M _inst_1 a) -> (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) b a) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1)))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5777 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5777 a) -> (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5777))) b a) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5777)))))
Case conversion may be inaccurate. Consider using '#align is_unit.exists_left_inv IsUnit.exists_left_invₓ'. -/
@[to_additive IsAddUnit.exists_neg']
theorem IsUnit.exists_left_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩
  exact ⟨b, hba⟩
#align is_unit.exists_left_inv IsUnit.exists_left_inv

/- warning: is_unit_iff_exists_inv -> isUnit_iff_exists_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] {a : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) a) (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) a b) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1))))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5814 : CommMonoid.{u_1} M] {a : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5814) a) (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5814)))) a b) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5814))))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_exists_inv isUnit_iff_exists_invₓ'. -/
@[to_additive]
theorem isUnit_iff_exists_inv [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨fun h => h.exists_right_inv, fun ⟨b, hab⟩ => isUnit_of_mul_eq_one _ b hab⟩
#align is_unit_iff_exists_inv isUnit_iff_exists_inv

/- warning: is_unit_iff_exists_inv' -> isUnit_iff_exists_inv' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] {a : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) a) (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) b a) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1))))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5871 : CommMonoid.{u_1} M] {a : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5871) a) (Exists.{succ u_1} M (fun (b : M) => Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5871)))) b a) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5871))))))
Case conversion may be inaccurate. Consider using '#align is_unit_iff_exists_inv' isUnit_iff_exists_inv'ₓ'. -/
@[to_additive]
theorem isUnit_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, b * a = 1 := by
  simp [isUnit_iff_exists_inv, mul_comm]
#align is_unit_iff_exists_inv' isUnit_iff_exists_inv'

/- warning: is_unit.mul -> IsUnit.mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M _inst_1 x) -> (IsUnit.{u_1} M _inst_1 y) -> (IsUnit.{u_1} M _inst_1 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) x y))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5935 : Monoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5935 x) -> (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5935 y) -> (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5935 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5935))) x y))
Case conversion may be inaccurate. Consider using '#align is_unit.mul IsUnit.mulₓ'. -/
@[to_additive]
theorem IsUnit.mul [Monoid M] {x y : M} : IsUnit x → IsUnit y → IsUnit (x * y) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩
  exact ⟨x * y, Units.val_mul _ _⟩
#align is_unit.mul IsUnit.mul

/- warning: units.is_unit_mul_units -> Units.isUnit_mul_units is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] (a : M) (u : Units.{u_1} M _inst_1), Iff (IsUnit.{u_1} M _inst_1 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M _inst_1) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (Units.val.{u_1} M _inst_1)))) u))) (IsUnit.{u_1} M _inst_1 a)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.5981 : Monoid.{u_1} M] (a : M) (u : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5981), Iff (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5981 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5981))) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5981 u))) (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.5981 a)
Case conversion may be inaccurate. Consider using '#align units.is_unit_mul_units Units.isUnit_mul_unitsₓ'. -/
/-- Multiplication by a `u : Mˣ` on the right doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the right doesn't\naffect `is_add_unit`."]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹ <;> rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this)
    fun v => v.mul u.IsUnit
#align units.is_unit_mul_units Units.isUnit_mul_units

/- warning: units.is_unit_units_mul -> Units.isUnit_units_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] (u : Units.{u_1} M _inst_1) (a : M), Iff (IsUnit.{u_1} M _inst_1 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M _inst_1) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (Units.val.{u_1} M _inst_1)))) u) a)) (IsUnit.{u_1} M _inst_1 a)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6194 : Monoid.{u_1} M] (u : Units.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6194) (a : M), Iff (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6194 (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6194))) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6194 u) a)) (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6194 a)
Case conversion may be inaccurate. Consider using '#align units.is_unit_units_mul Units.isUnit_units_mulₓ'. -/
/-- Multiplication by a `u : Mˣ` on the left doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the left doesn't affect `is_add_unit`."]
theorem Units.isUnit_units_mul {M : Type _} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v <;> rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.IsUnit.mul
#align units.is_unit_units_mul Units.isUnit_units_mul

/- warning: is_unit_of_mul_is_unit_left -> isUnit_of_mul_isUnit_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) x y)) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) x)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6402 : CommMonoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6402) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6402)))) x y)) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6402) x)
Case conversion may be inaccurate. Consider using '#align is_unit_of_mul_is_unit_left isUnit_of_mul_isUnit_leftₓ'. -/
@[to_additive]
theorem isUnit_of_mul_isUnit_left [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩
#align is_unit_of_mul_is_unit_left isUnit_of_mul_isUnit_left

/- warning: is_unit_of_mul_is_unit_right -> isUnit_of_mul_isUnit_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) x y)) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) y)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6487 : CommMonoid.{u_1} M] {x : M} {y : M}, (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6487) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6487)))) x y)) -> (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6487) y)
Case conversion may be inaccurate. Consider using '#align is_unit_of_mul_is_unit_right isUnit_of_mul_isUnit_rightₓ'. -/
@[to_additive]
theorem isUnit_of_mul_isUnit_right [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y :=
  @isUnit_of_mul_isUnit_left _ _ y x <| by rwa [mul_comm]
#align is_unit_of_mul_is_unit_right isUnit_of_mul_isUnit_right

namespace IsUnit

/- warning: is_unit.mul_iff -> IsUnit.mul_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : CommMonoid.{u_1} M] {x : M} {y : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1)))) x y)) (And (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) x) (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M _inst_1) y))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6552 : CommMonoid.{u_1} M] {x : M} {y : M}, Iff (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6552) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6552)))) x y)) (And (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6552) x) (IsUnit.{u_1} M (CommMonoid.toMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6552) y))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_iff IsUnit.mul_iffₓ'. -/
@[simp, to_additive]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩, fun h =>
    IsUnit.mul h.1 h.2⟩
#align is_unit.mul_iff IsUnit.mul_iff

section Monoid

variable [Monoid M] {a b c : M}

#print IsUnit.unit /-
/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `division_monoid`, use `is_unit.unit'` instead. -/
@[to_additive
      "The element of the additive group of additive units, corresponding to an element of\nan additive monoid which is an additive unit. When `α` is a `subtraction_monoid`, use\n`is_add_unit.add_unit'` instead."]
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_unit.unit IsUnit.unit
-/

#print IsUnit.unit_of_val_units /-
@[simp, to_additive]
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.Unit = a :=
  Units.ext <| rfl
#align is_unit.unit_of_coe_units IsUnit.unit_of_val_units
-/

#print IsUnit.unit_spec /-
@[simp, to_additive]
theorem unit_spec (h : IsUnit a) : ↑h.Unit = a :=
  rfl
#align is_unit.unit_spec IsUnit.unit_spec
-/

/- warning: is_unit.coe_inv_mul -> IsUnit.val_inv_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} (h : IsUnit.{u_1} M _inst_1 a), Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M _inst_1) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (Units.val.{u_1} M _inst_1)))) (Inv.inv.{u_1} (Units.{u_1} M _inst_1) (Units.hasInv.{u_1} M _inst_1) (IsUnit.unit.{u_1} M _inst_1 a h))) a) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6726 : Monoid.{u_1} M] {a : M} (h : IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726 a), Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726))) (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726) (IsUnit.unit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726 a h))) a) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6726)))
Case conversion may be inaccurate. Consider using '#align is_unit.coe_inv_mul IsUnit.val_inv_mulₓ'. -/
@[simp, to_additive]
theorem val_inv_mul (h : IsUnit a) : ↑h.Unit⁻¹ * a = 1 :=
  Units.mul_inv _
#align is_unit.coe_inv_mul IsUnit.val_inv_mul

/- warning: is_unit.mul_coe_inv -> IsUnit.mul_val_inv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} (h : IsUnit.{u_1} M _inst_1 a), Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a ((fun (a : Type.{u_1}) (b : Type.{u_1}) [self : HasLiftT.{succ u_1, succ u_1} a b] => self.0) (Units.{u_1} M _inst_1) M (HasLiftT.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.coe.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (CoeTCₓ.mk.{succ u_1, succ u_1} (Units.{u_1} M _inst_1) M (Units.val.{u_1} M _inst_1)))) (Inv.inv.{u_1} (Units.{u_1} M _inst_1) (Units.hasInv.{u_1} M _inst_1) (IsUnit.unit.{u_1} M _inst_1 a h)))) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6756 : Monoid.{u_1} M] {a : M} (h : IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756 a), Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756))) a (Units.val.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756 (Inv.inv.{u_1} (Units.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756) (Units.instInvUnits.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756) (IsUnit.unit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756 a h)))) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (Monoid.toOne.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6756)))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_coe_inv IsUnit.mul_val_invₓ'. -/
@[simp, to_additive]
theorem mul_val_inv (h : IsUnit a) : a * ↑h.Unit⁻¹ = 1 := by convert h.unit.mul_inv
#align is_unit.mul_coe_inv IsUnit.mul_val_inv

/-- `is_unit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

/- warning: is_unit.mul_left_inj -> IsUnit.mul_left_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M _inst_1 a) -> (Iff (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) b a) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) c a)) (Eq.{succ u_1} M b c))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6859 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6859 a) -> (Iff (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6859))) b a) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6859))) c a)) (Eq.{succ u_1} M b c))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_left_inj IsUnit.mul_left_injₓ'. -/
@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj
#align is_unit.mul_left_inj IsUnit.mul_left_inj

/- warning: is_unit.mul_right_inj -> IsUnit.mul_right_inj is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M _inst_1 a) -> (Iff (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a c)) (Eq.{succ u_1} M b c))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6907 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6907 a) -> (Iff (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6907))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6907))) a c)) (Eq.{succ u_1} M b c))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_right_inj IsUnit.mul_right_injₓ'. -/
@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj
#align is_unit.mul_right_inj IsUnit.mul_right_inj

/- warning: is_unit.mul_left_cancel -> IsUnit.mul_left_cancel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M _inst_1 a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a c)) -> (Eq.{succ u_1} M b c)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6955 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6955 a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6955))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6955))) a c)) -> (Eq.{succ u_1} M b c)
Case conversion may be inaccurate. Consider using '#align is_unit.mul_left_cancel IsUnit.mul_left_cancelₓ'. -/
@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1
#align is_unit.mul_left_cancel IsUnit.mul_left_cancel

/- warning: is_unit.mul_right_cancel -> IsUnit.mul_right_cancel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M _inst_1 b) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) c b)) -> (Eq.{succ u_1} M a c)
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.6983 : Monoid.{u_1} M] {a : M} {b : M} {c : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6983 b) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6983))) a b) (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.6983))) c b)) -> (Eq.{succ u_1} M a c)
Case conversion may be inaccurate. Consider using '#align is_unit.mul_right_cancel IsUnit.mul_right_cancelₓ'. -/
@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1
#align is_unit.mul_right_cancel IsUnit.mul_right_cancel

/- warning: is_unit.mul_right_injective -> IsUnit.mul_right_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M _inst_1 a) -> (Function.Injective.{succ u_1, succ u_1} M M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) a))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.7011 : Monoid.{u_1} M] {a : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7011 a) -> (Function.Injective.{succ u_1, succ u_1} M M ((fun (x._@.Mathlib.Algebra.Group.Units._hyg.7026 : M) (x._@.Mathlib.Algebra.Group.Units._hyg.7028 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7011))) x._@.Mathlib.Algebra.Group.Units._hyg.7026 x._@.Mathlib.Algebra.Group.Units._hyg.7028) a))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_right_injective IsUnit.mul_right_injectiveₓ'. -/
@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective ((· * ·) a) := fun _ _ =>
  h.mul_left_cancel
#align is_unit.mul_right_injective IsUnit.mul_right_injective

/- warning: is_unit.mul_left_injective -> IsUnit.mul_left_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : Monoid.{u_1} M] {b : M}, (IsUnit.{u_1} M _inst_1 b) -> (Function.Injective.{succ u_1, succ u_1} M M (fun (_x : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M _inst_1))) _x b))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.7050 : Monoid.{u_1} M] {b : M}, (IsUnit.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7050 b) -> (Function.Injective.{succ u_1, succ u_1} M M (fun (x._@.Mathlib.Algebra.Group.Units._hyg.7062 : M) => HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7050))) x._@.Mathlib.Algebra.Group.Units._hyg.7062 b))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_left_injective IsUnit.mul_left_injectiveₓ'. -/
@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) := fun _ _ =>
  h.mul_right_cancel
#align is_unit.mul_left_injective IsUnit.mul_left_injective

end Monoid

variable [DivisionMonoid M] {a : M}

/- warning: is_unit.inv_mul_cancel -> IsUnit.inv_mul_cancel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} M] {a : M}, (IsUnit.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1)) a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1))))) (Inv.inv.{u_1} M (DivInvMonoid.toHasInv.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1)) a) a) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1))))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.7093 : DivisionMonoid.{u_1} M] {a : M}, (IsUnit.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7093)) a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7093))))) (Inv.inv.{u_1} M (InvOneClass.toInv.{u_1} M (DivInvOneMonoid.toInvOneClass.{u_1} M (DivisionMonoid.toDivInvOneMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7093))) a) a) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (InvOneClass.toOne.{u_1} M (DivInvOneMonoid.toInvOneClass.{u_1} M (DivisionMonoid.toDivInvOneMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7093))))))
Case conversion may be inaccurate. Consider using '#align is_unit.inv_mul_cancel IsUnit.inv_mul_cancelₓ'. -/
@[simp, to_additive]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]
#align is_unit.inv_mul_cancel IsUnit.inv_mul_cancel

/- warning: is_unit.mul_inv_cancel -> IsUnit.mul_inv_cancel is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u_1}} [_inst_1 : DivisionMonoid.{u_1} M] {a : M}, (IsUnit.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1)) a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toHasMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1))))) a (Inv.inv.{u_1} M (DivInvMonoid.toHasInv.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1)) a)) (OfNat.ofNat.{u_1} M 1 (OfNat.mk.{u_1} M 1 (One.one.{u_1} M (MulOneClass.toHasOne.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M _inst_1))))))))
but is expected to have type
  forall {M : Type.{u_1}} [inst._@.Mathlib.Algebra.Group.Units._hyg.7148 : DivisionMonoid.{u_1} M] {a : M}, (IsUnit.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7148)) a) -> (Eq.{succ u_1} M (HMul.hMul.{u_1, u_1, u_1} M M M (instHMul.{u_1} M (MulOneClass.toMul.{u_1} M (Monoid.toMulOneClass.{u_1} M (DivInvMonoid.toMonoid.{u_1} M (DivisionMonoid.toDivInvMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7148))))) a (Inv.inv.{u_1} M (InvOneClass.toInv.{u_1} M (DivInvOneMonoid.toInvOneClass.{u_1} M (DivisionMonoid.toDivInvOneMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7148))) a)) (OfNat.ofNat.{u_1} M 1 (One.toOfNat1.{u_1} M (InvOneClass.toOne.{u_1} M (DivInvOneMonoid.toInvOneClass.{u_1} M (DivisionMonoid.toDivInvOneMonoid.{u_1} M inst._@.Mathlib.Algebra.Group.Units._hyg.7148))))))
Case conversion may be inaccurate. Consider using '#align is_unit.mul_inv_cancel IsUnit.mul_inv_cancelₓ'. -/
@[simp, to_additive]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by
  rintro ⟨u, rfl⟩
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]
#align is_unit.mul_inv_cancel IsUnit.mul_inv_cancel

end IsUnit

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type _}

#print groupOfIsUnit /-
/-- Constructs a `group` structure on a `monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with inv := fun a => ↑(h a).Unit⁻¹,
    mul_left_inv := fun a => by 
      change ↑(h a).Unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align group_of_is_unit groupOfIsUnit
-/

#print commGroupOfIsUnit /-
/-- Constructs a `comm_group` structure on a `comm_monoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with inv := fun a => ↑(h a).Unit⁻¹,
    mul_left_inv := fun a => by 
      change ↑(h a).Unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align comm_group_of_is_unit commGroupOfIsUnit
-/

end NoncomputableDefs

