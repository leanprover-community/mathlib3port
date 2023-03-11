/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module topology.locally_constant.algebra
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Pi
import Mathbin.Topology.LocallyConstant.Basic

/-!
# Algebraic structure on locally constant functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file puts algebraic structure (`add_group`, etc)
on the type of locally constant functions.

-/


namespace LocallyConstant

variable {X Y : Type _} [TopologicalSpace X]

@[to_additive]
instance [One Y] : One (LocallyConstant X Y) where one := const X 1

#print LocallyConstant.coe_one /-
@[simp, to_additive]
theorem coe_one [One Y] : ⇑(1 : LocallyConstant X Y) = (1 : X → Y) :=
  rfl
#align locally_constant.coe_one LocallyConstant.coe_one
#align locally_constant.coe_zero LocallyConstant.coe_zero
-/

#print LocallyConstant.one_apply /-
@[to_additive]
theorem one_apply [One Y] (x : X) : (1 : LocallyConstant X Y) x = 1 :=
  rfl
#align locally_constant.one_apply LocallyConstant.one_apply
#align locally_constant.zero_apply LocallyConstant.zero_apply
-/

@[to_additive]
instance [Inv Y] : Inv (LocallyConstant X Y) where inv f := ⟨f⁻¹, f.IsLocallyConstant.inv⟩

#print LocallyConstant.coe_inv /-
@[simp, to_additive]
theorem coe_inv [Inv Y] (f : LocallyConstant X Y) : ⇑f⁻¹ = f⁻¹ :=
  rfl
#align locally_constant.coe_inv LocallyConstant.coe_inv
#align locally_constant.coe_neg LocallyConstant.coe_neg
-/

#print LocallyConstant.inv_apply /-
@[to_additive]
theorem inv_apply [Inv Y] (f : LocallyConstant X Y) (x : X) : f⁻¹ x = (f x)⁻¹ :=
  rfl
#align locally_constant.inv_apply LocallyConstant.inv_apply
#align locally_constant.neg_apply LocallyConstant.neg_apply
-/

@[to_additive]
instance [Mul Y] : Mul (LocallyConstant X Y)
    where mul f g := ⟨f * g, f.IsLocallyConstant.mul g.IsLocallyConstant⟩

#print LocallyConstant.coe_mul /-
@[simp, to_additive]
theorem coe_mul [Mul Y] (f g : LocallyConstant X Y) : ⇑(f * g) = f * g :=
  rfl
#align locally_constant.coe_mul LocallyConstant.coe_mul
#align locally_constant.coe_add LocallyConstant.coe_add
-/

#print LocallyConstant.mul_apply /-
@[to_additive]
theorem mul_apply [Mul Y] (f g : LocallyConstant X Y) (x : X) : (f * g) x = f x * g x :=
  rfl
#align locally_constant.mul_apply LocallyConstant.mul_apply
#align locally_constant.add_apply LocallyConstant.add_apply
-/

@[to_additive]
instance [MulOneClass Y] : MulOneClass (LocallyConstant X Y) :=
  { LocallyConstant.hasOne,
    LocallyConstant.hasMul with
    one_mul := by
      intros
      ext
      simp only [mul_apply, one_apply, one_mul]
    mul_one := by
      intros
      ext
      simp only [mul_apply, one_apply, mul_one] }

/- warning: locally_constant.coe_fn_monoid_hom -> LocallyConstant.coeFnMonoidHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulOneClass.{u2} Y], MonoidHom.{max u1 u2, max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (X -> Y) (LocallyConstant.mulOneClass.{u1, u2} X Y _inst_1 _inst_2) (Pi.mulOneClass.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_2))
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulOneClass.{u2} Y], MonoidHom.{max u2 u1, max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (X -> Y) (LocallyConstant.instMulOneClassLocallyConstant.{u1, u2} X Y _inst_1 _inst_2) (Pi.mulOneClass.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_2))
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_fn_monoid_hom LocallyConstant.coeFnMonoidHomₓ'. -/
/-- `coe_fn` is a `monoid_hom`. -/
@[to_additive "`coe_fn` is an `add_monoid_hom`.", simps]
def coeFnMonoidHom [MulOneClass Y] : LocallyConstant X Y →* X → Y
    where
  toFun := coeFn
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.coe_fn_monoid_hom LocallyConstant.coeFnMonoidHom
#align locally_constant.coe_fn_add_monoid_hom LocallyConstant.coeFnAddMonoidHom

/- warning: locally_constant.const_monoid_hom -> LocallyConstant.constMonoidHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulOneClass.{u2} Y], MonoidHom.{u2, max u1 u2} Y (LocallyConstant.{u1, u2} X Y _inst_1) _inst_2 (LocallyConstant.mulOneClass.{u1, u2} X Y _inst_1 _inst_2)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulOneClass.{u2} Y], MonoidHom.{u2, max u2 u1} Y (LocallyConstant.{u1, u2} X Y _inst_1) _inst_2 (LocallyConstant.instMulOneClassLocallyConstant.{u1, u2} X Y _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align locally_constant.const_monoid_hom LocallyConstant.constMonoidHomₓ'. -/
/-- The constant-function embedding, as a multiplicative monoid hom. -/
@[to_additive "The constant-function embedding, as an additive monoid hom.", simps]
def constMonoidHom [MulOneClass Y] : Y →* LocallyConstant X Y
    where
  toFun := const X
  map_one' := rfl
  map_mul' _ _ := rfl
#align locally_constant.const_monoid_hom LocallyConstant.constMonoidHom
#align locally_constant.const_add_monoid_hom LocallyConstant.constAddMonoidHom

instance [MulZeroClass Y] : MulZeroClass (LocallyConstant X Y) :=
  { LocallyConstant.hasZero,
    LocallyConstant.hasMul with
    zero_mul := by
      intros
      ext
      simp only [mul_apply, zero_apply, MulZeroClass.zero_mul]
    mul_zero := by
      intros
      ext
      simp only [mul_apply, zero_apply, MulZeroClass.mul_zero] }

instance [MulZeroOneClass Y] : MulZeroOneClass (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.mulOneClass with }

section CharFn

variable (Y) [MulZeroOneClass Y] {U V : Set X}

#print LocallyConstant.charFn /-
/-- Characteristic functions are locally constant functions taking `x : X` to `1` if `x ∈ U`,
  where `U` is a clopen set, and `0` otherwise. -/
noncomputable def charFn (hU : IsClopen U) : LocallyConstant X Y :=
  indicator 1 hU
#align locally_constant.char_fn LocallyConstant.charFn
-/

/- warning: locally_constant.coe_char_fn -> LocallyConstant.coe_charFn is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} (Y : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulZeroOneClass.{u2} Y] {U : Set.{u1} X} (hU : IsClopen.{u1} X _inst_1 U), Eq.{max (succ u1) (succ u2)} ((fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU)) (Set.indicator.{u1, u2} X Y (MulZeroClass.toHasZero.{u2} Y (MulZeroOneClass.toMulZeroClass.{u2} Y _inst_2)) U (OfNat.ofNat.{max u1 u2} (X -> Y) 1 (OfNat.mk.{max u1 u2} (X -> Y) 1 (One.one.{max u1 u2} (X -> Y) (Pi.instOne.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => MulOneClass.toHasOne.{u2} Y (MulZeroOneClass.toMulOneClass.{u2} Y _inst_2)))))))
but is expected to have type
  forall {X : Type.{u2}} (Y : Type.{u1}) [_inst_1 : TopologicalSpace.{u2} X] [_inst_2 : MulZeroOneClass.{u1} Y] {U : Set.{u2} X} (hU : IsClopen.{u2} X _inst_1 U), Eq.{max (succ u2) (succ u1)} (forall (a : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (LocallyConstant.{u2, u1} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u2, u1} X Y _inst_1) (LocallyConstant.charFn.{u2, u1} X Y _inst_1 _inst_2 U hU)) (Set.indicator.{u2, u1} X Y (MulZeroOneClass.toZero.{u1} Y _inst_2) U (OfNat.ofNat.{max u2 u1} (X -> Y) 1 (One.toOfNat1.{max u2 u1} (X -> Y) (Pi.instOne.{u2, u1} X (fun (a._@.Mathlib.Algebra.IndicatorFunction._hyg.77 : X) => Y) (fun (i : X) => MulOneClass.toOne.{u1} Y (MulZeroOneClass.toMulOneClass.{u1} Y _inst_2))))))
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_char_fn LocallyConstant.coe_charFnₓ'. -/
theorem coe_charFn (hU : IsClopen U) : (charFn Y hU : X → Y) = Set.indicator U 1 :=
  rfl
#align locally_constant.coe_char_fn LocallyConstant.coe_charFn

/- warning: locally_constant.char_fn_eq_one -> LocallyConstant.charFn_eq_one is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} (Y : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulZeroOneClass.{u2} Y] {U : Set.{u1} X} [_inst_3 : Nontrivial.{u2} Y] (x : X) (hU : IsClopen.{u1} X _inst_1 U), Iff (Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU) x) (OfNat.ofNat.{u2} Y 1 (OfNat.mk.{u2} Y 1 (One.one.{u2} Y (MulOneClass.toHasOne.{u2} Y (MulZeroOneClass.toMulOneClass.{u2} Y _inst_2)))))) (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U)
but is expected to have type
  forall {X : Type.{u1}} (Y : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulZeroOneClass.{u2} Y] {U : Set.{u1} X} [_inst_3 : Nontrivial.{u2} Y] (x : X) (hU : IsClopen.{u1} X _inst_1 U), Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyConstant.{u1, u2} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, u2} X Y _inst_1) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU) x) (OfNat.ofNat.{u2} Y 1 (One.toOfNat1.{u2} Y (MulOneClass.toOne.{u2} Y (MulZeroOneClass.toMulOneClass.{u2} Y _inst_2))))) (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x U)
Case conversion may be inaccurate. Consider using '#align locally_constant.char_fn_eq_one LocallyConstant.charFn_eq_oneₓ'. -/
theorem charFn_eq_one [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (1 : Y) ↔ x ∈ U :=
  Set.indicator_eq_one_iff_mem _
#align locally_constant.char_fn_eq_one LocallyConstant.charFn_eq_one

/- warning: locally_constant.char_fn_eq_zero -> LocallyConstant.charFn_eq_zero is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} (Y : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulZeroOneClass.{u2} Y] {U : Set.{u1} X} [_inst_3 : Nontrivial.{u2} Y] (x : X) (hU : IsClopen.{u1} X _inst_1 U), Iff (Eq.{succ u2} Y (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU) x) (OfNat.ofNat.{u2} Y 0 (OfNat.mk.{u2} Y 0 (Zero.zero.{u2} Y (MulZeroClass.toHasZero.{u2} Y (MulZeroOneClass.toMulZeroClass.{u2} Y _inst_2)))))) (Not (Membership.Mem.{u1, u1} X (Set.{u1} X) (Set.hasMem.{u1} X) x U))
but is expected to have type
  forall {X : Type.{u1}} (Y : Type.{u2}) [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : MulZeroOneClass.{u2} Y] {U : Set.{u1} X} [_inst_3 : Nontrivial.{u2} Y] (x : X) (hU : IsClopen.{u1} X _inst_1 U), Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (LocallyConstant.{u1, u2} X Y _inst_1) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u1, u2} X Y _inst_1) (LocallyConstant.charFn.{u1, u2} X Y _inst_1 _inst_2 U hU) x) (OfNat.ofNat.{u2} Y 0 (Zero.toOfNat0.{u2} Y (MulZeroOneClass.toZero.{u2} Y _inst_2)))) (Not (Membership.mem.{u1, u1} X (Set.{u1} X) (Set.instMembershipSet.{u1} X) x U))
Case conversion may be inaccurate. Consider using '#align locally_constant.char_fn_eq_zero LocallyConstant.charFn_eq_zeroₓ'. -/
theorem charFn_eq_zero [Nontrivial Y] (x : X) (hU : IsClopen U) : charFn Y hU x = (0 : Y) ↔ x ∉ U :=
  Set.indicator_eq_zero_iff_not_mem _
#align locally_constant.char_fn_eq_zero LocallyConstant.charFn_eq_zero

#print LocallyConstant.charFn_inj /-
theorem charFn_inj [Nontrivial Y] (hU : IsClopen U) (hV : IsClopen V)
    (h : charFn Y hU = charFn Y hV) : U = V :=
  Set.indicator_one_inj Y <| coe_inj.mpr h
#align locally_constant.char_fn_inj LocallyConstant.charFn_inj
-/

end CharFn

@[to_additive]
instance [Div Y] : Div (LocallyConstant X Y)
    where div f g := ⟨f / g, f.IsLocallyConstant.div g.IsLocallyConstant⟩

#print LocallyConstant.coe_div /-
@[to_additive]
theorem coe_div [Div Y] (f g : LocallyConstant X Y) : ⇑(f / g) = f / g :=
  rfl
#align locally_constant.coe_div LocallyConstant.coe_div
#align locally_constant.coe_sub LocallyConstant.coe_sub
-/

#print LocallyConstant.div_apply /-
@[to_additive]
theorem div_apply [Div Y] (f g : LocallyConstant X Y) (x : X) : (f / g) x = f x / g x :=
  rfl
#align locally_constant.div_apply LocallyConstant.div_apply
#align locally_constant.sub_apply LocallyConstant.sub_apply
-/

@[to_additive]
instance [Semigroup Y] : Semigroup (LocallyConstant X Y) :=
  { LocallyConstant.hasMul with
    mul_assoc := by
      intros
      ext
      simp only [mul_apply, mul_assoc] }

instance [SemigroupWithZero Y] : SemigroupWithZero (LocallyConstant X Y) :=
  { LocallyConstant.mulZeroClass, LocallyConstant.semigroup with }

@[to_additive]
instance [CommSemigroup Y] : CommSemigroup (LocallyConstant X Y) :=
  { LocallyConstant.semigroup with
    mul_comm := by
      intros
      ext
      simp only [mul_apply, mul_comm] }

@[to_additive]
instance [Monoid Y] : Monoid (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.mulOneClass with mul := (· * ·) }

instance [AddMonoidWithOne Y] : AddMonoidWithOne (LocallyConstant X Y) :=
  { LocallyConstant.addMonoid,
    LocallyConstant.hasOne with
    natCast := fun n => const X n
    natCast_zero := by ext <;> simp [Nat.cast]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast] }

@[to_additive]
instance [CommMonoid Y] : CommMonoid (LocallyConstant X Y) :=
  { LocallyConstant.commSemigroup, LocallyConstant.monoid with }

@[to_additive]
instance [Group Y] : Group (LocallyConstant X Y) :=
  { LocallyConstant.monoid, LocallyConstant.hasInv,
    LocallyConstant.hasDiv with
    mul_left_inv := by
      intros
      ext
      simp only [mul_apply, inv_apply, one_apply, mul_left_inv]
    div_eq_mul_inv := by
      intros
      ext
      simp only [mul_apply, inv_apply, div_apply, div_eq_mul_inv] }

@[to_additive]
instance [CommGroup Y] : CommGroup (LocallyConstant X Y) :=
  { LocallyConstant.commMonoid, LocallyConstant.group with }

instance [Distrib Y] : Distrib (LocallyConstant X Y) :=
  { LocallyConstant.hasAdd,
    LocallyConstant.hasMul with
    left_distrib := by
      intros
      ext
      simp only [mul_apply, add_apply, mul_add]
    right_distrib := by
      intros
      ext
      simp only [mul_apply, add_apply, add_mul] }

instance [NonUnitalNonAssocSemiring Y] : NonUnitalNonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.addCommMonoid, LocallyConstant.hasMul, LocallyConstant.distrib,
    LocallyConstant.mulZeroClass with }

instance [NonUnitalSemiring Y] : NonUnitalSemiring (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocSemiring with }

instance [NonAssocSemiring Y] : NonAssocSemiring (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.addMonoidWithOne,
    LocallyConstant.nonUnitalNonAssocSemiring with }

/- warning: locally_constant.const_ring_hom -> LocallyConstant.constRingHom is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NonAssocSemiring.{u2} Y], RingHom.{u2, max u1 u2} Y (LocallyConstant.{u1, u2} X Y _inst_1) _inst_2 (LocallyConstant.nonAssocSemiring.{u1, u2} X Y _inst_1 _inst_2)
but is expected to have type
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NonAssocSemiring.{u2} Y], RingHom.{u2, max u2 u1} Y (LocallyConstant.{u1, u2} X Y _inst_1) _inst_2 (LocallyConstant.instNonAssocSemiringLocallyConstant.{u1, u2} X Y _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align locally_constant.const_ring_hom LocallyConstant.constRingHomₓ'. -/
/-- The constant-function embedding, as a ring hom.  -/
@[simps]
def constRingHom [NonAssocSemiring Y] : Y →+* LocallyConstant X Y :=
  { constMonoidHom, constAddMonoidHom with toFun := const X }
#align locally_constant.const_ring_hom LocallyConstant.constRingHom

instance [Semiring Y] : Semiring (LocallyConstant X Y) :=
  { LocallyConstant.nonAssocSemiring, LocallyConstant.monoid with }

instance [NonUnitalCommSemiring Y] : NonUnitalCommSemiring (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalSemiring, LocallyConstant.commSemigroup with }

instance [CommSemiring Y] : CommSemiring (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.commMonoid with }

instance [NonUnitalNonAssocRing Y] : NonUnitalNonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.addCommGroup, LocallyConstant.hasMul, LocallyConstant.distrib,
    LocallyConstant.mulZeroClass with }

instance [NonUnitalRing Y] : NonUnitalRing (LocallyConstant X Y) :=
  { LocallyConstant.semigroup, LocallyConstant.nonUnitalNonAssocRing with }

instance [NonAssocRing Y] : NonAssocRing (LocallyConstant X Y) :=
  { LocallyConstant.mulOneClass, LocallyConstant.nonUnitalNonAssocRing with }

instance [Ring Y] : Ring (LocallyConstant X Y) :=
  { LocallyConstant.semiring, LocallyConstant.addCommGroup with }

instance [NonUnitalCommRing Y] : NonUnitalCommRing (LocallyConstant X Y) :=
  { LocallyConstant.nonUnitalCommSemiring, LocallyConstant.nonUnitalRing with }

instance [CommRing Y] : CommRing (LocallyConstant X Y) :=
  { LocallyConstant.commSemiring, LocallyConstant.ring with }

variable {R : Type _}

instance [SMul R Y] : SMul R (LocallyConstant X Y)
    where smul r f :=
    { toFun := r • f
      IsLocallyConstant := (f.IsLocallyConstant.comp ((· • ·) r) : _) }

#print LocallyConstant.coe_smul /-
@[simp]
theorem coe_smul [SMul R Y] (r : R) (f : LocallyConstant X Y) : ⇑(r • f) = r • f :=
  rfl
#align locally_constant.coe_smul LocallyConstant.coe_smul
-/

#print LocallyConstant.smul_apply /-
theorem smul_apply [SMul R Y] (r : R) (f : LocallyConstant X Y) (x : X) : (r • f) x = r • f x :=
  rfl
#align locally_constant.smul_apply LocallyConstant.smul_apply
-/

instance [Monoid R] [MulAction R Y] : MulAction R (LocallyConstant X Y) :=
  Function.Injective.mulAction _ coe_injective fun _ _ => rfl

instance [Monoid R] [AddMonoid Y] [DistribMulAction R Y] :
    DistribMulAction R (LocallyConstant X Y) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective fun _ _ => rfl

instance [Semiring R] [AddCommMonoid Y] [Module R Y] : Module R (LocallyConstant X Y) :=
  Function.Injective.module R coeFnAddMonoidHom coe_injective fun _ _ => rfl

section Algebra

variable [CommSemiring R] [Semiring Y] [Algebra R Y]

instance : Algebra R (LocallyConstant X Y)
    where
  toRingHom := constRingHom.comp <| algebraMap R Y
  commutes' := by
    intros
    ext
    exact Algebra.commutes' _ _
  smul_def' := by
    intros
    ext
    exact Algebra.smul_def' _ _

/- warning: locally_constant.coe_algebra_map -> LocallyConstant.coe_algebraMap is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u1} X] {R : Type.{u3}} [_inst_2 : CommSemiring.{u3} R] [_inst_3 : Semiring.{u2} Y] [_inst_4 : Algebra.{u3, u2} R Y _inst_2 _inst_3] (r : R), Eq.{max (succ u1) (succ u2)} (X -> Y) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (LocallyConstant.{u1, u2} X Y _inst_1) (fun (_x : LocallyConstant.{u1, u2} X Y _inst_1) => X -> Y) (LocallyConstant.hasCoeToFun.{u1, u2} X Y _inst_1) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (RingHom.{u3, max u1 u2} R (LocallyConstant.{u1, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (LocallyConstant.semiring.{u1, u2} X Y _inst_1 _inst_3))) (fun (_x : RingHom.{u3, max u1 u2} R (LocallyConstant.{u1, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (LocallyConstant.semiring.{u1, u2} X Y _inst_1 _inst_3))) => R -> (LocallyConstant.{u1, u2} X Y _inst_1)) (RingHom.hasCoeToFun.{u3, max u1 u2} R (LocallyConstant.{u1, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (LocallyConstant.{u1, u2} X Y _inst_1) (LocallyConstant.semiring.{u1, u2} X Y _inst_1 _inst_3))) (algebraMap.{u3, max u1 u2} R (LocallyConstant.{u1, u2} X Y _inst_1) _inst_2 (LocallyConstant.semiring.{u1, u2} X Y _inst_1 _inst_3) (LocallyConstant.algebra.{u1, u2, u3} X Y _inst_1 R _inst_2 _inst_3 _inst_4)) r)) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (RingHom.{u3, max u1 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (X -> Y) (Pi.semiring.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_3)))) (fun (_x : RingHom.{u3, max u1 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (X -> Y) (Pi.semiring.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_3)))) => R -> X -> Y) (RingHom.hasCoeToFun.{u3, max u1 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)) (Semiring.toNonAssocSemiring.{max u1 u2} (X -> Y) (Pi.semiring.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_3)))) (algebraMap.{u3, max u1 u2} R (X -> Y) _inst_2 (Pi.semiring.{u1, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_3)) (Function.algebra.{u3, u1, u2} R X Y _inst_2 _inst_3 _inst_4)) r)
but is expected to have type
  forall {X : Type.{u3}} {Y : Type.{u2}} [_inst_1 : TopologicalSpace.{u3} X] {R : Type.{u1}} [_inst_2 : CommSemiring.{u1} R] [_inst_3 : Semiring.{u2} Y] [_inst_4 : Algebra.{u1, u2} R Y _inst_2 _inst_3] (r : R), Eq.{max (succ u3) (succ u2)} (forall (ᾰ : X), (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) ᾰ) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => LocallyConstant.{u3, u2} X Y _inst_1) r) X (fun (_x : X) => (fun (x._@.Mathlib.Topology.LocallyConstant.Basic._hyg.2185 : X) => Y) _x) (LocallyConstant.instFunLikeLocallyConstant.{u3, u2} X Y _inst_1) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u2 u3} R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => LocallyConstant.{u3, u2} X Y _inst_1) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3))) R (LocallyConstant.{u3, u2} X Y _inst_1) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (LocallyConstant.{u3, u2} X Y _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3)))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3))) R (LocallyConstant.{u3, u2} X Y _inst_1) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u2 u3} R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3))) R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3)) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (LocallyConstant.{u3, u2} X Y _inst_1) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u2 u3} (LocallyConstant.{u3, u2} X Y _inst_1) (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3)))))) (algebraMap.{u1, max u2 u3} R (LocallyConstant.{u3, u2} X Y _inst_1) _inst_2 (LocallyConstant.instSemiringLocallyConstant.{u3, u2} X Y _inst_1 _inst_3) (LocallyConstant.instAlgebraLocallyConstantInstSemiringLocallyConstant.{u3, u2, u1} X Y _inst_1 R _inst_2 _inst_3 _inst_4)) r)) (FunLike.coe.{max (max (succ u3) (succ u2)) (succ u1), succ u1, max (succ u3) (succ u2)} (RingHom.{u1, max u3 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => X -> Y) _x) (MulHomClass.toFunLike.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3)))) R (X -> Y) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{max u3 u2} (X -> Y) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (X -> Y) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3))))) (NonUnitalRingHomClass.toMulHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3)))) R (X -> Y) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u3 u2} (X -> Y) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3)))) (RingHomClass.toNonUnitalRingHomClass.{max (max u3 u2) u1, u1, max u3 u2} (RingHom.{u1, max u3 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3)))) R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3))) (RingHom.instRingHomClassRingHom.{u1, max u3 u2} R (X -> Y) (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_2)) (Semiring.toNonAssocSemiring.{max u3 u2} (X -> Y) (Pi.semiring.{u3, u2} X (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) (fun (i : X) => _inst_3))))))) (algebraMap.{u1, max u3 u2} R (X -> Y) _inst_2 (Pi.semiring.{u3, u2} X (fun (ᾰ : X) => Y) (fun (i : X) => _inst_3)) (Pi.algebra.{u3, u2, u1} X R (fun (a._@.Mathlib.Topology.LocallyConstant.Algebra._hyg.2488 : X) => Y) _inst_2 (fun (i : X) => _inst_3) (fun (i : X) => _inst_4))) r)
Case conversion may be inaccurate. Consider using '#align locally_constant.coe_algebra_map LocallyConstant.coe_algebraMapₓ'. -/
@[simp]
theorem coe_algebraMap (r : R) : ⇑(algebraMap R (LocallyConstant X Y) r) = algebraMap R (X → Y) r :=
  rfl
#align locally_constant.coe_algebra_map LocallyConstant.coe_algebraMap

end Algebra

end LocallyConstant

