/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module number_theory.legendre_symbol.mul_character
! leanprover-community/mathlib commit f0c8bf9245297a541f468be517f1bde6195105e9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.CharP.Basic
import Mathbin.Algebra.EuclideanDomain.Instances
import Mathbin.Data.Fintype.Units

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be a commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `mul_char` for the definitions and results.

## Main results

We show that the multiplicative characters form a group (if `R'` is commutative);
see `mul_char.comm_group`. We also provide an equivalence with the
homomorphisms `Rˣ →* R'ˣ`; see `mul_char.equiv_to_unit_hom`.

We define a multiplicative character to be *quadratic* if its values
are among `0`, `1` and `-1`, and we prove some properties of quadratic characters.

Finally, we show that the sum of all values of a nontrivial multiplicative
character vanishes; see `mul_char.is_nontrivial.sum_eq_zero`.

## Tags

multiplicative character
-/


section DefinitionAndGroup

/-!
### Definitions related to multiplicative characters

Even though the intended use is when domain and target of the characters
are commutative rings, we define them in the more general setting when
the domain is a commutative monoid and the target is a commutative monoid
with zero. (We need a zero in the target, since non-units are supposed
to map to zero.)

In this setting, there is an equivalence between multiplicative characters
`R → R'` and group homomorphisms `Rˣ → R'ˣ`, and the multiplicative characters
have a natural structure as a commutative group.
-/


universe u v

section Defi

-- The domain of our multiplicative characters
variable (R : Type u) [CommMonoid R]

-- The target
variable (R' : Type v) [CommMonoidWithZero R']

#print MulChar /-
/-- Define a structure for multiplicative characters.
A multiplicative character from a commutative monoid `R` to a commutative monoid with zero `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero. -/
structure MulChar extends MonoidHom R R' where
  map_nonunit' : ∀ a : R, ¬IsUnit a → to_fun a = 0
#align mul_char MulChar
-/

#print MulCharClass /-
/-- This is the corresponding extension of `monoid_hom_class`. -/
class MulCharClass (F : Type _) (R R' : outParam <| Type _) [CommMonoid R]
  [CommMonoidWithZero R'] extends MonoidHomClass F R R' where
  map_nonunit : ∀ (χ : F) {a : R} (ha : ¬IsUnit a), χ a = 0
#align mul_char_class MulCharClass
-/

attribute [simp] MulCharClass.map_nonunit

end Defi

section Group

namespace MulChar

-- The domain of our multiplicative characters
variable {R : Type u} [CommMonoid R]

-- The target
variable {R' : Type v} [CommMonoidWithZero R']

#print MulChar.coeToFun /-
instance coeToFun : CoeFun (MulChar R R') fun _ => R → R' :=
  ⟨fun χ => χ.toFun⟩
#align mul_char.coe_to_fun MulChar.coeToFun
-/

#print MulChar.Simps.apply /-
/-- See note [custom simps projection] -/
protected def Simps.apply (χ : MulChar R R') : R → R' :=
  χ
#align mul_char.simps.apply MulChar.Simps.apply
-/

initialize_simps_projections MulChar (to_monoid_hom_to_fun → apply, -toMonoidHom)

section trivial

variable (R R')

#print MulChar.trivial /-
/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
noncomputable def trivial : MulChar R R'
    where
  toFun := by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto
#align mul_char.trivial MulChar.trivial
-/

end trivial

/- warning: mul_char.coe_coe -> MulChar.coe_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (_x : MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => R -> R') (MulChar.toMonoidHom.{u1, u2} R _inst_1 R' _inst_2 χ)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => R -> R') (MonoidHom.hasCoeToFun.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.toMonoidHom.{u1, u2} R _inst_1 R' _inst_2 χ)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} (forall (a : R), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => R') a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => R') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R R' (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (MulChar.toMonoidHom.{u1, u2} R _inst_1 R' _inst_2 χ)) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ)
Case conversion may be inaccurate. Consider using '#align mul_char.coe_coe MulChar.coe_coeₓ'. -/
@[simp]
theorem coe_coe (χ : MulChar R R') : (χ.toMonoidHom : R → R') = χ :=
  rfl
#align mul_char.coe_coe MulChar.coe_coe

/- warning: mul_char.to_fun_eq_coe -> MulChar.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} (R -> R') (MonoidHom.toFun.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulChar.toMonoidHom.{u1, u2} R _inst_1 R' _inst_2 χ)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} (R -> R') (OneHom.toFun.{u1, u2} R R' (MulOneClass.toOne.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toOne.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.toOneHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulChar.toMonoidHom.{u1, u2} R _inst_1 R' _inst_2 χ))) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ)
Case conversion may be inaccurate. Consider using '#align mul_char.to_fun_eq_coe MulChar.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe (χ : MulChar R R') : χ.toFun = χ :=
  rfl
#align mul_char.to_fun_eq_coe MulChar.toFun_eq_coe

/- warning: mul_char.coe_mk -> MulChar.coe_mk is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (hf : forall (a : R), (Not (IsUnit.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) -> (Eq.{succ u2} R' (MonoidHom.toFun.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) f a) (OfNat.ofNat.{u2} R' 0 (OfNat.mk.{u2} R' 0 (Zero.zero.{u2} R' (MulZeroClass.toHasZero.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))))))), Eq.{max (succ u1) (succ u2)} ((fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.mk.{u1, u2} R _inst_1 R' _inst_2 f hf)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (MulChar.mk.{u1, u2} R _inst_1 R' _inst_2 f hf)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => R -> R') (MonoidHom.hasCoeToFun.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) f)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (hf : forall (a : R), (Not (IsUnit.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) -> (Eq.{succ u2} R' (OneHom.toFun.{u1, u2} R R' (MulOneClass.toOne.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toOne.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.toOneHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) f) a) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' _inst_2))))), Eq.{max (succ u1) (succ u2)} (R -> R') (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (MulChar.mk.{u1, u2} R _inst_1 R' _inst_2 f hf)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R) => R') _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R R' (MulOneClass.toMul.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} R R' (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) f)
Case conversion may be inaccurate. Consider using '#align mul_char.coe_mk MulChar.coe_mkₓ'. -/
@[simp]
theorem coe_mk (f : R →* R') (hf) : (MulChar.mk f hf : R → R') = f :=
  rfl
#align mul_char.coe_mk MulChar.coe_mk

#print MulChar.ext' /-
/-- Extensionality. See `ext` below for the version that will actually be used. -/
theorem ext' {χ χ' : MulChar R R'} (h : ∀ a, χ a = χ' a) : χ = χ' :=
  by
  cases χ
  cases χ'
  congr
  exact MonoidHom.ext h
#align mul_char.ext' MulChar.ext'
-/

instance : MulCharClass (MulChar R R') R R'
    where
  coe χ := χ.toMonoidHom.toFun
  coe_injective' f g h := ext' fun a => congr_fun h a
  map_mul χ := χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit'

/- warning: mul_char.map_nonunit -> MulChar.map_nonunit is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) {a : R}, (Not (IsUnit.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) -> (Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ a) (OfNat.ofNat.{u2} R' 0 (OfNat.mk.{u2} R' 0 (Zero.zero.{u2} R' (MulZeroClass.toHasZero.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) {a : R}, (Not (IsUnit.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) -> (Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ a) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' _inst_2))))
Case conversion may be inaccurate. Consider using '#align mul_char.map_nonunit MulChar.map_nonunitₓ'. -/
theorem map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0 :=
  χ.map_nonunit' a ha
#align mul_char.map_nonunit MulChar.map_nonunit

#print MulChar.ext /-
/-- Extensionality. Since `mul_char`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
theorem ext {χ χ' : MulChar R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' :=
  by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]
#align mul_char.ext MulChar.ext
-/

#print MulChar.ext_iff /-
theorem ext_iff {χ χ' : MulChar R R'} : χ = χ' ↔ ∀ a : Rˣ, χ a = χ' a :=
  ⟨by
    rintro rfl a
    rfl, ext⟩
#align mul_char.ext_iff MulChar.ext_iff
-/

/-!
### Equivalence of multiplicative characters with homomorphisms on units

We show that restriction / extension by zero gives an equivalence
between `mul_char R R'` and `Rˣ →* R'ˣ`.
-/


/- warning: mul_char.to_unit_hom -> MulChar.toUnitHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], (MulChar.{u1, u2} R _inst_1 R' _inst_2) -> (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], (MulChar.{u1, u2} R _inst_1 R' _inst_2) -> (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))
Case conversion may be inaccurate. Consider using '#align mul_char.to_unit_hom MulChar.toUnitHomₓ'. -/
/-- Turn a `mul_char` into a homomorphism between the unit groups. -/
def toUnitHom (χ : MulChar R R') : Rˣ →* R'ˣ :=
  Units.map χ
#align mul_char.to_unit_hom MulChar.toUnitHom

/- warning: mul_char.coe_to_unit_hom -> MulChar.coe_toUnitHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (coeBase.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (Units.hasCoe.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) -> (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.toUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) a)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (coeBase.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (Units.hasCoe.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (Units.val.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (fun (_x : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulOneClass.toMul.{u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (MulChar.toUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) a)) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ (Units.val.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a))
Case conversion may be inaccurate. Consider using '#align mul_char.coe_to_unit_hom MulChar.coe_toUnitHomₓ'. -/
theorem coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a :=
  rfl
#align mul_char.coe_to_unit_hom MulChar.coe_toUnitHom

/- warning: mul_char.of_unit_hom -> MulChar.ofUnitHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) -> (MulChar.{u1, u2} R _inst_1 R' _inst_2)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) -> (MulChar.{u1, u2} R _inst_1 R' _inst_2)
Case conversion may be inaccurate. Consider using '#align mul_char.of_unit_hom MulChar.ofUnitHomₓ'. -/
/-- Turn a homomorphism between unit groups into a `mul_char`. -/
noncomputable def ofUnitHom (f : Rˣ →* R'ˣ) : MulChar R R'
    where
  toFun := by classical exact fun x => if hx : IsUnit x then f hx.Unit else 0
  map_one' := by
    have h1 : (is_unit_one.unit : Rˣ) = 1 := units.eq_iff.mp rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp only [hx, IsUnit.mul_iff, true_and_iff, dif_pos]
        by_cases hy : IsUnit y
        · simp only [hy, dif_pos]
          have hm : (is_unit.mul_iff.mpr ⟨hx, hy⟩).Unit = hx.unit * hy.unit := units.eq_iff.mp rfl
          rw [hm, map_mul]
          norm_cast
        · simp only [hy, not_false_iff, dif_neg, MulZeroClass.mul_zero]
      · simp only [hx, IsUnit.mul_iff, false_and_iff, not_false_iff, dif_neg, MulZeroClass.zero_mul]
  map_nonunit' := by
    intro a ha
    simp only [ha, not_false_iff, dif_neg]
#align mul_char.of_unit_hom MulChar.ofUnitHom

/- warning: mul_char.of_unit_hom_coe -> MulChar.ofUnitHom_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (MulChar.ofUnitHom.{u1, u2} R _inst_1 R' _inst_2 f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (coeBase.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (Units.hasCoe.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) a)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (coeBase.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (Units.hasCoe.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) -> (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) f a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (MulChar.ofUnitHom.{u1, u2} R _inst_1 R' _inst_2 f) (Units.val.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) (Units.val.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (fun (_x : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulOneClass.toMul.{u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) f a))
Case conversion may be inaccurate. Consider using '#align mul_char.of_unit_hom_coe MulChar.ofUnitHom_coeₓ'. -/
theorem ofUnitHom_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : of_unit_hom f ↑a = f a := by simp [of_unit_hom]
#align mul_char.of_unit_hom_coe MulChar.ofUnitHom_coe

/- warning: mul_char.equiv_to_unit_hom -> MulChar.equivToUnitHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))
Case conversion may be inaccurate. Consider using '#align mul_char.equiv_to_unit_hom MulChar.equivToUnitHomₓ'. -/
/-- The equivalence between multiplicative characters and homomorphisms of unit groups. -/
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ)
    where
  toFun := to_unit_hom
  invFun := of_unit_hom
  left_inv := by
    intro χ
    ext x
    rw [of_unit_hom_coe, coe_to_unit_hom]
  right_inv := by
    intro f
    ext x
    rw [coe_to_unit_hom, of_unit_hom_coe]
#align mul_char.equiv_to_unit_hom MulChar.equivToUnitHom

/- warning: mul_char.to_unit_hom_eq -> MulChar.toUnitHom_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.toUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) => (MulChar.{u1, u2} R _inst_1 R' _inst_2) -> (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2) χ)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.toUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MulChar.{u1, u2} R _inst_1 R' _inst_2) => MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2) χ)
Case conversion may be inaccurate. Consider using '#align mul_char.to_unit_hom_eq MulChar.toUnitHom_eqₓ'. -/
@[simp]
theorem toUnitHom_eq (χ : MulChar R R') : to_unit_hom χ = equiv_to_unit_hom χ :=
  rfl
#align mul_char.to_unit_hom_eq MulChar.toUnitHom_eq

/- warning: mul_char.of_unit_hom_eq -> MulChar.ofUnitHom_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))), Eq.{max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.ofUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) (coeFn.{max 1 (max (max (succ u2) (succ u1)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u2) (succ u1), max (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) => (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) -> (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2)) χ)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))), Eq.{max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.ofUnitHom.{u1, u2} R _inst_1 R' _inst_2 χ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => MulChar.{u1, u2} R _inst_1 R' _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2)) χ)
Case conversion may be inaccurate. Consider using '#align mul_char.of_unit_hom_eq MulChar.ofUnitHom_eqₓ'. -/
@[simp]
theorem ofUnitHom_eq (χ : Rˣ →* R'ˣ) : of_unit_hom χ = equiv_to_unit_hom.symm χ :=
  rfl
#align mul_char.of_unit_hom_eq MulChar.ofUnitHom_eq

/- warning: mul_char.coe_equiv_to_unit_hom -> MulChar.coe_equivToUnitHom is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (coeBase.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (Units.hasCoe.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) -> (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (coeFn.{max 1 (max (max (succ u1) (succ u2)) (succ u2) (succ u1)) (max (succ u2) (succ u1)) (succ u1) (succ u2), max (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) => (MulChar.{u1, u2} R _inst_1 R' _inst_2) -> (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2) χ) a)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (coeBase.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (Units.hasCoe.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (Units.val.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MulChar.{u1, u2} R _inst_1 R' _inst_2) => MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) χ) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (fun (_x : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MulChar.{u1, u2} R _inst_1 R' _inst_2) => MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) χ) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulOneClass.toMul.{u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MulChar.{u1, u2} R _inst_1 R' _inst_2) => MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) χ) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MulChar.{u1, u2} R _inst_1 R' _inst_2) => MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2) χ) a)) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ (Units.val.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a))
Case conversion may be inaccurate. Consider using '#align mul_char.coe_equiv_to_unit_hom MulChar.coe_equivToUnitHomₓ'. -/
@[simp]
theorem coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equiv_to_unit_hom χ a) = χ a :=
  coe_to_unit_hom χ a
#align mul_char.coe_equiv_to_unit_hom MulChar.coe_equivToUnitHom

/- warning: mul_char.equiv_unit_hom_symm_coe -> MulChar.equiv_unit_hom_symm_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (coeFn.{max 1 (max (max (succ u2) (succ u1)) (succ u1) (succ u2)) (max (succ u1) (succ u2)) (succ u2) (succ u1), max (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) => (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) -> (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2)) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (coeBase.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (Units.hasCoe.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) a)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (coeBase.{succ u2, succ u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) R' (Units.hasCoe.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) -> (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHom.hasCoeToFun.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.mulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.mulOneClass.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) f a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (f : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (fun (_x : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) => MulChar.{u1, u2} R _inst_1 R' _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.{u1, u2} R _inst_1 R' _inst_2)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MulChar.equivToUnitHom.{u1, u2} R _inst_1 R' _inst_2)) f) (Units.val.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) (Units.val.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (fun (_x : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) => Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MulOneClass.toMul.{u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))) (MulOneClass.toMul.{u2} (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (MonoidHom.monoidHomClass.{u1, u2} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))) (Units.instMulOneClassUnits.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) (Units.instMulOneClassUnits.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) f a))
Case conversion may be inaccurate. Consider using '#align mul_char.equiv_unit_hom_symm_coe MulChar.equiv_unit_hom_symm_coeₓ'. -/
@[simp]
theorem equiv_unit_hom_symm_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : equiv_to_unit_hom.symm f ↑a = f a :=
  of_unit_hom_coe f a
#align mul_char.equiv_unit_hom_symm_coe MulChar.equiv_unit_hom_symm_coe

/-!
### Commutative group structure on multiplicative characters

The multiplicative characters `R → R'` form a commutative group.
-/


/- warning: mul_char.map_one -> MulChar.map_one is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (MulOneClass.toHasOne.{u1} R (Monoid.toMulOneClass.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))))) (OfNat.ofNat.{u2} R' 1 (OfNat.mk.{u2} R' 1 (One.one.{u2} R' (MulOneClass.toHasOne.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Monoid.toOne.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) (OfNat.ofNat.{u2} R' 1 (One.toOfNat1.{u2} R' (Monoid.toOne.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))
Case conversion may be inaccurate. Consider using '#align mul_char.map_one MulChar.map_oneₓ'. -/
protected theorem map_one (χ : MulChar R R') : χ (1 : R) = 1 :=
  χ.map_one'
#align mul_char.map_one MulChar.map_one

/- warning: mul_char.map_zero -> MulChar.map_zero is a dubious translation:
lean 3 declaration is
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : CommMonoidWithZero.{u1} R] [_inst_4 : Nontrivial.{u1} R] (χ : MulChar.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2) (fun (_x : MulChar.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2) χ (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (MulZeroOneClass.toMulZeroClass.{u1} R (MonoidWithZero.toMulZeroOneClass.{u1} R (CommMonoidWithZero.toMonoidWithZero.{u1} R _inst_3)))))))) (OfNat.ofNat.{u2} R' 0 (OfNat.mk.{u2} R' 0 (Zero.zero.{u2} R' (MulZeroClass.toHasZero.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))))
but is expected to have type
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : CommMonoidWithZero.{u1} R] [_inst_4 : Nontrivial.{u1} R] (χ : MulChar.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R (CommMonoidWithZero.toCommMonoid.{u1} R _inst_3) R' _inst_2 χ (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R _inst_3)))) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_char.map_zero MulChar.map_zeroₓ'. -/
/-- If the domain has a zero (and is nontrivial), then `χ 0 = 0`. -/
protected theorem map_zero {R : Type u} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    χ (0 : R) = 0 := by rw [map_nonunit χ not_isUnit_zero]
#align mul_char.map_zero MulChar.map_zero

/- warning: mul_char.map_ring_char -> MulChar.map_ringChar is a dubious translation:
lean 3 declaration is
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : CommRing.{u1} R] [_inst_4 : Nontrivial.{u1} R] (χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2) (fun (_x : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2) χ ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u1} Nat R (CoeTCₓ.coe.{1, succ u1} Nat R (Nat.castCoe.{u1} R (AddMonoidWithOne.toNatCast.{u1} R (AddGroupWithOne.toAddMonoidWithOne.{u1} R (AddCommGroupWithOne.toAddGroupWithOne.{u1} R (Ring.toAddCommGroupWithOne.{u1} R (CommRing.toRing.{u1} R _inst_3)))))))) (ringChar.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_3)))))) (OfNat.ofNat.{u2} R' 0 (OfNat.mk.{u2} R' 0 (Zero.zero.{u2} R' (MulZeroClass.toHasZero.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))))
but is expected to have type
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : CommRing.{u1} R] [_inst_4 : Nontrivial.{u1} R] (χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_3) R' _inst_2 χ (Nat.cast.{u1} R (Semiring.toNatCast.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3))) (ringChar.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_3)))))) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' _inst_2)))
Case conversion may be inaccurate. Consider using '#align mul_char.map_ring_char MulChar.map_ringCharₓ'. -/
/-- If the domain is a ring `R`, then `χ (ring_char R) = 0`. -/
theorem map_ringChar {R : Type u} [CommRing R] [Nontrivial R] (χ : MulChar R R') :
    χ (ringChar R) = 0 := by rw [ringChar.Nat.cast_ringChar, χ.map_zero]
#align mul_char.map_ring_char MulChar.map_ringChar

#print MulChar.hasOne /-
noncomputable instance hasOne : One (MulChar R R') :=
  ⟨trivial R R'⟩
#align mul_char.has_one MulChar.hasOne
-/

#print MulChar.inhabited /-
noncomputable instance inhabited : Inhabited (MulChar R R') :=
  ⟨1⟩
#align mul_char.inhabited MulChar.inhabited
-/

/- warning: mul_char.one_apply_coe -> MulChar.one_apply_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (OfNat.ofNat.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) 1 (OfNat.mk.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) 1 (One.one.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasOne.{u1, u2} R _inst_1 R' _inst_2)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (coeBase.{succ u1, succ u1} (Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)) R (Units.hasCoe.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1))))) a)) (OfNat.ofNat.{u2} R' 1 (OfNat.mk.{u2} R' 1 (One.one.{u2} R' (MulOneClass.toHasOne.{u2} R' (MulZeroOneClass.toMulOneClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (a : Units.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1)), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (OfNat.ofNat.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) 1 (One.toOfNat1.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasOne.{u1, u2} R _inst_1 R' _inst_2))) (Units.val.{u1} R (CommMonoid.toMonoid.{u1} R _inst_1) a)) (OfNat.ofNat.{u2} R' 1 (One.toOfNat1.{u2} R' (Monoid.toOne.{u2} R' (MonoidWithZero.toMonoid.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))
Case conversion may be inaccurate. Consider using '#align mul_char.one_apply_coe MulChar.one_apply_coeₓ'. -/
/-- Evaluation of the trivial character -/
@[simp]
theorem one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1 := by classical exact dif_pos a.is_unit
#align mul_char.one_apply_coe MulChar.one_apply_coe

#print MulChar.mul /-
/-- Multiplication of multiplicative characters. (This needs the target to be commutative.) -/
def mul (χ χ' : MulChar R R') : MulChar R R' :=
  { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp [map_nonunit χ ha] }
#align mul_char.mul MulChar.mul
-/

#print MulChar.hasMul /-
instance hasMul : Mul (MulChar R R') :=
  ⟨mul⟩
#align mul_char.has_mul MulChar.hasMul
-/

/- warning: mul_char.mul_apply -> MulChar.mul_apply is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (χ' : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : R), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (instHMul.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasMul.{u1, u2} R _inst_1 R' _inst_2)) χ χ') a) (HMul.hMul.{u2, u2, u2} R' R' R' (instHMul.{u2} R' (MulZeroClass.toHasMul.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ' a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (χ' : MulChar.{u1, u2} R _inst_1 R' _inst_2) (a : R), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (instHMul.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasMul.{u1, u2} R _inst_1 R' _inst_2)) χ χ') a) (HMul.hMul.{u2, u2, u2} R' R' R' (instHMul.{u2} R' (MulZeroClass.toMul.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2))))) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ a) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ' a))
Case conversion may be inaccurate. Consider using '#align mul_char.mul_apply MulChar.mul_applyₓ'. -/
theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
  rfl
#align mul_char.mul_apply MulChar.mul_apply

/- warning: mul_char.coe_to_fun_mul -> MulChar.coeToFun_mul is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (χ' : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{succ (max u1 u2)} (R -> R') (coeFn.{succ (max u1 u2), succ (max u1 u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (instHMul.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasMul.{u1, u2} R _inst_1 R' _inst_2)) χ χ')) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (R -> R') (R -> R') (R -> R') (instHMul.{max u1 u2} (R -> R') (Pi.instMul.{u1, u2} R (fun (ᾰ : R) => R') (fun (i : R) => MulZeroClass.toHasMul.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (fun (_x : MulChar.{u1, u2} R _inst_1 R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' _inst_2) χ'))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' _inst_2) (χ' : MulChar.{u1, u2} R _inst_1 R' _inst_2), Eq.{max (succ u1) (succ u2)} (R -> R') (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.{u1, u2} R _inst_1 R' _inst_2) (instHMul.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' _inst_2) (MulChar.hasMul.{u1, u2} R _inst_1 R' _inst_2)) χ χ')) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (R -> R') (R -> R') (R -> R') (instHMul.{max u1 u2} (R -> R') (Pi.instMul.{u1, u2} R (fun (ᾰ : R) => R') (fun (i : R) => MulZeroClass.toMul.{u2} R' (MulZeroOneClass.toMulZeroClass.{u2} R' (MonoidWithZero.toMulZeroOneClass.{u2} R' (CommMonoidWithZero.toMonoidWithZero.{u2} R' _inst_2)))))) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ) (MulChar.toFun'.{u1, u2} R _inst_1 R' _inst_2 χ'))
Case conversion may be inaccurate. Consider using '#align mul_char.coe_to_fun_mul MulChar.coeToFun_mulₓ'. -/
@[simp]
theorem coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ' :=
  rfl
#align mul_char.coe_to_fun_mul MulChar.coeToFun_mul

#print MulChar.one_mul /-
protected theorem one_mul (χ : MulChar R R') : (1 : MulChar R R') * χ = χ :=
  by
  ext
  simp
#align mul_char.one_mul MulChar.one_mul
-/

#print MulChar.mul_one /-
protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ :=
  by
  ext
  simp
#align mul_char.mul_one MulChar.mul_one
-/

#print MulChar.inv /-
/-- The inverse of a multiplicative character. We define it as `inverse ∘ χ`. -/
noncomputable def inv (χ : MulChar R R') : MulChar R R' :=
  {
    MonoidWithZero.inverse.toMonoidHom.comp
      χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }
#align mul_char.inv MulChar.inv
-/

#print MulChar.hasInv /-
noncomputable instance hasInv : Inv (MulChar R R') :=
  ⟨inv⟩
#align mul_char.has_inv MulChar.hasInv
-/

#print MulChar.inv_apply_eq_inv /-
/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`. -/
theorem inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = Ring.inverse (χ a) :=
  Eq.refl <| inv χ a
#align mul_char.inv_apply_eq_inv MulChar.inv_apply_eq_inv
-/

/- warning: mul_char.inv_apply_eq_inv' -> MulChar.inv_apply_eq_inv' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_3 : Field.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (a : R), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (fun (_x : MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (Inv.inv.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (MulChar.hasInv.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) χ) a) (Inv.inv.{u2} R' (DivInvMonoid.toHasInv.{u2} R' (DivisionRing.toDivInvMonoid.{u2} R' (Field.toDivisionRing.{u2} R' _inst_3))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (fun (_x : MulChar.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) => R -> R') (MulChar.coeToFun.{u1, u2} R _inst_1 R' (CommSemiring.toCommMonoidWithZero.{u2} R' (Semifield.toCommSemiring.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) χ a))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommMonoid.{u1} R] {R' : Type.{u2}} [_inst_3 : Field.{u2} R'] (χ : MulChar.{u1, u2} R _inst_1 R' (CommGroupWithZero.toCommMonoidWithZero.{u2} R' (Semifield.toCommGroupWithZero.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (a : R), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R _inst_1 R' (CommGroupWithZero.toCommMonoidWithZero.{u2} R' (Semifield.toCommGroupWithZero.{u2} R' (Field.toSemifield.{u2} R' _inst_3))) (Inv.inv.{max u1 u2} (MulChar.{u1, u2} R _inst_1 R' (CommGroupWithZero.toCommMonoidWithZero.{u2} R' (Semifield.toCommGroupWithZero.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) (MulChar.hasInv.{u1, u2} R _inst_1 R' (CommGroupWithZero.toCommMonoidWithZero.{u2} R' (Semifield.toCommGroupWithZero.{u2} R' (Field.toSemifield.{u2} R' _inst_3)))) χ) a) (Inv.inv.{u2} R' (Field.toInv.{u2} R' _inst_3) (MulChar.toFun'.{u1, u2} R _inst_1 R' (CommGroupWithZero.toCommMonoidWithZero.{u2} R' (Semifield.toCommGroupWithZero.{u2} R' (Field.toSemifield.{u2} R' _inst_3))) χ a))
Case conversion may be inaccurate. Consider using '#align mul_char.inv_apply_eq_inv' MulChar.inv_apply_eq_inv'ₓ'. -/
/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`.
Variant when the target is a field -/
theorem inv_apply_eq_inv' {R' : Type v} [Field R'] (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ :=
  (inv_apply_eq_inv χ a).trans <| Ring.inverse_eq_inv (χ a)
#align mul_char.inv_apply_eq_inv' MulChar.inv_apply_eq_inv'

#print MulChar.inv_apply /-
/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
theorem inv_apply {R : Type u} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = χ (Ring.inverse a) := by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (· * ·) (χ a) using IsUnit.mul_right_injective h
    rw [Ring.mul_inverse_cancel _ h, ← map_mul, Ring.mul_inverse_cancel _ ha, MulChar.map_one]
  · revert ha
    nontriviality R
    intro ha
    -- `nontriviality R` by itself doesn't do it
    rw [map_nonunit _ ha, Ring.inverse_non_unit a ha, MulChar.map_zero χ]
#align mul_char.inv_apply MulChar.inv_apply
-/

/- warning: mul_char.inv_apply' -> MulChar.inv_apply' is a dubious translation:
lean 3 declaration is
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : Field.{u1} R] (χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (a : R), Eq.{succ u2} R' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (fun (_x : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (Inv.inv.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (MulChar.hasInv.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) χ) a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (fun (_x : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) χ (Inv.inv.{u1} R (DivInvMonoid.toHasInv.{u1} R (DivisionRing.toDivInvMonoid.{u1} R (Field.toDivisionRing.{u1} R _inst_3))) a))
but is expected to have type
  forall {R' : Type.{u2}} [_inst_2 : CommMonoidWithZero.{u2} R'] {R : Type.{u1}} [_inst_3 : Field.{u1} R] (χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (a : R), Eq.{succ u2} R' (MulChar.toFun'.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2 (Inv.inv.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) (MulChar.hasInv.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2) χ) a) (MulChar.toFun'.{u1, u2} R (CommRing.toCommMonoid.{u1} R (EuclideanDomain.toCommRing.{u1} R (Field.toEuclideanDomain.{u1} R _inst_3))) R' _inst_2 χ (Inv.inv.{u1} R (Field.toInv.{u1} R _inst_3) a))
Case conversion may be inaccurate. Consider using '#align mul_char.inv_apply' MulChar.inv_apply'ₓ'. -/
/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
theorem inv_apply' {R : Type u} [Field R] (χ : MulChar R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
  (inv_apply χ a).trans <| congr_arg _ (Ring.inverse_eq_inv a)
#align mul_char.inv_apply' MulChar.inv_apply'

#print MulChar.inv_mul /-
/-- The product of a character with its inverse is the trivial character. -/
@[simp]
theorem inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1 :=
  by
  ext x
  rw [coe_to_fun_mul, Pi.mul_apply, inv_apply_eq_inv,
    Ring.inverse_mul_cancel _ (IsUnit.map _ x.is_unit), one_apply_coe]
#align mul_char.inv_mul MulChar.inv_mul
-/

#print MulChar.commGroup /-
/-- The commutative group structure on `mul_char R R'`. -/
noncomputable instance commGroup : CommGroup (MulChar R R') :=
  { one := 1
    mul := (· * ·)
    inv := Inv.inv
    mul_left_inv := inv_mul
    mul_assoc := by
      intro χ₁ χ₂ χ₃
      ext a
      simp [mul_assoc]
    mul_comm := by
      intro χ₁ χ₂
      ext a
      simp [mul_comm]
    one_mul
    mul_one }
#align mul_char.comm_group MulChar.commGroup
-/

#print MulChar.pow_apply_coe /-
/-- If `a` is a unit and `n : ℕ`, then `(χ ^ n) a = (χ a) ^ n`. -/
theorem pow_apply_coe (χ : MulChar R R') (n : ℕ) (a : Rˣ) : (χ ^ n) a = χ a ^ n :=
  by
  induction' n with n ih
  · rw [pow_zero, pow_zero, one_apply_coe]
  · rw [pow_succ, pow_succ, mul_apply, ih]
#align mul_char.pow_apply_coe MulChar.pow_apply_coe
-/

#print MulChar.pow_apply' /-
/-- If `n` is positive, then `(χ ^ n) a = (χ a) ^ n`. -/
theorem pow_apply' (χ : MulChar R R') {n : ℕ} (hn : 0 < n) (a : R) : (χ ^ n) a = χ a ^ n :=
  by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]
#align mul_char.pow_apply' MulChar.pow_apply'
-/

end MulChar

end Group

end DefinitionAndGroup

/-!
### Properties of multiplicative characters

We introduce the properties of being nontrivial or quadratic and prove
some basic facts about them.

We now assume that domain and target are commutative rings.
-/


section Properties

namespace MulChar

universe u v w

variable {R : Type u} [CommRing R] {R' : Type v} [CommRing R'] {R'' : Type w} [CommRing R'']

#print MulChar.IsNontrivial /-
/-- A multiplicative character is *nontrivial* if it takes a value `≠ 1` on a unit. -/
def IsNontrivial (χ : MulChar R R') : Prop :=
  ∃ a : Rˣ, χ a ≠ 1
#align mul_char.is_nontrivial MulChar.IsNontrivial
-/

#print MulChar.isNontrivial_iff /-
/-- A multiplicative character is nontrivial iff it is not the trivial character. -/
theorem isNontrivial_iff (χ : MulChar R R') : χ.IsNontrivial ↔ χ ≠ 1 := by
  simp only [is_nontrivial, Ne.def, ext_iff, not_forall, one_apply_coe]
#align mul_char.is_nontrivial_iff MulChar.isNontrivial_iff
-/

#print MulChar.IsQuadratic /-
/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
def IsQuadratic (χ : MulChar R R') : Prop :=
  ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1
#align mul_char.is_quadratic MulChar.IsQuadratic
-/

/- warning: mul_char.is_quadratic.eq_of_eq_coe -> MulChar.IsQuadratic.eq_of_eq_coe is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {R'' : Type.{u3}} [_inst_3 : CommRing.{u3} R''] {χ : MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)}, (MulChar.IsQuadratic.{u1, 0} R _inst_1 Int Int.commRing χ) -> (forall {χ' : MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)}, (MulChar.IsQuadratic.{u2, 0} R' _inst_2 Int Int.commRing χ') -> (forall [_inst_4 : Nontrivial.{u3} R''], (Ne.{1} Nat (ringChar.{u3} R'' (NonAssocRing.toNonAssocSemiring.{u3} R'' (Ring.toNonAssocRing.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> (forall {a : R} {a' : R'}, (Eq.{succ u3} R'' ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Int R'' (HasLiftT.mk.{1, succ u3} Int R'' (CoeTCₓ.coe.{1, succ u3} Int R'' (Int.castCoe.{u3} R'' (AddGroupWithOne.toHasIntCast.{u3} R'' (AddCommGroupWithOne.toAddGroupWithOne.{u3} R'' (Ring.toAddCommGroupWithOne.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3))))))) (coeFn.{succ u1, succ u1} (MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) (fun (_x : MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) => R -> Int) (MulChar.coeToFun.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) χ a)) ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Int R'' (HasLiftT.mk.{1, succ u3} Int R'' (CoeTCₓ.coe.{1, succ u3} Int R'' (Int.castCoe.{u3} R'' (AddGroupWithOne.toHasIntCast.{u3} R'' (AddCommGroupWithOne.toAddGroupWithOne.{u3} R'' (Ring.toAddCommGroupWithOne.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3))))))) (coeFn.{succ u2, succ u2} (MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) (fun (_x : MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) => R' -> Int) (MulChar.coeToFun.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) χ' a'))) -> (Eq.{1} Int (coeFn.{succ u1, succ u1} (MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) (fun (_x : MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) => R -> Int) (MulChar.coeToFun.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) χ a) (coeFn.{succ u2, succ u2} (MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) (fun (_x : MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) => R' -> Int) (MulChar.coeToFun.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CommSemiring.toCommMonoidWithZero.{0} Int Int.commSemiring)) χ' a')))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {R'' : Type.{u3}} [_inst_3 : CommRing.{u3} R''] {χ : MulChar.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))}, (MulChar.IsQuadratic.{u1, 0} R _inst_1 Int Int.instCommRingInt χ) -> (forall {χ' : MulChar.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))))}, (MulChar.IsQuadratic.{u2, 0} R' _inst_2 Int Int.instCommRingInt χ') -> (forall [_inst_4 : Nontrivial.{u3} R''], (Ne.{1} Nat (ringChar.{u3} R'' (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> (forall {a : R} {a' : R'}, (Eq.{succ u3} R'' (Int.cast.{u3} R'' (Ring.toIntCast.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)) (MulChar.toFun'.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) χ a)) (Int.cast.{u3} R'' (Ring.toIntCast.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)) (MulChar.toFun'.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) χ' a'))) -> (Eq.{1} Int (MulChar.toFun'.{u1, 0} R (CommRing.toCommMonoid.{u1} R _inst_1) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) χ a) (MulChar.toFun'.{u2, 0} R' (CommRing.toCommMonoid.{u2} R' _inst_2) Int (CancelCommMonoidWithZero.toCommMonoidWithZero.{0} Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing)))) χ' a')))))
Case conversion may be inaccurate. Consider using '#align mul_char.is_quadratic.eq_of_eq_coe MulChar.IsQuadratic.eq_of_eq_coeₓ'. -/
/-- If two values of quadratic characters with target `ℤ` agree after coercion into a ring
of characteristic not `2`, then they agree in `ℤ`. -/
theorem IsQuadratic.eq_of_eq_coe {χ : MulChar R ℤ} (hχ : IsQuadratic χ) {χ' : MulChar R' ℤ}
    (hχ' : IsQuadratic χ') [Nontrivial R''] (hR'' : ringChar R'' ≠ 2) {a : R} {a' : R'}
    (h : (χ a : R'') = χ' a') : χ a = χ' a' :=
  Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h
#align mul_char.is_quadratic.eq_of_eq_coe MulChar.IsQuadratic.eq_of_eq_coe

#print MulChar.ringHomComp /-
/-- We can post-compose a multiplicative character with a ring homomorphism. -/
@[simps]
def ringHomComp (χ : MulChar R R') (f : R' →+* R'') : MulChar R R'' :=
  {
    f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }
#align mul_char.ring_hom_comp MulChar.ringHomComp
-/

/- warning: mul_char.is_nontrivial.comp -> MulChar.IsNontrivial.comp is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {R'' : Type.{u3}} [_inst_3 : CommRing.{u3} R''] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))}, (MulChar.IsNontrivial.{u1, u2} R _inst_1 R' _inst_2 χ) -> (forall {f : RingHom.{u2, u3} R' R'' (NonAssocRing.toNonAssocSemiring.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R'' (Ring.toNonAssocRing.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)))}, (Function.Injective.{succ u2, succ u3} R' R'' (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} R' R'' (NonAssocRing.toNonAssocSemiring.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R'' (Ring.toNonAssocRing.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)))) (fun (_x : RingHom.{u2, u3} R' R'' (NonAssocRing.toNonAssocSemiring.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R'' (Ring.toNonAssocRing.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)))) => R' -> R'') (RingHom.hasCoeToFun.{u2, u3} R' R'' (NonAssocRing.toNonAssocSemiring.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R'' (Ring.toNonAssocRing.{u3} R'' (CommRing.toRing.{u3} R'' _inst_3)))) f)) -> (MulChar.IsNontrivial.{u1, u3} R _inst_1 R'' _inst_3 (MulChar.ringHomComp.{u1, u2, u3} R _inst_1 R' _inst_2 R'' _inst_3 χ f)))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {R'' : Type.{u3}} [_inst_3 : CommRing.{u3} R''] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))}, (MulChar.IsNontrivial.{u1, u2} R _inst_1 R' _inst_2 χ) -> (forall {f : RingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))}, (Function.Injective.{succ u2, succ u3} R' R'' (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (RingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) R' (fun (_x : R') => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : R') => R'') _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (RingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) R' R'' (NonUnitalNonAssocSemiring.toMul.{u2} R' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))))) (NonUnitalNonAssocSemiring.toMul.{u3} R'' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R'' (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3))))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) R' R'' (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2)))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R'' (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) (RingHomClass.toNonUnitalRingHomClass.{max u2 u3, u2, u3} (RingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3)))) R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3))) (RingHom.instRingHomClassRingHom.{u2, u3} R' R'' (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Semiring.toNonAssocSemiring.{u3} R'' (CommSemiring.toSemiring.{u3} R'' (CommRing.toCommSemiring.{u3} R'' _inst_3))))))) f)) -> (MulChar.IsNontrivial.{u1, u3} R _inst_1 R'' _inst_3 (MulChar.ringHomComp.{u1, u2, u3} R _inst_1 R' _inst_2 R'' _inst_3 χ f)))
Case conversion may be inaccurate. Consider using '#align mul_char.is_nontrivial.comp MulChar.IsNontrivial.compₓ'. -/
/-- Composition with an injective ring homomorphism preserves nontriviality. -/
theorem IsNontrivial.comp {χ : MulChar R R'} (hχ : χ.IsNontrivial) {f : R' →+* R''}
    (hf : Function.Injective f) : (χ.ringHomComp f).IsNontrivial :=
  by
  obtain ⟨a, ha⟩ := hχ
  use a
  rw [ring_hom_comp_apply, ← RingHom.map_one f]
  exact fun h => ha (hf h)
#align mul_char.is_nontrivial.comp MulChar.IsNontrivial.comp

#print MulChar.IsQuadratic.comp /-
/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' →+* R'') :
    (χ.ringHomComp f).IsQuadratic := by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]
#align mul_char.is_quadratic.comp MulChar.IsQuadratic.comp
-/

#print MulChar.IsQuadratic.inv /-
/-- The inverse of a quadratic character is itself. →  -/
theorem IsQuadratic.inv {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ⁻¹ = χ :=
  by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · rw [h₂, (by norm_cast : (-1 : R') = (-1 : R'ˣ)), Ring.inverse_unit (-1 : R'ˣ)]
    rfl
#align mul_char.is_quadratic.inv MulChar.IsQuadratic.inv
-/

#print MulChar.IsQuadratic.sq_eq_one /-
/-- The square of a quadratic character is the trivial character. -/
theorem IsQuadratic.sq_eq_one {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ ^ 2 = 1 :=
  by
  convert mul_left_inv _
  rw [pow_two, hχ.inv]
#align mul_char.is_quadratic.sq_eq_one MulChar.IsQuadratic.sq_eq_one
-/

/- warning: mul_char.is_quadratic.pow_char -> MulChar.IsQuadratic.pow_char is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))}, (MulChar.IsQuadratic.{u1, u2} R _inst_1 R' _inst_2 χ) -> (forall (p : Nat) [hp : Fact (Nat.Prime p)] [_inst_4 : CharP.{u2} R' (AddGroupWithOne.toAddMonoidWithOne.{u2} R' (AddCommGroupWithOne.toAddGroupWithOne.{u2} R' (Ring.toAddCommGroupWithOne.{u2} R' (CommRing.toRing.{u2} R' _inst_2)))) p], Eq.{succ (max u1 u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) Nat (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (instHPow.{max u1 u2, 0} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) Nat (Monoid.Pow.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (DivInvMonoid.toMonoid.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Group.toDivInvMonoid.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (CommGroup.toGroup.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (MulChar.commGroup.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2)))))))) χ p) χ)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))}, (MulChar.IsQuadratic.{u1, u2} R _inst_1 R' _inst_2 χ) -> (forall (p : Nat) [hp : Fact (Nat.Prime p)] [_inst_4 : CharP.{u2} R' (AddGroupWithOne.toAddMonoidWithOne.{u2} R' (Ring.toAddGroupWithOne.{u2} R' (CommRing.toRing.{u2} R' _inst_2))) p], Eq.{max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (HPow.hPow.{max u1 u2, 0, max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) Nat (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (instHPow.{max u1 u2, 0} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) Nat (Monoid.Pow.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (DivInvMonoid.toMonoid.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Group.toDivInvMonoid.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (CommGroup.toGroup.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (MulChar.commGroup.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2)))))))) χ p) χ)
Case conversion may be inaccurate. Consider using '#align mul_char.is_quadratic.pow_char MulChar.IsQuadratic.pow_charₓ'. -/
/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
theorem IsQuadratic.pow_char {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : ℕ) [hp : Fact p.Prime]
    [CharP R' p] : χ ^ p = χ := by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (Fact.out p.prime).Pos]
  · rw [one_pow]
  · exact CharP.neg_one_pow_char R' p
#align mul_char.is_quadratic.pow_char MulChar.IsQuadratic.pow_char

#print MulChar.IsQuadratic.pow_even /-
/-- The `n`th power of a quadratic character is the trivial character, when `n` is even. -/
theorem IsQuadratic.pow_even {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Even n) :
    χ ^ n = 1 := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul, hχ.sq_eq_one, one_pow]
#align mul_char.is_quadratic.pow_even MulChar.IsQuadratic.pow_even
-/

#print MulChar.IsQuadratic.pow_odd /-
/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
theorem IsQuadratic.pow_odd {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Odd n) :
    χ ^ n = χ := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add, pow_one, hχ.pow_even (even_two_mul _), one_mul]
#align mul_char.is_quadratic.pow_odd MulChar.IsQuadratic.pow_odd
-/

open BigOperators

/- warning: mul_char.is_nontrivial.sum_eq_zero -> MulChar.IsNontrivial.sum_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] [_inst_4 : Fintype.{u1} R] [_inst_5 : IsDomain.{u2} R' (Ring.toSemiring.{u2} R' (CommRing.toRing.{u2} R' _inst_2))] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))}, (MulChar.IsNontrivial.{u1, u2} R _inst_1 R' _inst_2 χ) -> (Eq.{succ u2} R' (Finset.sum.{u2, u1} R' R (AddCommGroup.toAddCommMonoid.{u2} R' (NonUnitalNonAssocRing.toAddCommGroup.{u2} R' (NonAssocRing.toNonUnitalNonAssocRing.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))))) (Finset.univ.{u1} R _inst_4) (fun (a : R) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (fun (_x : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) χ a)) (OfNat.ofNat.{u2} R' 0 (OfNat.mk.{u2} R' 0 (Zero.zero.{u2} R' (MulZeroClass.toHasZero.{u2} R' (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R' (NonAssocRing.toNonUnitalNonAssocRing.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] [_inst_4 : Fintype.{u1} R] [_inst_5 : IsDomain.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))] {χ : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} R' (IsDomain.toCancelCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2) _inst_5))}, (MulChar.IsNontrivial.{u1, u2} R _inst_1 R' _inst_2 χ) -> (Eq.{succ u2} R' (Finset.sum.{u2, u1} R' R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R' (NonAssocRing.toNonUnitalNonAssocRing.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))))) (Finset.univ.{u1} R _inst_4) (fun (a : R) => MulChar.toFun'.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} R' (IsDomain.toCancelCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2) _inst_5)) χ a)) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} R' (IsDomain.toCancelCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2) _inst_5))))))
Case conversion may be inaccurate. Consider using '#align mul_char.is_nontrivial.sum_eq_zero MulChar.IsNontrivial.sum_eq_zeroₓ'. -/
/-- The sum over all values of a nontrivial multiplicative character on a finite ring is zero
(when the target is a domain). -/
theorem IsNontrivial.sum_eq_zero [Fintype R] [IsDomain R'] {χ : MulChar R R'}
    (hχ : χ.IsNontrivial) : (∑ a, χ a) = 0 :=
  by
  rcases hχ with ⟨b, hb⟩
  refine' eq_zero_of_mul_eq_self_left hb _
  simp only [Finset.mul_sum, ← map_mul]
  exact Fintype.sum_bijective _ (Units.mulLeft_bijective b) _ _ fun x => rfl
#align mul_char.is_nontrivial.sum_eq_zero MulChar.IsNontrivial.sum_eq_zero

/- warning: mul_char.sum_one_eq_card_units -> MulChar.sum_one_eq_card_units is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] [_inst_4 : Fintype.{u1} R] [_inst_5 : DecidableEq.{succ u1} R], Eq.{succ u2} R' (Finset.sum.{u2, u1} R' R (AddCommGroup.toAddCommMonoid.{u2} R' (NonUnitalNonAssocRing.toAddCommGroup.{u2} R' (NonAssocRing.toNonUnitalNonAssocRing.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))))) (Finset.univ.{u1} R _inst_4) (fun (a : R) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (fun (_x : MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) => R -> R') (MulChar.coeToFun.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (OfNat.ofNat.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) 1 (OfNat.mk.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) 1 (One.one.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (MulChar.hasOne.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2)))))) a)) ((fun (a : Type) (b : Type.{u2}) [self : HasLiftT.{1, succ u2} a b] => self.0) Nat R' (HasLiftT.mk.{1, succ u2} Nat R' (CoeTCₓ.coe.{1, succ u2} Nat R' (Nat.castCoe.{u2} R' (AddMonoidWithOne.toNatCast.{u2} R' (AddGroupWithOne.toAddMonoidWithOne.{u2} R' (AddCommGroupWithOne.toAddGroupWithOne.{u2} R' (Ring.toAddCommGroupWithOne.{u2} R' (CommRing.toRing.{u2} R' _inst_2)))))))) (Fintype.card.{u1} (Units.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Units.fintype.{u1} R (Ring.toMonoid.{u1} R (CommRing.toRing.{u1} R _inst_1)) _inst_4 (fun (a : R) (b : R) => _inst_5 a b))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] {R' : Type.{u2}} [_inst_2 : CommRing.{u2} R'] [_inst_4 : Fintype.{u1} R] [_inst_5 : DecidableEq.{succ u1} R], Eq.{succ u2} R' (Finset.sum.{u2, u1} R' R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} R' (NonAssocRing.toNonUnitalNonAssocRing.{u2} R' (Ring.toNonAssocRing.{u2} R' (CommRing.toRing.{u2} R' _inst_2))))) (Finset.univ.{u1} R _inst_4) (fun (a : R) => MulChar.toFun'.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2)) (OfNat.ofNat.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) 1 (One.toOfNat1.{max u1 u2} (MulChar.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (MulChar.hasOne.{u1, u2} R (CommRing.toCommMonoid.{u1} R _inst_1) R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))))) a)) (Nat.cast.{u2} R' (Semiring.toNatCast.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_2))) (Fintype.card.{u1} (Units.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))) (instFintypeUnits.{u1} R (MonoidWithZero.toMonoid.{u1} R (Semiring.toMonoidWithZero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))) _inst_4 (fun (a : R) (b : R) => _inst_5 a b))))
Case conversion may be inaccurate. Consider using '#align mul_char.sum_one_eq_card_units MulChar.sum_one_eq_card_unitsₓ'. -/
/-- The sum over all values of the trivial multiplicative character on a finite ring is
the cardinality of its unit group. -/
theorem sum_one_eq_card_units [Fintype R] [DecidableEq R] :
    (∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ :=
  by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => _
    _ = ((Finset.univ : Finset R).filterₓ IsUnit).card := Finset.sum_boole
    _ = (finset.univ.map ⟨(coe : Rˣ → R), Units.ext⟩).card := _
    _ = Fintype.card Rˣ := congr_arg _ (Finset.card_map _)
    
  · split_ifs with h h
    · exact one_apply_coe h.unit
    · exact map_nonunit _ h
  · congr
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, Finset.mem_map,
      Function.Embedding.coeFn_mk, exists_true_left, IsUnit]
#align mul_char.sum_one_eq_card_units MulChar.sum_one_eq_card_units

end MulChar

end Properties

