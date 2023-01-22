/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.equiv.units.basic
! leanprover-community/mathlib commit d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Units

/-!
# Multiplicative and additive equivalence acting on units.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {F α β A B M N P Q G H : Type _}

/- warning: to_units -> toUnits is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.mulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align to_units toUnitsₓ'. -/
/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ
    where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun := coe
  left_inv x := rfl
  right_inv u := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align to_units toUnits
#align to_add_units toAddUnits

/- warning: coe_to_units -> coe_toUnits is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (g : G), Eq.{succ u1} G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) G (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) G (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) G (coeBase.{succ u1, succ u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) G (Units.hasCoe.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.mulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (fun (_x : MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.mulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) => G -> (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulEquiv.hasCoeToFun.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.mulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (toUnits.{u1} G _inst_1) g)) g
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (g : G), Eq.{succ u1} G (Units.val.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} G (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toMul.{u1} (Units.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Units.instMulOneClassUnits.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))))) (toUnits.{u1} G _inst_1) g)) g
Case conversion may be inaccurate. Consider using '#align coe_to_units coe_toUnitsₓ'. -/
@[simp, to_additive]
theorem coe_toUnits [Group G] (g : G) : (toUnits g : G) = g :=
  rfl
#align coe_to_units coe_toUnits
#align coe_to_add_units coe_toAddUnits

namespace Units

variable [Monoid M] [Monoid N] [Monoid P]

/- warning: units.map_equiv -> Units.mapEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N], (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) -> (MulEquiv.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2)))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N], (MulEquiv.{u1, u2} M N (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) -> (MulEquiv.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toMul.{u1} (Units.{u1} M _inst_1) (Units.instMulOneClassUnits.{u1} M _inst_1)) (MulOneClass.toMul.{u2} (Units.{u2} N _inst_2) (Units.instMulOneClassUnits.{u2} N _inst_2)))
Case conversion may be inaccurate. Consider using '#align units.map_equiv Units.mapEquivₓ'. -/
/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom
    left_inv := fun u => ext <| h.left_inv u
    right_inv := fun u => ext <| h.right_inv u }
#align units.map_equiv Units.mapEquiv

/- warning: units.map_equiv_symm -> Units.mapEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} (Units.{u2} N _inst_2) (Units.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2)) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1))) (MulEquiv.symm.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2)) (Units.mapEquiv.{u1, u2} M N _inst_1 _inst_2 h)) (Units.mapEquiv.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.symm.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) h))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u1, u2} (Units.{u1} N _inst_2) (Units.{u2} M _inst_1) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2)) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1))) (MulEquiv.symm.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2)) (Units.mapEquiv.{u2, u1} M N _inst_1 _inst_2 h)) (Units.mapEquiv.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.symm.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) h))
Case conversion may be inaccurate. Consider using '#align units.map_equiv_symm Units.mapEquiv_symmₓ'. -/
@[simp]
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl
#align units.map_equiv_symm Units.mapEquiv_symm

/- warning: units.coe_map_equiv -> Units.coe_mapEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (x : Units.{u1} M _inst_1), Eq.{succ u2} N ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Units.{u2} N _inst_2) N (HasLiftT.mk.{succ u2, succ u2} (Units.{u2} N _inst_2) N (CoeTCₓ.coe.{succ u2, succ u2} (Units.{u2} N _inst_2) N (coeBase.{succ u2, succ u2} (Units.{u2} N _inst_2) N (Units.hasCoe.{u2} N _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2))) (fun (_x : MulEquiv.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2))) => (Units.{u1} M _inst_1) -> (Units.{u2} N _inst_2)) (MulEquiv.hasCoeToFun.{u1, u2} (Units.{u1} M _inst_1) (Units.{u2} N _inst_2) (MulOneClass.toHasMul.{u1} (Units.{u1} M _inst_1) (Units.mulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (Units.{u2} N _inst_2) (Units.mulOneClass.{u2} N _inst_2))) (Units.mapEquiv.{u1, u2} M N _inst_1 _inst_2 h) x)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) h ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (x : Units.{u2} M _inst_1), Eq.{succ u1} N (Units.val.{u1} N _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2))) (Units.{u2} M _inst_1) (fun (_x : Units.{u2} M _inst_1) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Units.{u2} M _inst_1) => Units.{u1} N _inst_2) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2))) (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2))) (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2))) (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} (Units.{u2} M _inst_1) (Units.{u1} N _inst_2) (MulOneClass.toMul.{u2} (Units.{u2} M _inst_1) (Units.instMulOneClassUnits.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (Units.{u1} N _inst_2) (Units.instMulOneClassUnits.{u1} N _inst_2)))))) (Units.mapEquiv.{u2, u1} M N _inst_1 _inst_2 h) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)))))) h (Units.val.{u2} M _inst_1 x))
Case conversion may be inaccurate. Consider using '#align units.coe_map_equiv Units.coe_mapEquivₓ'. -/
@[simp]
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl
#align units.coe_map_equiv Units.coe_mapEquiv

#print Units.mulLeft /-
/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := ↑u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left
#align units.mul_left Units.mulLeft
#align add_units.add_left AddUnits.addLeft
-/

#print Units.mulLeft_symm /-
@[simp, to_additive]
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun x => rfl
#align units.mul_left_symm Units.mulLeft_symm
#align add_units.add_left_symm AddUnits.addLeft_symm
-/

/- warning: units.mul_left_bijective -> Units.mulLeft_bijective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : Units.{u1} M _inst_1), Function.Bijective.{succ u1, succ u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) a))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : Units.{u1} M _inst_1), Function.Bijective.{succ u1, succ u1} M M (fun (x._@.Mathlib.Algebra.Hom.Equiv.Units.Basic._hyg.445 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Units.val.{u1} M _inst_1 a) x._@.Mathlib.Algebra.Hom.Equiv.Units.Basic._hyg.445)
Case conversion may be inaccurate. Consider using '#align units.mul_left_bijective Units.mulLeft_bijectiveₓ'. -/
@[to_additive]
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((· * ·) a : M → M) :=
  (mulLeft a).Bijective
#align units.mul_left_bijective Units.mulLeft_bijective
#align add_units.add_left_bijective AddUnits.addLeft_bijective

#print Units.mulRight /-
/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u
#align units.mul_right Units.mulRight
#align add_units.add_right AddUnits.addRight
-/

#print Units.mulRight_symm /-
@[simp, to_additive]
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun x => rfl
#align units.mul_right_symm Units.mulRight_symm
#align add_units.add_right_symm AddUnits.addRight_symm
-/

/- warning: units.mul_right_bijective -> Units.mulRight_bijective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : Units.{u1} M _inst_1), Function.Bijective.{succ u1, succ u1} M M (fun (_x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) _x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Units.{u1} M _inst_1) M (HasLiftT.mk.{succ u1, succ u1} (Units.{u1} M _inst_1) M (CoeTCₓ.coe.{succ u1, succ u1} (Units.{u1} M _inst_1) M (coeBase.{succ u1, succ u1} (Units.{u1} M _inst_1) M (Units.hasCoe.{u1} M _inst_1)))) a))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (a : Units.{u1} M _inst_1), Function.Bijective.{succ u1, succ u1} M M (fun (_x : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) _x (Units.val.{u1} M _inst_1 a))
Case conversion may be inaccurate. Consider using '#align units.mul_right_bijective Units.mulRight_bijectiveₓ'. -/
@[to_additive]
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).Bijective
#align units.mul_right_bijective Units.mulRight_bijective
#align add_units.add_right_bijective AddUnits.addRight_bijective

end Units

namespace Equiv

section Group

variable [Group G]

#print Equiv.mulLeft /-
/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft
#align equiv.mul_left Equiv.mulLeft
#align equiv.add_left Equiv.addLeft
-/

#print Equiv.coe_mulLeft /-
@[simp, to_additive]
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (· * ·) a :=
  rfl
#align equiv.coe_mul_left Equiv.coe_mulLeft
#align equiv.coe_add_left Equiv.coe_addLeft
-/

#print Equiv.mulLeft_symm_apply /-
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (· * ·) a⁻¹ :=
  rfl
#align equiv.mul_left_symm_apply Equiv.mulLeft_symm_apply
#align equiv.add_left_symm_apply Equiv.addLeft_symm_apply
-/

/- warning: equiv.mul_left_symm -> Equiv.mulLeft_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.symm.{succ u1, succ u1} G G (Equiv.mulLeft.{u1} G _inst_1 a)) (Equiv.mulLeft.{u1} G _inst_1 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.symm.{succ u1, succ u1} G G (Equiv.mulLeft.{u1} G _inst_1 a)) (Equiv.mulLeft.{u1} G _inst_1 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.mul_left_symm Equiv.mulLeft_symmₓ'. -/
@[simp, to_additive]
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun x => rfl
#align equiv.mul_left_symm Equiv.mulLeft_symm
#align equiv.add_left_symm Equiv.addLeft_symm

/- warning: group.mul_left_bijective -> Group.mulLeft_bijective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Bijective.{succ u1, succ u1} G G (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Bijective.{succ u1, succ u1} G G (fun (x._@.Mathlib.Algebra.Hom.Equiv.Units.Basic._hyg.832 : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) a x._@.Mathlib.Algebra.Hom.Equiv.Units.Basic._hyg.832)
Case conversion may be inaccurate. Consider using '#align group.mul_left_bijective Group.mulLeft_bijectiveₓ'. -/
@[to_additive]
theorem Group.mulLeft_bijective (a : G) : Function.Bijective ((· * ·) a) :=
  (Equiv.mulLeft a).Bijective
#align group.mul_left_bijective Group.mulLeft_bijective
#align add_group.add_left_bijective AddGroup.addLeft_bijective

#print Equiv.mulRight /-
/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight
#align equiv.mul_right Equiv.mulRight
#align equiv.add_right Equiv.addRight
-/

#print Equiv.coe_mulRight /-
@[simp, to_additive]
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl
#align equiv.coe_mul_right Equiv.coe_mulRight
#align equiv.coe_add_right Equiv.coe_addRight
-/

/- warning: equiv.mul_right_symm -> Equiv.mulRight_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.symm.{succ u1, succ u1} G G (Equiv.mulRight.{u1} G _inst_1 a)) (Equiv.mulRight.{u1} G _inst_1 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.symm.{succ u1, succ u1} G G (Equiv.mulRight.{u1} G _inst_1 a)) (Equiv.mulRight.{u1} G _inst_1 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.mul_right_symm Equiv.mulRight_symmₓ'. -/
@[simp, to_additive]
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun x => rfl
#align equiv.mul_right_symm Equiv.mulRight_symm
#align equiv.add_right_symm Equiv.addRight_symm

#print Equiv.mulRight_symm_apply /-
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl
#align equiv.mul_right_symm_apply Equiv.mulRight_symm_apply
#align equiv.add_right_symm_apply Equiv.addRight_symm_apply
-/

/- warning: group.mul_right_bijective -> Group.mulRight_bijective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Bijective.{succ u1, succ u1} G G (fun (_x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) _x a)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Function.Bijective.{succ u1, succ u1} G G (fun (_x : G) => HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) _x a)
Case conversion may be inaccurate. Consider using '#align group.mul_right_bijective Group.mulRight_bijectiveₓ'. -/
@[to_additive]
theorem Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).Bijective
#align group.mul_right_bijective Group.mulRight_bijective
#align add_group.add_right_bijective AddGroup.addRight_bijective

#print Equiv.divLeft /-
/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `equiv.add_left a (-b)` that is defeq to `a - b`. ", simps]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_left Equiv.divLeft
#align equiv.sub_left Equiv.subLeft
-/

/- warning: equiv.div_left_eq_inv_trans_mul_left -> Equiv.divLeft_eq_inv_trans_mulLeft is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.divLeft.{u1} G _inst_1 a) (Equiv.trans.{succ u1, succ u1, succ u1} G G G (Equiv.inv.{u1} G (DivisionMonoid.toHasInvolutiveInv.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))) (Equiv.mulLeft.{u1} G _inst_1 a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.divLeft.{u1} G _inst_1 a) (Equiv.trans.{succ u1, succ u1, succ u1} G G G (Equiv.inv.{u1} G (DivisionMonoid.toInvolutiveInv.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1))) (Equiv.mulLeft.{u1} G _inst_1 a))
Case conversion may be inaccurate. Consider using '#align equiv.div_left_eq_inv_trans_mul_left Equiv.divLeft_eq_inv_trans_mulLeftₓ'. -/
@[to_additive]
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_left_eq_inv_trans_mul_left Equiv.divLeft_eq_inv_trans_mulLeft
#align equiv.sub_left_eq_neg_trans_add_left Equiv.subLeft_eq_neg_trans_addLeft

#print Equiv.divRight /-
/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `equiv.add_right (-a) b` that is defeq to `b - a`. ", simps]
protected def divRight (a : G) : G ≃ G
    where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_right Equiv.divRight
#align equiv.sub_right Equiv.subRight
-/

/- warning: equiv.div_right_eq_mul_right_inv -> Equiv.divRight_eq_mulRight_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.divRight.{u1} G _inst_1 a) (Equiv.mulRight.{u1} G _inst_1 (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) a))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (a : G), Eq.{succ u1} (Equiv.{succ u1, succ u1} G G) (Equiv.divRight.{u1} G _inst_1 a) (Equiv.mulRight.{u1} G _inst_1 (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) a))
Case conversion may be inaccurate. Consider using '#align equiv.div_right_eq_mul_right_inv Equiv.divRight_eq_mulRight_invₓ'. -/
@[to_additive]
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_right_eq_mul_right_inv Equiv.divRight_eq_mulRight_inv
#align equiv.sub_right_eq_add_right_neg Equiv.subRight_eq_addRight_neg

end Group

end Equiv

/- warning: mul_equiv.inv -> MulEquiv.inv is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : DivisionCommMonoid.{u1} G], MulEquiv.{u1, u1} G G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1)))))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : DivisionCommMonoid.{u1} G], MulEquiv.{u1, u1} G G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_equiv.inv MulEquiv.invₓ'. -/
/-- In a `division_comm_monoid`, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`.", simps apply]
def MulEquiv.inv (G : Type _) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with
    toFun := Inv.inv
    invFun := Inv.inv
    map_mul' := mul_inv }
#align mul_equiv.inv MulEquiv.inv
#align add_equiv.neg AddEquiv.neg

/- warning: mul_equiv.inv_symm -> MulEquiv.inv_symm is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : DivisionCommMonoid.{u1} G], Eq.{succ u1} (MulEquiv.{u1, u1} G G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1)))))) (MulEquiv.symm.{u1, u1} G G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulEquiv.inv.{u1} G _inst_1)) (MulEquiv.inv.{u1} G _inst_1)
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : DivisionCommMonoid.{u1} G], Eq.{succ u1} (MulEquiv.{u1, u1} G G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1)))))) (MulEquiv.symm.{u1, u1} G G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (DivisionMonoid.toDivInvMonoid.{u1} G (DivisionCommMonoid.toDivisionMonoid.{u1} G _inst_1))))) (MulEquiv.inv.{u1} G _inst_1)) (MulEquiv.inv.{u1} G _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_equiv.inv_symm MulEquiv.inv_symmₓ'. -/
@[simp]
theorem MulEquiv.inv_symm (G : Type _) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl
#align mul_equiv.inv_symm MulEquiv.inv_symm

