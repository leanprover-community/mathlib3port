/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin

! This file was ported from Lean 3 source module algebra.group.with_one.basic
! leanprover-community/mathlib commit 6d0adfa76594f304b4650d098273d4366edeb61b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.WithOne.Defs
import Mathbin.Algebra.Hom.Equiv.Basic

/-!
# More operations on `with_one` and `with_zero`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines various bundled morphisms on `with_one` and `with_zero`
that were not available in `algebra/group/with_one/defs`.

## Main definitions

* `with_one.lift`, `with_zero.lift`
* `with_one.map`, `with_zero.map`
-/


universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

section

#print WithOne.coeMulHom /-
-- workaround: we make `with_one`/`with_zero` irreducible for this definition, otherwise `simps`
-- will unfold it in the statement of the lemma it generates.
/-- `coe` as a bundled morphism -/
@[to_additive "`coe` as a bundled morphism", simps apply]
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' x y := rfl
#align with_one.coe_mul_hom WithOne.coeMulHom
-/

end

section lift

attribute [local semireducible] WithOne WithZero

variable [Mul α] [MulOneClass β]

/- warning: with_one.lift -> WithOne.lift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)
Case conversion may be inaccurate. Consider using '#align with_one.lift WithOne.liftₓ'. -/
/-- Lift a semigroup homomorphism `f` to a bundled monoid homorphism. -/
@[to_additive "Lift an add_semigroup homomorphism `f` to a bundled add_monoid homorphism."]
def lift : (α →ₙ* β) ≃ (WithOne α →* β)
    where
  toFun f :=
    { toFun := fun x => Option.casesOn x 1 f
      map_one' := rfl
      map_mul' := fun x y =>
        (WithOne.cases_on x
            (by
              rw [one_mul]
              exact (one_mul _).symm))
          fun x =>
          (WithOne.cases_on y
              (by
                rw [mul_one]
                exact (mul_one _).symm))
            fun y => f.map_mul x y }
  invFun F := F.toMulHom.comp coeMulHom
  left_inv f := MulHom.ext fun x => rfl
  right_inv F := MonoidHom.ext fun x => (WithOne.cases_on x F.map_one.symm) fun x => rfl
#align with_one.lift WithOne.lift

variable (f : α →ₙ* β)

/- warning: with_one.lift_coe -> WithOne.lift_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (x : α), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (fun (_x : MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) => (WithOne.{u1} α) -> β) (MonoidHom.hasCoeToFun.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (coeFn.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) => (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) -> (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (WithOne.lift.{u1, u2} α β _inst_1 _inst_2) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithOne.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithOne.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithOne.{u1} α) (WithOne.hasCoeT.{u1} α))) x)) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) => α -> β) (MulHom.hasCoeToFun.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) f x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) (WithOne.coe.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) (fun (_x : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) β (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2 (MonoidHom.monoidHomClass.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)))) (WithOne.lift.{u1, u2} α β _inst_1 _inst_2) f) (WithOne.coe.{u1} α x)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2) (MulHom.mulHomClass.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2))) f x)
Case conversion may be inaccurate. Consider using '#align with_one.lift_coe WithOne.lift_coeₓ'. -/
@[simp, to_additive]
theorem lift_coe (x : α) : lift f x = f x :=
  rfl
#align with_one.lift_coe WithOne.lift_coe

/- warning: with_one.lift_one -> WithOne.lift_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)), Eq.{succ u2} β (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (fun (_x : MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) => (WithOne.{u1} α) -> β) (MonoidHom.hasCoeToFun.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (coeFn.{max 1 (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (fun (_x : Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) => (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) -> (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (Equiv.hasCoeToFun.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toHasMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (WithOne.lift.{u1, u2} α β _inst_1 _inst_2) f) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (OfNat.mk.{u1} (WithOne.{u1} α) 1 (One.one.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α))))) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β (MulOneClass.toHasOne.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : MulOneClass.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (One.toOfNat1.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α)))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) (fun (_x : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) β (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) f) (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2 (MonoidHom.monoidHomClass.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2))) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (fun (_x : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) => MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)) (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2) (Equiv.instEquivLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulHom.{u1, u2} α β _inst_1 (MulOneClass.toMul.{u2} β _inst_2)) (MonoidHom.{u1, u2} (WithOne.{u1} α) β (WithOne.mulOneClass.{u1} α _inst_1) _inst_2)))) (WithOne.lift.{u1, u2} α β _inst_1 _inst_2) f) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (One.toOfNat1.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α)))) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (One.toOfNat1.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α)))) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (One.toOfNat1.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α)))) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => β) (OfNat.ofNat.{u1} (WithOne.{u1} α) 1 (One.toOfNat1.{u1} (WithOne.{u1} α) (WithOne.one.{u1} α)))) _inst_2)))
Case conversion may be inaccurate. Consider using '#align with_one.lift_one WithOne.lift_oneₓ'. -/
@[simp, to_additive]
theorem lift_one : lift f 1 = 1 :=
  rfl
#align with_one.lift_one WithOne.lift_one

#print WithOne.lift_unique /-
@[to_additive]
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm
#align with_one.lift_unique WithOne.lift_unique
-/

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

#print WithOne.map /-
/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `with_one α` to `with_one β` -/
@[to_additive
      "Given an additive map from `α → β` returns an add_monoid homomorphism\n  from `with_zero α` to `with_zero β`"]
def map (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)
#align with_one.map WithOne.map
-/

/- warning: with_one.map_coe -> WithOne.map_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} (WithOne.{u2} β) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (fun (_x : MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) => (WithOne.{u1} α) -> (WithOne.{u2} β)) (MonoidHom.hasCoeToFun.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.map.{u1, u2} α β _inst_1 _inst_2 f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) α (WithOne.{u1} α) (HasLiftT.mk.{succ u1, succ u1} α (WithOne.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} α (WithOne.{u1} α) (WithOne.hasCoeT.{u1} α))) a)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (WithOne.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (WithOne.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (WithOne.{u2} β) (WithOne.hasCoeT.{u2} β))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (MulHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] (f : MulHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => WithOne.{u2} β) (WithOne.coe.{u1} α a)) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (fun (_x : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => WithOne.{u2} β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} (WithOne.{u2} β) (WithOne.mulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)))) (WithOne.map.{u1, u2} α β _inst_1 _inst_2 f) (WithOne.coe.{u1} α a)) (WithOne.coe.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MulHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : α) => β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MulHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (MulHom.mulHomClass.{u1, u2} α β _inst_1 _inst_2)) f a))
Case conversion may be inaccurate. Consider using '#align with_one.map_coe WithOne.map_coeₓ'. -/
@[simp, to_additive]
theorem map_coe (f : α →ₙ* β) (a : α) : map f (a : WithOne α) = f a :=
  lift_coe _ _
#align with_one.map_coe WithOne.map_coe

#print WithOne.map_id /-
@[simp, to_additive]
theorem map_id : map (MulHom.id α) = MonoidHom.id (WithOne α) :=
  by
  ext
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_id WithOne.map_id
-/

/- warning: with_one.map_map -> WithOne.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] [_inst_3 : Mul.{u3} γ] (f : MulHom.{u1, u2} α β _inst_1 _inst_2) (g : MulHom.{u2, u3} β γ _inst_2 _inst_3) (x : WithOne.{u1} α), Eq.{succ u3} (WithOne.{u3} γ) (coeFn.{max (succ u3) (succ u2), max (succ u2) (succ u3)} (MonoidHom.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) (fun (_x : MonoidHom.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) => (WithOne.{u2} β) -> (WithOne.{u3} γ)) (MonoidHom.hasCoeToFun.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.map.{u2, u3} β γ _inst_2 _inst_3 g) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (fun (_x : MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) => (WithOne.{u1} α) -> (WithOne.{u2} β)) (MonoidHom.hasCoeToFun.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.map.{u1, u2} α β _inst_1 _inst_2 f) x)) (coeFn.{max (succ u3) (succ u1), max (succ u1) (succ u3)} (MonoidHom.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) (fun (_x : MonoidHom.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) => (WithOne.{u1} α) -> (WithOne.{u3} γ)) (MonoidHom.hasCoeToFun.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.map.{u1, u3} α γ _inst_1 _inst_3 (MulHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) x)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Mul.{u1} α] [_inst_2 : Mul.{u2} β] [_inst_3 : Mul.{u3} γ] (f : MulHom.{u1, u2} α β _inst_1 _inst_2) (g : MulHom.{u2, u3} β γ _inst_2 _inst_3) (x : WithOne.{u1} α), Eq.{succ u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u2} β) => WithOne.{u3} γ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (fun (a : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => WithOne.{u2} β) a) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} (WithOne.{u2} β) (WithOne.mulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)))) (WithOne.map.{u1, u2} α β _inst_1 _inst_2 f) x)) (FunLike.coe.{max (succ u2) (succ u3), succ u2, succ u3} (MonoidHom.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u2} β) (fun (_x : WithOne.{u2} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u2} β) => WithOne.{u3} γ) _x) (MulHomClass.toFunLike.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u2} β) (WithOne.{u3} γ) (MulOneClass.toMul.{u2} (WithOne.{u2} β) (WithOne.mulOneClass.{u2} β _inst_2)) (MulOneClass.toMul.{u3} (WithOne.{u3} γ) (WithOne.mulOneClass.{u3} γ _inst_3)) (MonoidHomClass.toMulHomClass.{max u2 u3, u2, u3} (MonoidHom.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3) (MonoidHom.monoidHomClass.{u2, u3} (WithOne.{u2} β) (WithOne.{u3} γ) (WithOne.mulOneClass.{u2} β _inst_2) (WithOne.mulOneClass.{u3} γ _inst_3)))) (WithOne.map.{u2, u3} β γ _inst_2 _inst_3 g) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (fun (_x : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => WithOne.{u2} β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u2} (WithOne.{u2} β) (WithOne.mulOneClass.{u2} β _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)) (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2) (MonoidHom.monoidHomClass.{u1, u2} (WithOne.{u1} α) (WithOne.{u2} β) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u2} β _inst_2)))) (WithOne.map.{u1, u2} α β _inst_1 _inst_2 f) x)) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (MonoidHom.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u1} α) (fun (_x : WithOne.{u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : WithOne.{u1} α) => WithOne.{u3} γ) _x) (MulHomClass.toFunLike.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u1} α) (WithOne.{u3} γ) (MulOneClass.toMul.{u1} (WithOne.{u1} α) (WithOne.mulOneClass.{u1} α _inst_1)) (MulOneClass.toMul.{u3} (WithOne.{u3} γ) (WithOne.mulOneClass.{u3} γ _inst_3)) (MonoidHomClass.toMulHomClass.{max u1 u3, u1, u3} (MonoidHom.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)) (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3) (MonoidHom.monoidHomClass.{u1, u3} (WithOne.{u1} α) (WithOne.{u3} γ) (WithOne.mulOneClass.{u1} α _inst_1) (WithOne.mulOneClass.{u3} γ _inst_3)))) (WithOne.map.{u1, u3} α γ _inst_1 _inst_3 (MulHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) x)
Case conversion may be inaccurate. Consider using '#align with_one.map_map WithOne.map_mapₓ'. -/
@[to_additive]
theorem map_map (f : α →ₙ* β) (g : β →ₙ* γ) (x) : map g (map f x) = map (g.comp f) x := by
  induction x using WithOne.cases_on <;> rfl
#align with_one.map_map WithOne.map_map

#print WithOne.map_comp /-
@[simp, to_additive]
theorem map_comp (f : α →ₙ* β) (g : β →ₙ* γ) : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun x => (map_map f g x).symm
#align with_one.map_comp WithOne.map_comp
-/

#print MulEquiv.withOneCongr /-
/-- A version of `equiv.option_congr` for `with_one`. -/
@[to_additive "A version of `equiv.option_congr` for `with_zero`.", simps apply]
def MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { map e.toMulHom with
    toFun := map e.toMulHom
    invFun := map e.symm.toMulHom
    left_inv := fun x => (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp
    right_inv := fun x =>
      (map_map _ _ _).trans <| by induction x using WithOne.cases_on <;> · simp }
#align mul_equiv.with_one_congr MulEquiv.withOneCongr
-/

#print MulEquiv.withOneCongr_refl /-
@[simp]
theorem MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective map_id
#align mul_equiv.with_one_congr_refl MulEquiv.withOneCongr_refl
-/

#print MulEquiv.withOneCongr_symm /-
@[simp]
theorem MulEquiv.withOneCongr_symm (e : α ≃* β) : e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl
#align mul_equiv.with_one_congr_symm MulEquiv.withOneCongr_symm
-/

#print MulEquiv.withOneCongr_trans /-
@[simp]
theorem MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (map_comp _ _).symm
#align mul_equiv.with_one_congr_trans MulEquiv.withOneCongr_trans
-/

end Map

end WithOne

