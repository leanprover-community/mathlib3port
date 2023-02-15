/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.equiv.basic
! leanprover-community/mathlib commit 369525b73f229ccd76a6ec0e0e0bf2be57599768
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Data.FunLike.Equiv
import Mathbin.Logic.Equiv.Basic
import Mathbin.Data.Pi.Algebra

/-!
# Multiplicative and additive equivs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

* ``infix ` ≃* `:25 := mul_equiv``
* ``infix ` ≃+ `:25 := add_equiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/


variable {F α β A B M N P Q G H : Type _}

#print MulHom.inverse /-
/-- Makes a multiplicative inverse from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive inverse from a bijection which preserves addition."]
def MulHom.inverse [Mul M] [Mul N] (f : M →ₙ* N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₙ* M
    where
  toFun := g
  map_mul' x y :=
    calc
      g (x * y) = g (f (g x) * f (g y)) := by rw [h₂ x, h₂ y]
      _ = g (f (g x * g y)) := by rw [f.map_mul]
      _ = g x * g y := h₁ _
      
#align mul_hom.inverse MulHom.inverse
#align add_hom.inverse AddHom.inverse
-/

/- warning: monoid_hom.inverse -> MonoidHom.inverse is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : Monoid.{u1} A] [_inst_2 : Monoid.{u2} B] (f : MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) (g : B -> A), (Function.LeftInverse.{succ u1, succ u2} A B g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) (fun (_x : MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) => A -> B) (MonoidHom.hasCoeToFun.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) f)) -> (Function.RightInverse.{succ u1, succ u2} A B g (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) (fun (_x : MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) => A -> B) (MonoidHom.hasCoeToFun.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) f)) -> (MonoidHom.{u2, u1} B A (Monoid.toMulOneClass.{u2} B _inst_2) (Monoid.toMulOneClass.{u1} A _inst_1))
but is expected to have type
  forall {A : Type.{u1}} {B : Type.{u2}} [_inst_1 : Monoid.{u1} A] [_inst_2 : Monoid.{u2} B] (f : MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) (g : B -> A), (Function.LeftInverse.{succ u1, succ u2} A B g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : A) => B) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A B (MulOneClass.toMul.{u1} A (Monoid.toMulOneClass.{u1} A _inst_1)) (MulOneClass.toMul.{u2} B (Monoid.toMulOneClass.{u2} B _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2) (MonoidHom.monoidHomClass.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)))) f)) -> (Function.RightInverse.{succ u1, succ u2} A B g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A (fun (_x : A) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : A) => B) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A B (MulOneClass.toMul.{u1} A (Monoid.toMulOneClass.{u1} A _inst_1)) (MulOneClass.toMul.{u2} B (Monoid.toMulOneClass.{u2} B _inst_2)) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)) A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2) (MonoidHom.monoidHomClass.{u1, u2} A B (Monoid.toMulOneClass.{u1} A _inst_1) (Monoid.toMulOneClass.{u2} B _inst_2)))) f)) -> (MonoidHom.{u2, u1} B A (Monoid.toMulOneClass.{u2} B _inst_2) (Monoid.toMulOneClass.{u1} A _inst_1))
Case conversion may be inaccurate. Consider using '#align monoid_hom.inverse MonoidHom.inverseₓ'. -/
/-- The inverse of a bijective `monoid_hom` is a `monoid_hom`. -/
@[to_additive "The inverse of a bijective `add_monoid_hom` is an `add_monoid_hom`.", simps]
def MonoidHom.inverse {A B : Type _} [Monoid A] [Monoid B] (f : A →* B) (g : B → A)
    (h₁ : Function.LeftInverse g f) (h₂ : Function.RightInverse g f) : B →* A :=
  { (f : A →ₙ* B).inverse g h₁ h₂ with
    toFun := g
    map_one' := by rw [← f.map_one, h₁] }
#align monoid_hom.inverse MonoidHom.inverse
#align add_monoid_hom.inverse AddMonoidHom.inverse

#print AddEquiv /-
/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
structure AddEquiv (A B : Type _) [Add A] [Add B] extends A ≃ B, AddHom A B
#align add_equiv AddEquiv
-/

#print AddEquivClass /-
/-- `add_equiv_class F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `add_equiv`. -/
class AddEquivClass (F A B : Type _) [Add A] [Add B] extends EquivLike F A B where
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b
#align add_equiv_class AddEquivClass
-/

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc AddEquiv.toAddHom

#print MulEquiv /-
/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
structure MulEquiv (M N : Type _) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N
#align mul_equiv MulEquiv
#align add_equiv AddEquiv
-/

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc MulEquiv.toMulHom

#print MulEquivClass /-
/-- `mul_equiv_class F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `mul_equiv`. -/
@[to_additive]
class MulEquivClass (F A B : Type _) [Mul A] [Mul B] extends EquivLike F A B where
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b
#align mul_equiv_class MulEquivClass
#align add_equiv_class AddEquivClass
-/

-- mathport name: «expr ≃* »
infixl:25 " ≃* " => MulEquiv

-- mathport name: «expr ≃+ »
infixl:25 " ≃+ " => AddEquiv

namespace MulEquivClass

variable (F)

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [Mul M] [Mul N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with
    coe := (coe : F → M → N)
    coe_injective' := @FunLike.coe_injective F _ _ _ }

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.mulHomClass F with
    coe := (coe : F → M → N)
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (inv e (1 : N) : M) := congr_arg _ (right_inv e 1).symm
        _ = e (inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := right_inv e 1
         }

/- warning: mul_equiv_class.to_monoid_with_zero_hom_class -> MulEquivClass.toMonoidWithZeroHomClass is a dubious translation:
lean 3 declaration is
  forall (F : Type.{u1}) {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : MulZeroOneClass.{u2} α] [_inst_2 : MulZeroOneClass.{u3} β] [_inst_3 : MulEquivClass.{u1, u2, u3} F α β (MulZeroClass.toHasMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulZeroClass.toHasMul.{u3} β (MulZeroOneClass.toMulZeroClass.{u3} β _inst_2))], MonoidWithZeroHomClass.{u1, u2, u3} F α β _inst_1 _inst_2
but is expected to have type
  forall (F : Type.{u1}) {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : MulZeroOneClass.{u2} α} {_inst_2 : MulZeroOneClass.{u3} β} [_inst_3 : MulEquivClass.{u1, u2, u3} F α β (MulZeroClass.toMul.{u2} α (MulZeroOneClass.toMulZeroClass.{u2} α _inst_1)) (MulZeroClass.toMul.{u3} β (MulZeroOneClass.toMulZeroClass.{u3} β _inst_2))], MonoidWithZeroHomClass.{u1, u2, u3} F α β _inst_1 _inst_2
Case conversion may be inaccurate. Consider using '#align mul_equiv_class.to_monoid_with_zero_hom_class MulEquivClass.toMonoidWithZeroHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass {α β : Type _} [MulZeroOneClass α]
    [MulZeroOneClass β] [MulEquivClass F α β] : MonoidWithZeroHomClass F α β :=
  { MulEquivClass.monoidHomClass _ with
    map_zero := fun e =>
      calc
        e 0 = e 0 * e (EquivLike.inv e 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by
          convert mul_zero _
          exact EquivLike.right_inv e _
         }
#align mul_equiv_class.to_monoid_with_zero_hom_class MulEquivClass.toMonoidWithZeroHomClass

variable {F}

/- warning: mul_equiv_class.map_eq_one_iff -> MulEquivClass.map_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : MulEquivClass.{u1, u2, u3} F M N (MulOneClass.toHasMul.{u2} M _inst_1) (MulOneClass.toHasMul.{u3} N _inst_2)] (h : F) {x : M}, Iff (Eq.{succ u3} N (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (EmbeddingLike.toFunLike.{succ u1, succ u2, succ u3} F M N (EquivLike.toEmbeddingLike.{succ u1, succ u2, succ u3} F M N (MulEquivClass.toEquivLike.{u1, u2, u3} F M N (MulOneClass.toHasMul.{u2} M _inst_1) (MulOneClass.toHasMul.{u3} N _inst_2) _inst_3)))) h x) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N _inst_2))))) (Eq.{succ u2} M x (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M _inst_1)))))
but is expected to have type
  forall {F : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulEquivClass.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2)] (h : F) {x : M}, Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{succ u1, succ u3, succ u2} F M N (EquivLike.toEmbeddingLike.{succ u1, succ u3, succ u2} F M N (MulEquivClass.toEquivLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) _inst_3))) h x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) _inst_2)))) (Eq.{succ u3} M x (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M (MulOneClass.toOne.{u3} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_equiv_class.map_eq_one_iff MulEquivClass.map_eq_one_iffₓ'. -/
@[simp, to_additive]
theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
    h x = 1 ↔ x = 1 :=
  map_eq_one_iff h (EquivLike.injective h)
#align mul_equiv_class.map_eq_one_iff MulEquivClass.map_eq_one_iff
#align add_equiv_class.map_eq_zero_iff AddEquivClass.map_eq_zero_iff

/- warning: mul_equiv_class.map_ne_one_iff -> MulEquivClass.map_ne_one_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {M : Type.{u2}} {N : Type.{u3}} [_inst_1 : MulOneClass.{u2} M] [_inst_2 : MulOneClass.{u3} N] [_inst_3 : MulEquivClass.{u1, u2, u3} F M N (MulOneClass.toHasMul.{u2} M _inst_1) (MulOneClass.toHasMul.{u3} N _inst_2)] (h : F) {x : M}, Iff (Ne.{succ u3} N (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F M (fun (_x : M) => N) (EmbeddingLike.toFunLike.{succ u1, succ u2, succ u3} F M N (EquivLike.toEmbeddingLike.{succ u1, succ u2, succ u3} F M N (MulEquivClass.toEquivLike.{u1, u2, u3} F M N (MulOneClass.toHasMul.{u2} M _inst_1) (MulOneClass.toHasMul.{u3} N _inst_2) _inst_3)))) h x) (OfNat.ofNat.{u3} N 1 (OfNat.mk.{u3} N 1 (One.one.{u3} N (MulOneClass.toHasOne.{u3} N _inst_2))))) (Ne.{succ u2} M x (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M _inst_1)))))
but is expected to have type
  forall {F : Type.{u1}} {M : Type.{u3}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u3} M] [_inst_2 : MulOneClass.{u2} N] [_inst_3 : MulEquivClass.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2)] (h : F) {x : M}, Iff (Ne.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{succ u1, succ u3, succ u2} F M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{succ u1, succ u3, succ u2} F M N (EquivLike.toEmbeddingLike.{succ u1, succ u3, succ u2} F M N (MulEquivClass.toEquivLike.{u1, u3, u2} F M N (MulOneClass.toMul.{u3} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2) _inst_3))) h x) (OfNat.ofNat.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) 1 (One.toOfNat1.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (MulOneClass.toOne.{u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) _inst_2)))) (Ne.{succ u3} M x (OfNat.ofNat.{u3} M 1 (One.toOfNat1.{u3} M (MulOneClass.toOne.{u3} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align mul_equiv_class.map_ne_one_iff MulEquivClass.map_ne_one_iffₓ'. -/
@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] (h : F) {x : M} :
    h x ≠ 1 ↔ x ≠ 1 :=
  map_ne_one_iff h (EquivLike.injective h)
#align mul_equiv_class.map_ne_one_iff MulEquivClass.map_ne_one_iff
#align add_equiv_class.map_ne_zero_iff AddEquivClass.map_ne_zero_iff

end MulEquivClass

@[to_additive]
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨fun f =>
    { toFun := f
      invFun := EquivLike.inv f
      left_inv := EquivLike.left_inv f
      right_inv := EquivLike.right_inv f
      map_mul' := map_mul f }⟩

namespace MulEquiv

@[to_additive]
instance [Mul M] [Mul N] : CoeFun (M ≃* N) fun _ => M → N :=
  ⟨MulEquiv.toFun⟩

@[to_additive]
instance [Mul M] [Mul N] : MulEquivClass (M ≃* N) M N
    where
  coe := toFun
  inv := invFun
  left_inv := left_inv
  right_inv := right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
  map_mul := map_mul'

variable [Mul M] [Mul N] [Mul P] [Mul Q]

/- warning: mul_equiv.to_equiv_eq_coe clashes with [anonymous] -> [anonymous]
warning: mul_equiv.to_equiv_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} M N) (MulEquiv.toEquiv.{u1, u2} M N _inst_1 _inst_2 f) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)}) [self : HasLiftT.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} a b] => self.0) (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (HasLiftT.mk.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (CoeTCₓ.coe.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (Equiv.hasCoeT.{succ u1, succ u2, max (succ u1) (succ u2)} M N (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (MulEquivClass.toEquivLike.{max u1 u2, u1, u2} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.mulEquivClass.{u1, u2} M N _inst_1 _inst_2))))) f)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}}, (Nat -> M -> N) -> Nat -> (List.{u1} M) -> (List.{u2} N)
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_equiv_eq_coe [anonymous]ₓ'. -/
@[simp, to_additive]
theorem [anonymous] (f : M ≃* N) : f.toEquiv = f :=
  rfl
#align mul_equiv.to_equiv_eq_coe [anonymous]

/- warning: mul_equiv.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: mul_equiv.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (M -> N) (MulEquiv.toFun.{u1, u2} M N _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}}, (Nat -> M -> N) -> Nat -> (List.{u1} M) -> (List.{u2} N)
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp, to_additive]
theorem [anonymous] {f : M ≃* N} : f.toFun = f :=
  rfl
#align mul_equiv.to_fun_eq_coe [anonymous]

/- warning: mul_equiv.coe_to_equiv -> MulEquiv.coe_toEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} M N) (fun (_x : Equiv.{succ u1, succ u2} M N) => M -> N) (Equiv.hasCoeToFun.{succ u1, succ u2} M N) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)}) [self : HasLiftT.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} a b] => self.0) (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (HasLiftT.mk.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (CoeTCₓ.coe.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (Equiv.{succ u1, succ u2} M N) (Equiv.hasCoeT.{succ u1, succ u2, max (succ u1) (succ u2)} M N (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (MulEquivClass.toEquivLike.{max u1 u2, u1, u2} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.mulEquivClass.{u1, u2} M N _inst_1 _inst_2))))) f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} M N) M (fun (_x : M) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : M) => N) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} M N) (MulEquiv.toEquiv.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_to_equiv MulEquiv.coe_toEquivₓ'. -/
@[simp, to_additive]
theorem coe_toEquiv {f : M ≃* N} : ⇑(f : M ≃ N) = f :=
  rfl
#align mul_equiv.coe_to_equiv MulEquiv.coe_toEquiv
#align add_equiv.coe_to_equiv AddEquiv.coe_toEquiv

/- warning: mul_equiv.coe_to_mul_hom -> MulEquiv.coe_toMulHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulHom.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.toMulHom.{u1, u2} M N _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulHom.mulHomClass.{u2, u1} M N _inst_1 _inst_2)) (MulEquiv.toMulHom.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_to_mul_hom MulEquiv.coe_toMulHomₓ'. -/
@[simp, to_additive]
theorem coe_toMulHom {f : M ≃* N} : ⇑f.toMulHom = f :=
  rfl
#align mul_equiv.coe_to_mul_hom MulEquiv.coe_toMulHom
#align add_equiv.coe_to_add_hom AddEquiv.coe_toAddHom

/- warning: mul_equiv.map_mul -> MulEquiv.map_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (x : M) (y : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (x : M) (y : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) y) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (instHMul.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f y))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_mul MulEquiv.map_mulₓ'. -/
/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive "An additive isomorphism preserves addition."]
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  map_mul f
#align mul_equiv.map_mul MulEquiv.map_mul
#align add_equiv.map_add AddEquiv.map_add

#print MulEquiv.mk' /-
/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N :=
  ⟨f.1, f.2, f.3, f.4, h⟩
#align mul_equiv.mk' MulEquiv.mk'
#align add_equiv.mk' AddEquiv.mk'
-/

/- warning: mul_equiv.bijective -> MulEquiv.bijective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Function.Bijective.{succ u1, succ u2} M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Function.Bijective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)
Case conversion may be inaccurate. Consider using '#align mul_equiv.bijective MulEquiv.bijectiveₓ'. -/
@[to_additive]
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e
#align mul_equiv.bijective MulEquiv.bijective
#align add_equiv.bijective AddEquiv.bijective

/- warning: mul_equiv.injective -> MulEquiv.injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Function.Injective.{succ u1, succ u2} M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Function.Injective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)
Case conversion may be inaccurate. Consider using '#align mul_equiv.injective MulEquiv.injectiveₓ'. -/
@[to_additive]
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e
#align mul_equiv.injective MulEquiv.injective
#align add_equiv.injective AddEquiv.injective

/- warning: mul_equiv.surjective -> MulEquiv.surjective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)
Case conversion may be inaccurate. Consider using '#align mul_equiv.surjective MulEquiv.surjectiveₓ'. -/
@[to_additive]
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e
#align mul_equiv.surjective MulEquiv.surjective
#align add_equiv.surjective AddEquiv.surjective

#print MulEquiv.refl /-
/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive "The identity map is an additive isomorphism."]
def refl (M : Type _) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }
#align mul_equiv.refl MulEquiv.refl
#align add_equiv.refl AddEquiv.refl
-/

@[to_additive]
instance : Inhabited (M ≃* M) :=
  ⟨refl M⟩

#print MulEquiv.symm /-
/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive "The inverse of an isomorphism is an isomorphism."]
def symm (h : M ≃* N) : N ≃* M :=
  { h.toEquiv.symm with
    map_mul' := (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv).map_mul }
#align mul_equiv.symm MulEquiv.symm
#align add_equiv.symm AddEquiv.symm
-/

/- warning: mul_equiv.inv_fun_eq_symm -> MulEquiv.invFun_eq_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (N -> M) (MulEquiv.invFun.{u1, u2} M N _inst_1 _inst_2 f) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (N -> M) (Equiv.invFun.{succ u2, succ u1} M N (MulEquiv.toEquiv.{u2, u1} M N _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align mul_equiv.inv_fun_eq_symm MulEquiv.invFun_eq_symmₓ'. -/
@[simp, to_additive]
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm :=
  rfl
#align mul_equiv.inv_fun_eq_symm MulEquiv.invFun_eq_symm
#align add_equiv.neg_fun_eq_symm AddEquiv.invFun_eq_symm

#print MulEquiv.Simps.symmApply /-
-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.
/-- See Note [custom simps projection] -/
@[to_additive "See Note custom simps projection"]
def Simps.symmApply (e : M ≃* N) : N → M :=
  e.symm
#align mul_equiv.simps.symm_apply MulEquiv.Simps.symmApply
#align add_equiv.simps.symm_apply AddEquiv.Simps.symmApply
-/

initialize_simps_projections AddEquiv (toFun → apply, invFun → symm_apply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)

/- warning: mul_equiv.to_equiv_symm -> MulEquiv.toEquiv_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} N M) (MulEquiv.toEquiv.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 f)) (Equiv.symm.{succ u1, succ u2} M N (MulEquiv.toEquiv.{u1, u2} M N _inst_1 _inst_2 f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} N M) (MulEquiv.toEquiv.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 f)) (Equiv.symm.{succ u2, succ u1} M N (MulEquiv.toEquiv.{u2, u1} M N _inst_1 _inst_2 f))
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_equiv_symm MulEquiv.toEquiv_symmₓ'. -/
@[simp, to_additive]
theorem toEquiv_symm (f : M ≃* N) : f.symm.toEquiv = f.toEquiv.symm :=
  rfl
#align mul_equiv.to_equiv_symm MulEquiv.toEquiv_symm
#align add_equiv.to_equiv_symm AddEquiv.toEquiv_symm

@[simp, to_additive]
theorem coe_mk (f : M → N) (g h₁ h₂ h₃) : ⇑(MulEquiv.mk f g h₁ h₂ h₃) = f :=
  rfl
#align mul_equiv.coe_mk MulEquiv.coe_mkₓ
#align add_equiv.coe_mk AddEquiv.coe_mkₓ

/- warning: mul_equiv.to_equiv_mk clashes with [anonymous] -> [anonymous]
warning: mul_equiv.to_equiv_mk -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : M -> N) (g : N -> M) (h₁ : Function.LeftInverse.{succ u1, succ u2} M N g f) (h₂ : Function.RightInverse.{succ u1, succ u2} M N g f) (h₃ : forall (x : M) (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (f x) (f y))), Eq.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} M N) (MulEquiv.toEquiv.{u1, u2} M N _inst_1 _inst_2 (MulEquiv.mk.{u1, u2} M N _inst_1 _inst_2 f g h₁ h₂ h₃)) (Equiv.mk.{succ u1, succ u2} M N f g h₁ h₂)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}}, (Nat -> M -> N) -> Nat -> (List.{u1} M) -> (List.{u2} N)
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_equiv_mk [anonymous]ₓ'. -/
@[simp, to_additive]
theorem [anonymous] (f : M → N) (g : N → M) (h₁ h₂ h₃) :
    (mk f g h₁ h₂ h₃).toEquiv = ⟨f, g, h₁, h₂⟩ :=
  rfl
#align mul_equiv.to_equiv_mk [anonymous]

/- warning: mul_equiv.symm_symm -> MulEquiv.symm_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (f : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.symm.{u2, u1} N M _inst_2 _inst_1 (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 f)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (f : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.symm.{u1, u2} N M _inst_2 _inst_1 (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 f)) f
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_symm MulEquiv.symm_symmₓ'. -/
@[simp, to_additive]
theorem symm_symm : ∀ f : M ≃* N, f.symm.symm = f
  | ⟨f, g, h₁, h₂, h₃⟩ => rfl
#align mul_equiv.symm_symm MulEquiv.symm_symm
#align add_equiv.symm_symm AddEquiv.symm_symm

/- warning: mul_equiv.symm_bijective -> MulEquiv.symm_bijective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N], Function.Bijective.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N], Function.Bijective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.{u1, u2} N M _inst_2 _inst_1) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_bijective MulEquiv.symm_bijectiveₓ'. -/
@[to_additive]
theorem symm_bijective : Function.Bijective (symm : M ≃* N → N ≃* M) :=
  Equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩
#align mul_equiv.symm_bijective MulEquiv.symm_bijective
#align add_equiv.symm_bijective AddEquiv.symm_bijective

@[simp, to_additive]
theorem symm_mk (f : M → N) (g h₁ h₂ h₃) :
    (MulEquiv.mk f g h₁ h₂ h₃).symm =
      { (MulEquiv.mk f g h₁ h₂ h₃).symm with
        toFun := g
        invFun := f } :=
  rfl
#align mul_equiv.symm_mk MulEquiv.symm_mkₓ
#align add_equiv.symm_mk AddEquiv.symm_mkₓ

#print MulEquiv.refl_symm /-
@[simp, to_additive]
theorem refl_symm : (refl M).symm = refl M :=
  rfl
#align mul_equiv.refl_symm MulEquiv.refl_symm
#align add_equiv.refl_symm AddEquiv.refl_symm
-/

#print MulEquiv.trans /-
/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y =>
      show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by rw [h1.map_mul, h2.map_mul] }
#align mul_equiv.trans MulEquiv.trans
#align add_equiv.trans AddEquiv.trans
-/

/- warning: mul_equiv.apply_symm_apply -> MulEquiv.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (y : N), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) y)) y
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (y : N), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (a : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) y)) y
Case conversion may be inaccurate. Consider using '#align mul_equiv.apply_symm_apply MulEquiv.apply_symm_applyₓ'. -/
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[simp, to_additive "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y
#align mul_equiv.apply_symm_apply MulEquiv.apply_symm_apply
#align add_equiv.apply_symm_apply AddEquiv.apply_symm_apply

/- warning: mul_equiv.symm_apply_apply -> MulEquiv.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (x : M), Eq.{succ u1} M (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e x)) x
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (x : M), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e x)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e x)) x
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_apply_apply MulEquiv.symm_apply_applyₓ'. -/
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[simp, to_additive "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x
#align mul_equiv.symm_apply_apply MulEquiv.symm_apply_apply
#align add_equiv.symm_apply_apply AddEquiv.symm_apply_apply

/- warning: mul_equiv.symm_comp_self -> MulEquiv.symm_comp_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (M -> M) (Function.comp.{succ u1, succ u2, succ u1} M N M (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)) (id.{succ u1} M)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u2} (M -> M) (Function.comp.{succ u2, succ u1, succ u2} M N M (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)) (id.{succ u2} M)
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_comp_self MulEquiv.symm_comp_selfₓ'. -/
@[simp, to_additive]
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply
#align mul_equiv.symm_comp_self MulEquiv.symm_comp_self
#align add_equiv.symm_comp_self AddEquiv.symm_comp_self

/- warning: mul_equiv.self_comp_symm -> MulEquiv.self_comp_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (N -> N) (Function.comp.{succ u2, succ u1, succ u2} N M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e))) (id.{succ u2} N)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (N -> N) (Function.comp.{succ u1, succ u2, succ u1} N M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e))) (id.{succ u1} N)
Case conversion may be inaccurate. Consider using '#align mul_equiv.self_comp_symm MulEquiv.self_comp_symmₓ'. -/
@[simp, to_additive]
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply
#align mul_equiv.self_comp_symm MulEquiv.self_comp_symm
#align add_equiv.self_comp_symm AddEquiv.self_comp_symm

/- warning: mul_equiv.coe_refl -> MulEquiv.coe_refl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], Eq.{succ u1} (M -> M) (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) (fun (_x : MulEquiv.{u1, u1} M M _inst_1 _inst_1) => M -> M) (MulEquiv.hasCoeToFun.{u1, u1} M M _inst_1 _inst_1) (MulEquiv.refl.{u1} M _inst_1)) (id.{succ u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M], Eq.{succ u1} (M -> M) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M _inst_1 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} M M _inst_1 _inst_1)))) (MulEquiv.refl.{u1} M _inst_1)) (id.{succ u1} M)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_refl MulEquiv.coe_reflₓ'. -/
@[simp, to_additive]
theorem coe_refl : ⇑(refl M) = id :=
  rfl
#align mul_equiv.coe_refl MulEquiv.coe_refl
#align add_equiv.coe_refl AddEquiv.coe_refl

/- warning: mul_equiv.refl_apply -> MulEquiv.refl_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (m : M), Eq.{succ u1} M (coeFn.{succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) (fun (_x : MulEquiv.{u1, u1} M M _inst_1 _inst_1) => M -> M) (MulEquiv.hasCoeToFun.{u1, u1} M M _inst_1 _inst_1) (MulEquiv.refl.{u1} M _inst_1) m) m
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Mul.{u1} M] (m : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => M) m) (FunLike.coe.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M (MulEquivClass.toEquivLike.{u1, u1, u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) M M _inst_1 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} M M _inst_1 _inst_1)))) (MulEquiv.refl.{u1} M _inst_1) m) m
Case conversion may be inaccurate. Consider using '#align mul_equiv.refl_apply MulEquiv.refl_applyₓ'. -/
@[simp, to_additive]
theorem refl_apply (m : M) : refl M m = m :=
  rfl
#align mul_equiv.refl_apply MulEquiv.refl_apply
#align add_equiv.refl_apply AddEquiv.refl_apply

/- warning: mul_equiv.coe_trans -> MulEquiv.coe_trans is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (e₁ : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u3} N P _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (M -> P) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MulEquiv.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulEquiv.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulEquiv.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MulEquiv.trans.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 e₁ e₂)) (Function.comp.{succ u1, succ u2, succ u3} M N P (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulEquiv.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MulEquiv.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MulEquiv.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) e₂) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e₁))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (e₁ : MulEquiv.{u3, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u1} N P _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} (M -> P) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => P) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P (MulEquivClass.toEquivLike.{max u3 u1, u3, u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulEquiv.instMulEquivClassMulEquiv.{u3, u1} M P _inst_1 _inst_3)))) (MulEquiv.trans.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 e₁ e₂)) (Function.comp.{succ u3, succ u2, succ u1} M N P (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => P) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} N P _inst_2 _inst_3)))) e₂) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N _inst_1 _inst_2)))) e₁))
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_trans MulEquiv.coe_transₓ'. -/
@[simp, to_additive]
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl
#align mul_equiv.coe_trans MulEquiv.coe_trans
#align add_equiv.coe_trans AddEquiv.coe_trans

/- warning: mul_equiv.trans_apply -> MulEquiv.trans_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (e₁ : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u3} N P _inst_2 _inst_3) (m : M), Eq.{succ u3} P (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (MulEquiv.{u1, u3} M P _inst_1 _inst_3) (fun (_x : MulEquiv.{u1, u3} M P _inst_1 _inst_3) => M -> P) (MulEquiv.hasCoeToFun.{u1, u3} M P _inst_1 _inst_3) (MulEquiv.trans.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 e₁ e₂) m) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (MulEquiv.{u2, u3} N P _inst_2 _inst_3) (fun (_x : MulEquiv.{u2, u3} N P _inst_2 _inst_3) => N -> P) (MulEquiv.hasCoeToFun.{u2, u3} N P _inst_2 _inst_3) e₂ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e₁ m))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (e₁ : MulEquiv.{u3, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u1} N P _inst_2 _inst_3) (m : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => P) m) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => P) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u3, succ u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P (MulEquivClass.toEquivLike.{max u3 u1, u3, u1} (MulEquiv.{u3, u1} M P _inst_1 _inst_3) M P _inst_1 _inst_3 (MulEquiv.instMulEquivClassMulEquiv.{u3, u1} M P _inst_1 _inst_3)))) (MulEquiv.trans.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 e₁ e₂) m) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => P) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} N P _inst_2 _inst_3) N P _inst_2 _inst_3 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} N P _inst_2 _inst_3)))) e₂ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N _inst_1 _inst_2)))) e₁ m))
Case conversion may be inaccurate. Consider using '#align mul_equiv.trans_apply MulEquiv.trans_applyₓ'. -/
@[simp, to_additive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) :=
  rfl
#align mul_equiv.trans_apply MulEquiv.trans_apply
#align add_equiv.trans_apply AddEquiv.trans_apply

/- warning: mul_equiv.symm_trans_apply -> MulEquiv.symm_trans_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u3} P] (e₁ : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u3} N P _inst_2 _inst_3) (p : P), Eq.{succ u1} M (coeFn.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (MulEquiv.{u3, u1} P M _inst_3 _inst_1) (fun (_x : MulEquiv.{u3, u1} P M _inst_3 _inst_1) => P -> M) (MulEquiv.hasCoeToFun.{u3, u1} P M _inst_3 _inst_1) (MulEquiv.symm.{u1, u3} M P _inst_1 _inst_3 (MulEquiv.trans.{u1, u2, u3} M N P _inst_1 _inst_2 _inst_3 e₁ e₂)) p) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e₁) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (MulEquiv.{u3, u2} P N _inst_3 _inst_2) (fun (_x : MulEquiv.{u3, u2} P N _inst_3 _inst_2) => P -> N) (MulEquiv.hasCoeToFun.{u3, u2} P N _inst_3 _inst_2) (MulEquiv.symm.{u2, u3} N P _inst_2 _inst_3 e₂) p))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_1 : Mul.{u3} M] [_inst_2 : Mul.{u2} N] [_inst_3 : Mul.{u1} P] (e₁ : MulEquiv.{u3, u2} M N _inst_1 _inst_2) (e₂ : MulEquiv.{u2, u1} N P _inst_2 _inst_3) (p : P), Eq.{succ u3} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : P) => M) p) (FunLike.coe.{max (succ u3) (succ u1), succ u1, succ u3} (MulEquiv.{u1, u3} P M _inst_3 _inst_1) P (fun (_x : P) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : P) => M) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u1, succ u3} (MulEquiv.{u1, u3} P M _inst_3 _inst_1) P M (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u1, succ u3} (MulEquiv.{u1, u3} P M _inst_3 _inst_1) P M (MulEquivClass.toEquivLike.{max u3 u1, u1, u3} (MulEquiv.{u1, u3} P M _inst_3 _inst_1) P M _inst_3 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u3} P M _inst_3 _inst_1)))) (MulEquiv.symm.{u3, u1} M P _inst_1 _inst_3 (MulEquiv.trans.{u3, u2, u1} M N P _inst_1 _inst_2 _inst_3 e₁ e₂)) p) (FunLike.coe.{max (succ u3) (succ u2), succ u2, succ u3} (MulEquiv.{u2, u3} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u2, succ u3} (MulEquiv.{u2, u3} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u2, succ u3} (MulEquiv.{u2, u3} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u3 u2, u2, u3} (MulEquiv.{u2, u3} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u2, u3} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u3, u2} M N _inst_1 _inst_2 e₁) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} P N _inst_3 _inst_2) P (fun (_x : P) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : P) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} P N _inst_3 _inst_2) P N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} P N _inst_3 _inst_2) P N (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} P N _inst_3 _inst_2) P N _inst_3 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} P N _inst_3 _inst_2)))) (MulEquiv.symm.{u2, u1} N P _inst_2 _inst_3 e₂) p))
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_trans_apply MulEquiv.symm_trans_applyₓ'. -/
@[simp, to_additive]
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) :=
  rfl
#align mul_equiv.symm_trans_apply MulEquiv.symm_trans_apply
#align add_equiv.symm_trans_apply AddEquiv.symm_trans_apply

/- warning: mul_equiv.apply_eq_iff_eq -> MulEquiv.apply_eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : M}, Iff (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e y)) (Eq.{succ u1} M x y)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : M}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e y)) (Eq.{succ u2} M x y)
Case conversion may be inaccurate. Consider using '#align mul_equiv.apply_eq_iff_eq MulEquiv.apply_eq_iff_eqₓ'. -/
@[simp, to_additive]
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.Injective.eq_iff
#align mul_equiv.apply_eq_iff_eq MulEquiv.apply_eq_iff_eq
#align add_equiv.apply_eq_iff_eq AddEquiv.apply_eq_iff_eq

/- warning: mul_equiv.apply_eq_iff_symm_apply -> MulEquiv.apply_eq_iff_symm_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) {x : M} {y : N}, Iff (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e x) y) (Eq.{succ u1} M x (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) {x : M} {y : N}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e x) y) (Eq.{succ u2} M x (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) y))
Case conversion may be inaccurate. Consider using '#align mul_equiv.apply_eq_iff_symm_apply MulEquiv.apply_eq_iff_symm_applyₓ'. -/
@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply
#align mul_equiv.apply_eq_iff_symm_apply MulEquiv.apply_eq_iff_symm_apply
#align add_equiv.apply_eq_iff_symm_apply AddEquiv.apply_eq_iff_symm_apply

/- warning: mul_equiv.symm_apply_eq -> MulEquiv.symm_apply_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) {x : N} {y : M}, Iff (Eq.{succ u1} M (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) x) y) (Eq.{succ u2} N x (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e y))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) {x : N} {y : (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) x}, Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) x) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) x) y) (Eq.{succ u1} N x (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e y))
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_apply_eq MulEquiv.symm_apply_eqₓ'. -/
@[to_additive]
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq
#align mul_equiv.symm_apply_eq MulEquiv.symm_apply_eq
#align add_equiv.symm_apply_eq AddEquiv.symm_apply_eq

/- warning: mul_equiv.eq_symm_apply -> MulEquiv.eq_symm_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) {x : N} {y : M}, Iff (Eq.{succ u1} M y (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) x)) (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e y) x)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) {x : N} {y : (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) x}, Iff (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) x) y (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) x)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) y) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e y) x)
Case conversion may be inaccurate. Consider using '#align mul_equiv.eq_symm_apply MulEquiv.eq_symm_applyₓ'. -/
@[to_additive]
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply
#align mul_equiv.eq_symm_apply MulEquiv.eq_symm_apply
#align add_equiv.eq_symm_apply AddEquiv.eq_symm_apply

/- warning: mul_equiv.eq_comp_symm -> MulEquiv.eq_comp_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {α : Type.{u3}} (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (f : N -> α) (g : M -> α), Iff (Eq.{max (succ u2) (succ u3)} (N -> α) f (Function.comp.{succ u2, succ u1, succ u3} N M α g (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)))) (Eq.{max (succ u1) (succ u3)} (M -> α) (Function.comp.{succ u1, succ u2, succ u3} M N α f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)) g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {α : Type.{u3}} (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (f : N -> α) (g : M -> α), Iff (Eq.{max (succ u1) (succ u3)} (N -> α) f (Function.comp.{succ u1, succ u2, succ u3} N M α g (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)))) (Eq.{max (succ u2) (succ u3)} (M -> α) (Function.comp.{succ u2, succ u1, succ u3} M N α f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)) g)
Case conversion may be inaccurate. Consider using '#align mul_equiv.eq_comp_symm MulEquiv.eq_comp_symmₓ'. -/
@[to_additive]
theorem eq_comp_symm {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g
#align mul_equiv.eq_comp_symm MulEquiv.eq_comp_symm
#align add_equiv.eq_comp_symm AddEquiv.eq_comp_symm

/- warning: mul_equiv.comp_symm_eq -> MulEquiv.comp_symm_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {α : Type.{u3}} (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (f : N -> α) (g : M -> α), Iff (Eq.{max (succ u2) (succ u3)} (N -> α) (Function.comp.{succ u2, succ u1, succ u3} N M α g (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e))) f) (Eq.{max (succ u1) (succ u3)} (M -> α) g (Function.comp.{succ u1, succ u2, succ u3} M N α f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {α : Type.{u3}} (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (f : N -> α) (g : M -> α), Iff (Eq.{max (succ u1) (succ u3)} (N -> α) (Function.comp.{succ u1, succ u2, succ u3} N M α g (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e))) f) (Eq.{max (succ u2) (succ u3)} (M -> α) g (Function.comp.{succ u2, succ u1, succ u3} M N α f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.comp_symm_eq MulEquiv.comp_symm_eqₓ'. -/
@[to_additive]
theorem comp_symm_eq {α : Type _} (e : M ≃* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g
#align mul_equiv.comp_symm_eq MulEquiv.comp_symm_eq
#align add_equiv.comp_symm_eq AddEquiv.comp_symm_eq

/- warning: mul_equiv.eq_symm_comp -> MulEquiv.eq_symm_comp is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {α : Type.{u3}} (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (f : α -> M) (g : α -> N), Iff (Eq.{max (succ u3) (succ u1)} (α -> M) f (Function.comp.{succ u3, succ u2, succ u1} α N M (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)) g)) (Eq.{max (succ u3) (succ u2)} (α -> N) (Function.comp.{succ u3, succ u1, succ u2} α M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) f) g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {α : Type.{u3}} (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (f : α -> M) (g : α -> N), Iff (Eq.{max (succ u2) (succ u3)} (α -> M) f (Function.comp.{succ u3, succ u1, succ u2} α N M (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)) g)) (Eq.{max (succ u1) (succ u3)} (α -> N) (Function.comp.{succ u3, succ u2, succ u1} α M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) f) g)
Case conversion may be inaccurate. Consider using '#align mul_equiv.eq_symm_comp MulEquiv.eq_symm_compₓ'. -/
@[to_additive]
theorem eq_symm_comp {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g
#align mul_equiv.eq_symm_comp MulEquiv.eq_symm_comp
#align add_equiv.eq_symm_comp AddEquiv.eq_symm_comp

/- warning: mul_equiv.symm_comp_eq -> MulEquiv.symm_comp_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {α : Type.{u3}} (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (f : α -> M) (g : α -> N), Iff (Eq.{max (succ u3) (succ u1)} (α -> M) (Function.comp.{succ u3, succ u2, succ u1} α N M (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (fun (_x : MulEquiv.{u2, u1} N M _inst_2 _inst_1) => N -> M) (MulEquiv.hasCoeToFun.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)) g) f) (Eq.{max (succ u3) (succ u2)} (α -> N) g (Function.comp.{succ u3, succ u1, succ u2} α M N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) f))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {α : Type.{u3}} (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (f : α -> M) (g : α -> N), Iff (Eq.{max (succ u2) (succ u3)} (α -> M) (Function.comp.{succ u3, succ u1, succ u2} α N M (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N (fun (_x : N) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : N) => M) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M (MulEquivClass.toEquivLike.{max u2 u1, u1, u2} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) N M _inst_2 _inst_1 (MulEquiv.instMulEquivClassMulEquiv.{u1, u2} N M _inst_2 _inst_1)))) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)) g) f) (Eq.{max (succ u1) (succ u3)} (α -> N) g (Function.comp.{succ u3, succ u2, succ u1} α M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) f))
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_comp_eq MulEquiv.symm_comp_eqₓ'. -/
@[to_additive]
theorem symm_comp_eq {α : Type _} (e : M ≃* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g
#align mul_equiv.symm_comp_eq MulEquiv.symm_comp_eq
#align add_equiv.symm_comp_eq AddEquiv.symm_comp_eq

/- warning: mul_equiv.symm_trans_self -> MulEquiv.symm_trans_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u2} (MulEquiv.{u2, u2} N N _inst_2 _inst_2) (MulEquiv.trans.{u2, u1, u2} N M N _inst_2 _inst_1 _inst_2 (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e) e) (MulEquiv.refl.{u2} N _inst_2)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u1} (MulEquiv.{u1, u1} N N _inst_2 _inst_2) (MulEquiv.trans.{u1, u2, u1} N M N _inst_2 _inst_1 _inst_2 (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e) e) (MulEquiv.refl.{u1} N _inst_2)
Case conversion may be inaccurate. Consider using '#align mul_equiv.symm_trans_self MulEquiv.symm_trans_selfₓ'. -/
@[simp, to_additive]
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  FunLike.ext _ _ e.apply_symm_apply
#align mul_equiv.symm_trans_self MulEquiv.symm_trans_self
#align add_equiv.symm_trans_self AddEquiv.symm_trans_self

/- warning: mul_equiv.self_trans_symm -> MulEquiv.self_trans_symm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2), Eq.{succ u1} (MulEquiv.{u1, u1} M M _inst_1 _inst_1) (MulEquiv.trans.{u1, u2, u1} M N M _inst_1 _inst_2 _inst_1 e (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)) (MulEquiv.refl.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2), Eq.{succ u2} (MulEquiv.{u2, u2} M M _inst_1 _inst_1) (MulEquiv.trans.{u2, u1, u2} M N M _inst_1 _inst_2 _inst_1 e (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)) (MulEquiv.refl.{u2} M _inst_1)
Case conversion may be inaccurate. Consider using '#align mul_equiv.self_trans_symm MulEquiv.self_trans_symmₓ'. -/
@[simp, to_additive]
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  FunLike.ext _ _ e.symm_apply_apply
#align mul_equiv.self_trans_symm MulEquiv.self_trans_symm
#align add_equiv.self_trans_symm AddEquiv.self_trans_symm

/- warning: mul_equiv.coe_monoid_hom_refl -> MulEquiv.coe_monoidHom_refl is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M], Eq.{succ u1} (MonoidHom.{u1, u1} M M _inst_5 _inst_5) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (MulEquiv.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)) (MonoidHom.{u1, u1} M M _inst_5 _inst_5) (HasLiftT.mk.{succ u1, succ u1} (MulEquiv.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)) (MonoidHom.{u1, u1} M M _inst_5 _inst_5) (CoeTCₓ.coe.{succ u1, succ u1} (MulEquiv.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)) (MonoidHom.{u1, u1} M M _inst_5 _inst_5) (MonoidHom.hasCoeT.{u1, u1, u1} M M (MulEquiv.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)) _inst_5 _inst_5 (MulEquivClass.monoidHomClass.{u1, u1, u1} (MulEquiv.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)) M M _inst_5 _inst_5 (MulEquiv.mulEquivClass.{u1, u1} M M (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u1} M _inst_5)))))) (MulEquiv.refl.{u1} M (MulOneClass.toHasMul.{u1} M _inst_5))) (MonoidHom.id.{u1} M _inst_5)
but is expected to have type
  forall {M : Type.{u1}} [_inst_5 : MulOneClass.{u1} M], Eq.{succ u1} (MonoidHom.{u1, u1} M M _inst_5 _inst_5) (MonoidHomClass.toMonoidHom.{u1, u1, u1} M M (MulEquiv.{u1, u1} M M (MulOneClass.toMul.{u1} M _inst_5) (MulOneClass.toMul.{u1} M _inst_5)) _inst_5 _inst_5 (MulEquivClass.instMonoidHomClass.{u1, u1, u1} (MulEquiv.{u1, u1} M M (MulOneClass.toMul.{u1} M _inst_5) (MulOneClass.toMul.{u1} M _inst_5)) M M _inst_5 _inst_5 (MulEquiv.instMulEquivClassMulEquiv.{u1, u1} M M (MulOneClass.toMul.{u1} M _inst_5) (MulOneClass.toMul.{u1} M _inst_5))) (MulEquiv.refl.{u1} M (MulOneClass.toMul.{u1} M _inst_5))) (MonoidHom.id.{u1} M _inst_5)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_monoid_hom_refl MulEquiv.coe_monoidHom_reflₓ'. -/
@[to_additive, simp]
theorem coe_monoidHom_refl {M} [MulOneClass M] : (refl M : M →* M) = MonoidHom.id M :=
  rfl
#align mul_equiv.coe_monoid_hom_refl MulEquiv.coe_monoidHom_refl
#align add_equiv.coe_add_monoid_hom_refl AddEquiv.coe_addMonoidHom_refl

/- warning: mul_equiv.coe_monoid_hom_trans -> MulEquiv.coe_monoidHom_trans is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] [_inst_7 : MulOneClass.{u3} P] (e₁ : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (e₂ : MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u1, u3} M P _inst_5 _inst_7) ((fun (a : Sort.{max (succ u1) (succ u3)}) (b : Sort.{max (succ u3) (succ u1)}) [self : HasLiftT.{max (succ u1) (succ u3), max (succ u3) (succ u1)} a b] => self.0) (MulEquiv.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u1, u3} M P _inst_5 _inst_7) (HasLiftT.mk.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (MulEquiv.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u1, u3} M P _inst_5 _inst_7) (CoeTCₓ.coe.{max (succ u1) (succ u3), max (succ u3) (succ u1)} (MulEquiv.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u1, u3} M P _inst_5 _inst_7) (MonoidHom.hasCoeT.{u1, u3, max u1 u3} M P (MulEquiv.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)) _inst_5 _inst_7 (MulEquivClass.monoidHomClass.{max u1 u3, u1, u3} (MulEquiv.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)) M P _inst_5 _inst_7 (MulEquiv.mulEquivClass.{u1, u3} M P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u3} P _inst_7)))))) (MulEquiv.trans.{u1, u2, u3} M N P (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7) e₁ e₂)) (MonoidHom.comp.{u1, u2, u3} M N P _inst_5 _inst_6 _inst_7 ((fun (a : Sort.{max (succ u2) (succ u3)}) (b : Sort.{max (succ u3) (succ u2)}) [self : HasLiftT.{max (succ u2) (succ u3), max (succ u3) (succ u2)} a b] => self.0) (MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u2, u3} N P _inst_6 _inst_7) (HasLiftT.mk.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u2, u3} N P _inst_6 _inst_7) (CoeTCₓ.coe.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)) (MonoidHom.{u2, u3} N P _inst_6 _inst_7) (MonoidHom.hasCoeT.{u2, u3, max u2 u3} N P (MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)) _inst_6 _inst_7 (MulEquivClass.monoidHomClass.{max u2 u3, u2, u3} (MulEquiv.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)) N P _inst_6 _inst_7 (MulEquiv.mulEquivClass.{u2, u3} N P (MulOneClass.toHasMul.{u2} N _inst_6) (MulOneClass.toHasMul.{u3} P _inst_7)))))) e₂) ((fun (a : Sort.{max (succ u1) (succ u2)}) (b : Sort.{max (succ u2) (succ u1)}) [self : HasLiftT.{max (succ u1) (succ u2), max (succ u2) (succ u1)} a b] => self.0) (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (HasLiftT.mk.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (CoeTCₓ.coe.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (MonoidHom.hasCoeT.{u1, u2, max u1 u2} M N (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) _inst_5 _inst_6 (MulEquivClass.monoidHomClass.{max u1 u2, u1, u2} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) M N _inst_5 _inst_6 (MulEquiv.mulEquivClass.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)))))) e₁))
but is expected to have type
  forall {M : Type.{u3}} {N : Type.{u2}} {P : Type.{u1}} [_inst_5 : MulOneClass.{u3} M] [_inst_6 : MulOneClass.{u2} N] [_inst_7 : MulOneClass.{u1} P] (e₁ : MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6)) (e₂ : MulEquiv.{u2, u1} N P (MulOneClass.toMul.{u2} N _inst_6) (MulOneClass.toMul.{u1} P _inst_7)), Eq.{max (succ u3) (succ u1)} (MonoidHom.{u3, u1} M P _inst_5 _inst_7) (MonoidHomClass.toMonoidHom.{u3, u1, max u3 u1} M P (MulEquiv.{u3, u1} M P (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u1} P _inst_7)) _inst_5 _inst_7 (MulEquivClass.instMonoidHomClass.{max u3 u1, u3, u1} (MulEquiv.{u3, u1} M P (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u1} P _inst_7)) M P _inst_5 _inst_7 (MulEquiv.instMulEquivClassMulEquiv.{u3, u1} M P (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u1} P _inst_7))) (MulEquiv.trans.{u3, u2, u1} M N P (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6) (MulOneClass.toMul.{u1} P _inst_7) e₁ e₂)) (MonoidHom.comp.{u3, u2, u1} M N P _inst_5 _inst_6 _inst_7 (MonoidHomClass.toMonoidHom.{u2, u1, max u2 u1} N P (MulEquiv.{u2, u1} N P (MulOneClass.toMul.{u2} N _inst_6) (MulOneClass.toMul.{u1} P _inst_7)) _inst_6 _inst_7 (MulEquivClass.instMonoidHomClass.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} N P (MulOneClass.toMul.{u2} N _inst_6) (MulOneClass.toMul.{u1} P _inst_7)) N P _inst_6 _inst_7 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} N P (MulOneClass.toMul.{u2} N _inst_6) (MulOneClass.toMul.{u1} P _inst_7))) e₂) (MonoidHomClass.toMonoidHom.{u3, u2, max u3 u2} M N (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6)) _inst_5 _inst_6 (MulEquivClass.instMonoidHomClass.{max u3 u2, u3, u2} (MulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6)) M N _inst_5 _inst_6 (MulEquiv.instMulEquivClassMulEquiv.{u3, u2} M N (MulOneClass.toMul.{u3} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6))) e₁))
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_monoid_hom_trans MulEquiv.coe_monoidHom_transₓ'. -/
@[to_additive, simp]
theorem coe_monoidHom_trans {M N P} [MulOneClass M] [MulOneClass N] [MulOneClass P] (e₁ : M ≃* N)
    (e₂ : N ≃* P) : (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ :=
  rfl
#align mul_equiv.coe_monoid_hom_trans MulEquiv.coe_monoidHom_trans
#align add_equiv.coe_add_monoid_hom_trans AddEquiv.coe_addMonoidHom_trans

/- warning: mul_equiv.ext -> MulEquiv.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2} {g : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x)) -> (Eq.{max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2} {g : MulEquiv.{u2, u1} M N _inst_1 _inst_2}, (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) g x)) -> (Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align mul_equiv.ext MulEquiv.extₓ'. -/
/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext,
  to_additive
      "Two additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h
#align mul_equiv.ext MulEquiv.ext
#align add_equiv.ext AddEquiv.ext

/- warning: mul_equiv.ext_iff -> MulEquiv.ext_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2} {g : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2} {g : MulEquiv.{u2, u1} M N _inst_1 _inst_2}, Iff (Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) f g) (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) g x))
Case conversion may be inaccurate. Consider using '#align mul_equiv.ext_iff MulEquiv.ext_iffₓ'. -/
@[to_additive]
theorem ext_iff {f g : MulEquiv M N} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff
#align mul_equiv.ext_iff MulEquiv.ext_iff
#align add_equiv.ext_iff AddEquiv.ext_iff

/- warning: mul_equiv.mk_coe -> MulEquiv.mk_coe is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (e' : N -> M) (h₁ : Function.LeftInverse.{succ u1, succ u2} M N e' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)) (h₂ : Function.RightInverse.{succ u1, succ u2} M N e' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e)) (h₃ : forall (x : M) (y : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e y))), Eq.{max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (MulEquiv.mk.{u1, u2} M N _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) e' h₁ h₂ h₃) e
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (e' : N -> M) (h₁ : Function.LeftInverse.{succ u2, succ u1} M N e' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)) (h₂ : Function.RightInverse.{succ u2, succ u1} M N e' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e)) (h₃ : forall (x : M) (y : M), Eq.{succ u1} N (Equiv.toFun.{succ u2, succ u1} M N (Equiv.mk.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) e' h₁ h₂) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) (Equiv.toFun.{succ u2, succ u1} M N (Equiv.mk.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) e' h₁ h₂) x) (Equiv.toFun.{succ u2, succ u1} M N (Equiv.mk.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) e' h₁ h₂) y))), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) (MulEquiv.mk.{u2, u1} M N _inst_1 _inst_2 (Equiv.mk.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) e' h₁ h₂) h₃) e
Case conversion may be inaccurate. Consider using '#align mul_equiv.mk_coe MulEquiv.mk_coeₓ'. -/
@[simp, to_additive]
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨e, e', h₁, h₂, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl
#align mul_equiv.mk_coe MulEquiv.mk_coe
#align add_equiv.mk_coe AddEquiv.mk_coe

/- warning: mul_equiv.mk_coe' -> MulEquiv.mk_coe' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) (f : N -> M) (h₁ : Function.LeftInverse.{succ u2, succ u1} N M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) f) (h₂ : Function.RightInverse.{succ u2, succ u1} N M (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) f) (h₃ : forall (x : N) (y : N), Eq.{succ u1} M (f (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N _inst_2) x y)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M _inst_1) (f x) (f y))), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} N M _inst_2 _inst_1) (MulEquiv.mk.{u2, u1} N M _inst_2 _inst_1 f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (e : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) e) h₁ h₂ h₃) (MulEquiv.symm.{u1, u2} M N _inst_1 _inst_2 e)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] (e : MulEquiv.{u2, u1} M N _inst_1 _inst_2) (f : N -> M) (h₁ : Function.LeftInverse.{succ u1, succ u2} N M (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (e : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) e) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) f) (h₂ : Function.RightInverse.{succ u1, succ u2} N M (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (e : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) e) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) f) (h₃ : forall (x : N) (y : N), Eq.{succ u2} M (Equiv.toFun.{succ u1, succ u2} N M (Equiv.mk.{succ u1, succ u2} N M f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) h₁ h₂) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N _inst_2) x y)) (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M _inst_1) (Equiv.toFun.{succ u1, succ u2} N M (Equiv.mk.{succ u1, succ u2} N M f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) h₁ h₂) x) (Equiv.toFun.{succ u1, succ u2} N M (Equiv.mk.{succ u1, succ u2} N M f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) h₁ h₂) y))), Eq.{max (succ u2) (succ u1)} (MulEquiv.{u1, u2} N M _inst_2 _inst_1) (MulEquiv.mk.{u1, u2} N M _inst_2 _inst_1 (Equiv.mk.{succ u1, succ u2} N M f (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (a : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) e) h₁ h₂) h₃) (MulEquiv.symm.{u2, u1} M N _inst_1 _inst_2 e)
Case conversion may be inaccurate. Consider using '#align mul_equiv.mk_coe' MulEquiv.mk_coe'ₓ'. -/
@[simp, to_additive]
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk f (⇑e) h₁ h₂ h₃ : N ≃* M) = e.symm :=
  symm_bijective.Injective <| ext fun x => rfl
#align mul_equiv.mk_coe' MulEquiv.mk_coe'
#align add_equiv.mk_coe' AddEquiv.mk_coe'

/- warning: mul_equiv.congr_arg -> MulEquiv.congr_arg is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2} {x : M} {x' : M}, (Eq.{succ u1} M x x') -> (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x'))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2} {x : M} {x' : M}, (Eq.{succ u2} M x x') -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x'))
Case conversion may be inaccurate. Consider using '#align mul_equiv.congr_arg MulEquiv.congr_argₓ'. -/
@[to_additive]
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  FunLike.congr_arg f
#align mul_equiv.congr_arg MulEquiv.congr_arg
#align add_equiv.congr_arg AddEquiv.congr_arg

/- warning: mul_equiv.congr_fun -> MulEquiv.congr_fun is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Mul.{u1} M] [_inst_2 : Mul.{u2} N] {f : MulEquiv.{u1, u2} M N _inst_1 _inst_2} {g : MulEquiv.{u1, u2} M N _inst_1 _inst_2}, (Eq.{max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N _inst_1 _inst_2) (fun (_x : MulEquiv.{u1, u2} M N _inst_1 _inst_2) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N _inst_1 _inst_2) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Mul.{u2} M] [_inst_2 : Mul.{u1} N] {f : MulEquiv.{u2, u1} M N _inst_1 _inst_2} {g : MulEquiv.{u2, u1} M N _inst_1 _inst_2}, (Eq.{max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) f g) -> (forall (x : M), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N _inst_1 _inst_2) M N _inst_1 _inst_2 (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N _inst_1 _inst_2)))) g x))
Case conversion may be inaccurate. Consider using '#align mul_equiv.congr_fun MulEquiv.congr_funₓ'. -/
@[to_additive]
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  FunLike.congr_fun h x
#align mul_equiv.congr_fun MulEquiv.congr_fun
#align add_equiv.congr_fun AddEquiv.congr_fun

#print MulEquiv.mulEquivOfUnique /-
/-- The `mul_equiv` between two monoids with a unique element. -/
@[to_additive "The `add_equiv` between two add_monoids with a unique element."]
def mulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.equivOfUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }
#align mul_equiv.mul_equiv_of_unique MulEquiv.mulEquivOfUnique
#align add_equiv.add_equiv_of_unique AddEquiv.addEquivOfUnique
-/

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive
      "There is a unique additive monoid homomorphism between two additive monoids with\na unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N)
    where
  default := mulEquivOfUnique
  uniq _ := ext fun x => Subsingleton.elim _ _

/-!
## Monoids
-/


/- warning: mul_equiv.map_one -> MulEquiv.map_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)), Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) h (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_5))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_6))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6))))) h (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5)))) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5)))) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5)))) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5)))) _inst_6)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_one MulEquiv.map_oneₓ'. -/
/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
      "An additive isomorphism of additive monoids sends `0` to `0`\n(and is hence an additive monoid isomorphism)."]
protected theorem map_one {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : h 1 = 1 :=
  map_one h
#align mul_equiv.map_one MulEquiv.map_one
#align add_equiv.map_zero AddEquiv.map_zero

/- warning: mul_equiv.map_eq_one_iff -> MulEquiv.map_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) {x : M}, Iff (Eq.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) h x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_6))))) (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_5)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) {x : M}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6))))) h x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) _inst_6)))) (Eq.{succ u2} M x (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5))))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_eq_one_iff MulEquiv.map_eq_one_iffₓ'. -/
@[to_additive]
protected theorem map_eq_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} :
    h x = 1 ↔ x = 1 :=
  MulEquivClass.map_eq_one_iff h
#align mul_equiv.map_eq_one_iff MulEquiv.map_eq_one_iff
#align add_equiv.map_eq_zero_iff AddEquiv.map_eq_zero_iff

/- warning: mul_equiv.map_ne_one_iff -> MulEquiv.map_ne_one_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] (h : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) {x : M}, Iff (Ne.{succ u2} N (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) h x) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N _inst_6))))) (Ne.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_5)))))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N] (h : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) {x : M}, Iff (Ne.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6))))) h x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) 1 (One.toOfNat1.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) (MulOneClass.toOne.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) x) _inst_6)))) (Ne.{succ u2} M x (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (MulOneClass.toOne.{u2} M _inst_5))))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_ne_one_iff MulEquiv.map_ne_one_iffₓ'. -/
@[to_additive]
theorem map_ne_one_iff {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) {x : M} :
    h x ≠ 1 ↔ x ≠ 1 :=
  MulEquivClass.map_ne_one_iff h
#align mul_equiv.map_ne_one_iff MulEquiv.map_ne_one_iff
#align add_equiv.map_ne_zero_iff AddEquiv.map_ne_zero_iff

#print MulEquiv.ofBijective /-
/-- A bijective `semigroup` homomorphism is an isomorphism -/
@[to_additive "A bijective `add_semigroup` homomorphism is an isomorphism", simps apply]
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [MulHomClass F M N] (f : F)
    (hf : Function.Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }
#align mul_equiv.of_bijective MulEquiv.ofBijective
#align add_equiv.of_bijective AddEquiv.ofBijective
-/

/- warning: mul_equiv.of_bijective_apply_symm_apply -> MulEquiv.ofBijective_apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] {n : N} (f : MonoidHom.{u1, u2} M N _inst_5 _inst_6) (hf : Function.Bijective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (fun (_x : MonoidHom.{u1, u2} M N _inst_5 _inst_6) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_5 _inst_6) f)), Eq.{succ u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (fun (_x : MonoidHom.{u1, u2} M N _inst_5 _inst_6) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_5 _inst_6) f (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} N M) (fun (_x : Equiv.{succ u2, succ u1} N M) => N -> M) (Equiv.hasCoeToFun.{succ u2, succ u1} N M) (Equiv.symm.{succ u1, succ u2} M N (Equiv.ofBijective.{succ u1, succ u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (fun (_x : MonoidHom.{u1, u2} M N _inst_5 _inst_6) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_5 _inst_6) f) hf)) n)) n
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N] {n : N} (f : MonoidHom.{u2, u1} M N _inst_5 _inst_6) (hf : Function.Bijective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N _inst_5 _inst_6 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_5 _inst_6))) f)), Eq.{succ u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} N M) N (fun (a : N) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : N) => M) a) (Equiv.instFunLikeEquiv.{succ u1, succ u2} N M) (Equiv.symm.{succ u2, succ u1} M N (Equiv.ofBijective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M (fun (a : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) a) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N _inst_5 _inst_6 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_5 _inst_6))) f) hf)) n)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N _inst_5 _inst_6 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_5 _inst_6))) f (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} N M) N (fun (_x : N) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : N) => M) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} N M) (Equiv.symm.{succ u2, succ u1} M N (Equiv.ofBijective.{succ u2, succ u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N _inst_5 _inst_6 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_5 _inst_6))) f) hf)) n)) n
Case conversion may be inaccurate. Consider using '#align mul_equiv.of_bijective_apply_symm_apply MulEquiv.ofBijective_apply_symm_applyₓ'. -/
@[simp]
theorem ofBijective_apply_symm_apply {M N} [MulOneClass M] [MulOneClass N] {n : N} (f : M →* N)
    (hf : Function.Bijective f) : f ((Equiv.ofBijective f hf).symm n) = n :=
  (MulEquiv.ofBijective f hf).apply_symm_apply n
#align mul_equiv.of_bijective_apply_symm_apply MulEquiv.ofBijective_apply_symm_apply

/- warning: mul_equiv.to_monoid_hom -> MulEquiv.toMonoidHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N], (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) -> (MonoidHom.{u1, u2} M N _inst_5 _inst_6)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N], (MulEquiv.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6)) -> (MonoidHom.{u1, u2} M N _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_monoid_hom MulEquiv.toMonoidHomₓ'. -/
/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive
      "Extract the forward direction of an additive equivalence\nas an addition-preserving function."]
def toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }
#align mul_equiv.to_monoid_hom MulEquiv.toMonoidHom
#align add_equiv.to_add_monoid_hom AddEquiv.toAddMonoidHom

/- warning: mul_equiv.coe_to_monoid_hom -> MulEquiv.coe_toMonoidHom is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] (e : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)), Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (fun (_x : MonoidHom.{u1, u2} M N _inst_5 _inst_6) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_5 _inst_6) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_5 _inst_6 e)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (fun (_x : MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) => M -> N) (MulEquiv.hasCoeToFun.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) e)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N] (e : MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_5 _inst_6) M N _inst_5 _inst_6 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_5 _inst_6))) (MulEquiv.toMonoidHom.{u2, u1} M N _inst_5 _inst_6 e)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => N) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6))))) e)
Case conversion may be inaccurate. Consider using '#align mul_equiv.coe_to_monoid_hom MulEquiv.coe_toMonoidHomₓ'. -/
@[simp, to_additive]
theorem coe_toMonoidHom {M N} [MulOneClass M] [MulOneClass N] (e : M ≃* N) : ⇑e.toMonoidHom = e :=
  rfl
#align mul_equiv.coe_to_monoid_hom MulEquiv.coe_toMonoidHom
#align add_equiv.coe_to_add_monoid_hom AddEquiv.coe_toAddMonoidHom

/- warning: mul_equiv.to_monoid_hom_injective -> MulEquiv.toMonoidHom_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N], Function.Injective.{max (succ u1) (succ u2), max (succ u2) (succ u1)} (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) (MonoidHom.{u1, u2} M N _inst_5 _inst_6) (MulEquiv.toMonoidHom.{u1, u2} M N _inst_5 _inst_6)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_5 : MulOneClass.{u2} M] [_inst_6 : MulOneClass.{u1} N], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (MulEquiv.{u2, u1} M N (MulOneClass.toMul.{u2} M _inst_5) (MulOneClass.toMul.{u1} N _inst_6)) (MonoidHom.{u2, u1} M N _inst_5 _inst_6) (MulEquiv.toMonoidHom.{u2, u1} M N _inst_5 _inst_6)
Case conversion may be inaccurate. Consider using '#align mul_equiv.to_monoid_hom_injective MulEquiv.toMonoidHom_injectiveₓ'. -/
@[to_additive]
theorem toMonoidHom_injective {M N} [MulOneClass M] [MulOneClass N] :
    Function.Injective (toMonoidHom : M ≃* N → M →* N) := fun f g h =>
  MulEquiv.ext (MonoidHom.ext_iff.1 h)
#align mul_equiv.to_monoid_hom_injective MulEquiv.toMonoidHom_injective
#align add_equiv.to_add_monoid_hom_injective AddEquiv.toAddMonoidHom_injective

#print MulEquiv.arrowCongr /-
/-- A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive
      "An additive analogue of `equiv.arrow_congr`,\nwhere the equivalence between the targets is additive.",
  simps apply]
def arrowCongr {M N P Q : Type _} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q)
    where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by
    ext
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    simp
#align mul_equiv.arrow_congr MulEquiv.arrowCongr
#align add_equiv.arrow_congr AddEquiv.arrowCongr
-/

/- warning: mul_equiv.monoid_hom_congr -> MulEquiv.monoidHomCongr is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] [_inst_7 : CommMonoid.{u3} P] [_inst_8 : CommMonoid.{u4} Q], (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_5) (MulOneClass.toHasMul.{u2} N _inst_6)) -> (MulEquiv.{u3, u4} P Q (MulOneClass.toHasMul.{u3} P (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_7))) (MulOneClass.toHasMul.{u4} Q (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_8)))) -> (MulEquiv.{max u3 u1, max u4 u2} (MonoidHom.{u1, u3} M P _inst_5 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_7))) (MonoidHom.{u2, u4} N Q _inst_6 (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_8))) (MonoidHom.hasMul.{u1, u3} M P _inst_5 _inst_7) (MonoidHom.hasMul.{u2, u4} N Q _inst_6 _inst_8))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} {P : Type.{u3}} {Q : Type.{u4}} [_inst_5 : MulOneClass.{u1} M] [_inst_6 : MulOneClass.{u2} N] [_inst_7 : CommMonoid.{u3} P] [_inst_8 : CommMonoid.{u4} Q], (MulEquiv.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_5) (MulOneClass.toMul.{u2} N _inst_6)) -> (MulEquiv.{u3, u4} P Q (MulOneClass.toMul.{u3} P (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_7))) (MulOneClass.toMul.{u4} Q (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_8)))) -> (MulEquiv.{max u3 u1, max u4 u2} (MonoidHom.{u1, u3} M P _inst_5 (Monoid.toMulOneClass.{u3} P (CommMonoid.toMonoid.{u3} P _inst_7))) (MonoidHom.{u2, u4} N Q _inst_6 (Monoid.toMulOneClass.{u4} Q (CommMonoid.toMonoid.{u4} Q _inst_8))) (MonoidHom.mul.{u1, u3} M P _inst_5 _inst_7) (MonoidHom.mul.{u2, u4} N Q _inst_6 _inst_8))
Case conversion may be inaccurate. Consider using '#align mul_equiv.monoid_hom_congr MulEquiv.monoidHomCongrₓ'. -/
/-- A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[to_additive
      "An additive analogue of `equiv.arrow_congr`,\nfor additive maps from an additive monoid to a commutative additive monoid.",
  simps apply]
def monoidHomCongr {M N P Q} [MulOneClass M] [MulOneClass N] [CommMonoid P] [CommMonoid Q]
    (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q)
    where
  toFun h := g.toMonoidHom.comp (h.comp f.symm.toMonoidHom)
  invFun k := g.symm.toMonoidHom.comp (k.comp f.toMonoidHom)
  left_inv h := by
    ext
    simp
  right_inv k := by
    ext
    simp
  map_mul' h k := by
    ext
    simp
#align mul_equiv.monoid_hom_congr MulEquiv.monoidHomCongr
#align add_equiv.add_monoid_hom_congr AddEquiv.addMonoidHomCongr

#print MulEquiv.piCongrRight /-
/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `mul_equiv` version of `equiv.Pi_congr_right`, and the dependent version of
`mul_equiv.arrow_congr`.
-/
@[to_additive AddEquiv.piCongrRight
      "A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`\ngenerates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.\n\nThis is the `add_equiv` version of `equiv.Pi_congr_right`, and the dependent version of\n`add_equiv.arrow_congr`.",
  simps apply]
def piCongrRight {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  {
    Equiv.piCongrRight fun j =>
      (es j).toEquiv with
    toFun := fun x j => es j (x j)
    invFun := fun x j => (es j).symm (x j)
    map_mul' := fun x y => funext fun j => (es j).map_mul (x j) (y j) }
#align mul_equiv.Pi_congr_right MulEquiv.piCongrRight
#align add_equiv.Pi_congr_right AddEquiv.piCongrRight
-/

/- warning: mul_equiv.Pi_congr_right_refl -> MulEquiv.piCongrRight_refl is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {Ms : η -> Type.{u2}} [_inst_5 : forall (j : η), Mul.{u2} (Ms j)], Eq.{succ (max u1 u2)} (MulEquiv.{max u1 u2, max u1 u2} (forall (j : η), Ms j) (forall (j : η), Ms j) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i))) (MulEquiv.piCongrRight.{u1, u2, u2} η (fun (j : η) => Ms j) (fun (j : η) => Ms j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_5 j) (fun (j : η) => MulEquiv.refl.{u2} (Ms j) (_inst_5 j))) (MulEquiv.refl.{max u1 u2} (forall (j : η), Ms j) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)))
but is expected to have type
  forall {η : Type.{u2}} {Ms : η -> Type.{u1}} [_inst_5 : forall (j : η), Mul.{u1} (Ms j)], Eq.{max (succ u2) (succ u1)} (MulEquiv.{max u2 u1, max u2 u1} (forall (j : η), Ms j) (forall (j : η), Ms j) (Pi.instMul.{u2, u1} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u2, u1} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i))) (MulEquiv.piCongrRight.{u2, u1, u1} η (fun (j : η) => Ms j) (fun (j : η) => Ms j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_5 j) (fun (j : η) => MulEquiv.refl.{u1} (Ms j) (_inst_5 j))) (MulEquiv.refl.{max u2 u1} (forall (j : η), Ms j) (Pi.instMul.{u2, u1} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.Pi_congr_right_refl MulEquiv.piCongrRight_reflₓ'. -/
@[simp, to_additive]
theorem piCongrRight_refl {η : Type _} {Ms : η → Type _} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ :=
  rfl
#align mul_equiv.Pi_congr_right_refl MulEquiv.piCongrRight_refl
#align add_equiv.Pi_congr_right_refl AddEquiv.piCongrRight_refl

/- warning: mul_equiv.Pi_congr_right_symm -> MulEquiv.piCongrRight_symm is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {Ms : η -> Type.{u2}} {Ns : η -> Type.{u3}} [_inst_5 : forall (j : η), Mul.{u2} (Ms j)] [_inst_6 : forall (j : η), Mul.{u3} (Ns j)] (es : forall (j : η), MulEquiv.{u2, u3} (Ms j) (Ns j) (_inst_5 j) (_inst_6 j)), Eq.{max (succ (max u1 u3)) (succ (max u1 u2))} (MulEquiv.{max u1 u3, max u1 u2} (forall (j : η), Ns j) (forall (j : η), Ms j) (Pi.instMul.{u1, u3} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i))) (MulEquiv.symm.{max u1 u2, max u1 u3} (forall (j : η), Ms j) (forall (j : η), Ns j) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u1, u3} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (MulEquiv.piCongrRight.{u1, u2, u3} η (fun (j : η) => Ms j) (fun (j : η) => Ns j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_6 j) es)) (MulEquiv.piCongrRight.{u1, u3, u2} η (fun (j : η) => Ns j) (fun (j : η) => Ms j) (fun (i : η) => _inst_6 i) (fun (i : η) => _inst_5 i) (fun (i : η) => MulEquiv.symm.{u2, u3} (Ms i) (Ns i) (_inst_5 i) (_inst_6 i) (es i)))
but is expected to have type
  forall {η : Type.{u3}} {Ms : η -> Type.{u2}} {Ns : η -> Type.{u1}} [_inst_5 : forall (j : η), Mul.{u2} (Ms j)] [_inst_6 : forall (j : η), Mul.{u1} (Ns j)] (es : forall (j : η), MulEquiv.{u2, u1} (Ms j) (Ns j) (_inst_5 j) (_inst_6 j)), Eq.{max (max (succ u3) (succ u2)) (succ u1)} (MulEquiv.{max u3 u1, max u3 u2} (forall (j : η), Ns j) (forall (j : η), Ms j) (Pi.instMul.{u3, u1} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (Pi.instMul.{u3, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i))) (MulEquiv.symm.{max u3 u2, max u3 u1} (forall (j : η), Ms j) (forall (j : η), Ns j) (Pi.instMul.{u3, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u3, u1} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (MulEquiv.piCongrRight.{u3, u2, u1} η (fun (j : η) => Ms j) (fun (j : η) => Ns j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_6 j) es)) (MulEquiv.piCongrRight.{u3, u1, u2} η (fun (j : η) => Ns j) (fun (j : η) => Ms j) (fun (i : η) => _inst_6 i) (fun (i : η) => _inst_5 i) (fun (i : η) => MulEquiv.symm.{u2, u1} (Ms i) (Ns i) (_inst_5 i) (_inst_6 i) (es i)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.Pi_congr_right_symm MulEquiv.piCongrRight_symmₓ'. -/
@[simp, to_additive]
theorem piCongrRight_symm {η : Type _} {Ms Ns : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm :=
  rfl
#align mul_equiv.Pi_congr_right_symm MulEquiv.piCongrRight_symm
#align add_equiv.Pi_congr_right_symm AddEquiv.piCongrRight_symm

/- warning: mul_equiv.Pi_congr_right_trans -> MulEquiv.piCongrRight_trans is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {Ms : η -> Type.{u2}} {Ns : η -> Type.{u3}} {Ps : η -> Type.{u4}} [_inst_5 : forall (j : η), Mul.{u2} (Ms j)] [_inst_6 : forall (j : η), Mul.{u3} (Ns j)] [_inst_7 : forall (j : η), Mul.{u4} (Ps j)] (es : forall (j : η), MulEquiv.{u2, u3} (Ms j) (Ns j) (_inst_5 j) (_inst_6 j)) (fs : forall (j : η), MulEquiv.{u3, u4} (Ns j) (Ps j) (_inst_6 j) (_inst_7 j)), Eq.{max (succ (max u1 u2)) (succ (max u1 u4))} (MulEquiv.{max u1 u2, max u1 u4} (forall (j : η), Ms j) (forall (j : η), Ps j) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u1, u4} η (fun (j : η) => Ps j) (fun (i : η) => _inst_7 i))) (MulEquiv.trans.{max u1 u2, max u1 u3, max u1 u4} (forall (j : η), Ms j) (forall (j : η), Ns j) (forall (j : η), Ps j) (Pi.instMul.{u1, u2} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u1, u3} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (Pi.instMul.{u1, u4} η (fun (j : η) => Ps j) (fun (i : η) => _inst_7 i)) (MulEquiv.piCongrRight.{u1, u2, u3} η (fun (j : η) => Ms j) (fun (j : η) => Ns j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_6 j) es) (MulEquiv.piCongrRight.{u1, u3, u4} η (fun (j : η) => Ns j) (fun (j : η) => Ps j) (fun (i : η) => _inst_6 i) (fun (j : η) => _inst_7 j) fs)) (MulEquiv.piCongrRight.{u1, u2, u4} η (fun (j : η) => Ms j) (fun (j : η) => Ps j) (fun (i : η) => _inst_5 i) (fun (i : η) => _inst_7 i) (fun (i : η) => MulEquiv.trans.{u2, u3, u4} (Ms i) (Ns i) (Ps i) (_inst_5 i) (_inst_6 i) (_inst_7 i) (es i) (fs i)))
but is expected to have type
  forall {η : Type.{u4}} {Ms : η -> Type.{u3}} {Ns : η -> Type.{u2}} {Ps : η -> Type.{u1}} [_inst_5 : forall (j : η), Mul.{u3} (Ms j)] [_inst_6 : forall (j : η), Mul.{u2} (Ns j)] [_inst_7 : forall (j : η), Mul.{u1} (Ps j)] (es : forall (j : η), MulEquiv.{u3, u2} (Ms j) (Ns j) (_inst_5 j) (_inst_6 j)) (fs : forall (j : η), MulEquiv.{u2, u1} (Ns j) (Ps j) (_inst_6 j) (_inst_7 j)), Eq.{max (max (succ u4) (succ u3)) (succ u1)} (MulEquiv.{max u4 u3, max u4 u1} (forall (j : η), Ms j) (forall (j : η), Ps j) (Pi.instMul.{u4, u3} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u4, u1} η (fun (j : η) => Ps j) (fun (i : η) => _inst_7 i))) (MulEquiv.trans.{max u4 u3, max u4 u2, max u4 u1} (forall (j : η), Ms j) (forall (j : η), Ns j) (forall (j : η), Ps j) (Pi.instMul.{u4, u3} η (fun (j : η) => Ms j) (fun (i : η) => _inst_5 i)) (Pi.instMul.{u4, u2} η (fun (j : η) => Ns j) (fun (i : η) => _inst_6 i)) (Pi.instMul.{u4, u1} η (fun (j : η) => Ps j) (fun (i : η) => _inst_7 i)) (MulEquiv.piCongrRight.{u4, u3, u2} η (fun (j : η) => Ms j) (fun (j : η) => Ns j) (fun (j : η) => _inst_5 j) (fun (j : η) => _inst_6 j) es) (MulEquiv.piCongrRight.{u4, u2, u1} η (fun (j : η) => Ns j) (fun (j : η) => Ps j) (fun (i : η) => _inst_6 i) (fun (j : η) => _inst_7 j) fs)) (MulEquiv.piCongrRight.{u4, u3, u1} η (fun (j : η) => Ms j) (fun (j : η) => Ps j) (fun (i : η) => _inst_5 i) (fun (i : η) => _inst_7 i) (fun (i : η) => MulEquiv.trans.{u3, u2, u1} (Ms i) (Ns i) (Ps i) (_inst_5 i) (_inst_6 i) (_inst_7 i) (es i) (fs i)))
Case conversion may be inaccurate. Consider using '#align mul_equiv.Pi_congr_right_trans MulEquiv.piCongrRight_transₓ'. -/
@[simp, to_additive]
theorem piCongrRight_trans {η : Type _} {Ms Ns Ps : η → Type _} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    [∀ j, Mul (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) :=
  rfl
#align mul_equiv.Pi_congr_right_trans MulEquiv.piCongrRight_trans
#align add_equiv.Pi_congr_right_trans AddEquiv.piCongrRight_trans

#print MulEquiv.piSubsingleton /-
/-- A family indexed by a nonempty subsingleton type is equivalent to the element at the single
index. -/
@[to_additive AddEquiv.piSubsingleton
      "A family indexed by a nonempty subsingleton type is\nequivalent to the element at the single index.",
  simps]
def piSubsingleton {ι : Type _} (M : ι → Type _) [∀ j, Mul (M j)] [Subsingleton ι] (i : ι) :
    (∀ j, M j) ≃* M i :=
  { Equiv.piSubsingleton M i with map_mul' := fun f1 f2 => Pi.mul_apply _ _ _ }
#align mul_equiv.Pi_subsingleton MulEquiv.piSubsingleton
#align add_equiv.Pi_subsingleton AddEquiv.piSubsingleton
-/

/-!
# Groups
-/


/- warning: mul_equiv.map_inv -> MulEquiv.map_inv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_5 : Group.{u1} G] [_inst_6 : DivisionMonoid.{u2} H] (h : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (x : G), Eq.{succ u2} H (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) h (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)) x)) (Inv.inv.{u2} H (DivInvMonoid.toHasInv.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) h x))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_5 : Group.{u2} G] [_inst_6 : DivisionMonoid.{u1} H] (h : MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) (x : G), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) (Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_5)))) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))))))) h (Inv.inv.{u2} G (InvOneClass.toInv.{u2} G (DivInvOneMonoid.toInvOneClass.{u2} G (DivisionMonoid.toDivInvOneMonoid.{u2} G (Group.toDivisionMonoid.{u2} G _inst_5)))) x)) (Inv.inv.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (InvOneClass.toInv.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (DivInvOneMonoid.toInvOneClass.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (DivisionMonoid.toDivInvOneMonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) _inst_6))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))))))) h x))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_inv MulEquiv.map_invₓ'. -/
/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive "An additive equivalence of additive groups preserves negation."]
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) : h x⁻¹ = (h x)⁻¹ :=
  map_inv h x
#align mul_equiv.map_inv MulEquiv.map_inv
#align add_equiv.map_neg AddEquiv.map_neg

/- warning: mul_equiv.map_div -> MulEquiv.map_div is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_5 : Group.{u1} G] [_inst_6 : DivisionMonoid.{u2} H] (h : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (x : G) (y : G), Eq.{succ u2} H (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) h (HDiv.hDiv.{u1, u1, u1} G G G (instHDiv.{u1} G (DivInvMonoid.toHasDiv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5))) x y)) (HDiv.hDiv.{u2, u2, u2} H H H (instHDiv.{u2} H (DivInvMonoid.toHasDiv.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) h x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) (fun (_x : MulEquiv.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) => G -> H) (MulEquiv.hasCoeToFun.{u1, u2} G H (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_5)))) (MulOneClass.toHasMul.{u2} H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (DivisionMonoid.toDivInvMonoid.{u2} H _inst_6))))) h y))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_5 : Group.{u2} G] [_inst_6 : DivisionMonoid.{u1} H] (h : MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) (x : G) (y : G), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5))) x y)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))))))) h (HDiv.hDiv.{u2, u2, u2} G G G (instHDiv.{u2} G (DivInvMonoid.toDiv.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5))) x y)) (HDiv.hDiv.{u1, u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) y) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (instHDiv.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (DivInvMonoid.toDiv.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) (DivisionMonoid.toDivInvMonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) x) _inst_6))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))))))) h x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G (fun (_x : G) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : G) => H) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulEquivClass.toEquivLike.{max u2 u1, u2, u1} (MulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6))))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))) (MulEquiv.instMulEquivClassMulEquiv.{u2, u1} G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_5)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (DivisionMonoid.toDivInvMonoid.{u1} H _inst_6)))))))) h y))
Case conversion may be inaccurate. Consider using '#align mul_equiv.map_div MulEquiv.map_divₓ'. -/
/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive "An additive equivalence of additive groups preserves subtractions."]
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  map_div h x y
#align mul_equiv.map_div MulEquiv.map_div
#align add_equiv.map_sub AddEquiv.map_sub

end MulEquiv

#print MulHom.toMulEquiv /-
/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive
      "Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and\n`f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nhomomorphisms.",
  simps (config := { fullyApplied := false })]
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N
    where
  toFun := f
  invFun := g
  left_inv := MulHom.congr_fun h₁
  right_inv := MulHom.congr_fun h₂
  map_mul' := f.map_mul
#align mul_hom.to_mul_equiv MulHom.toMulEquiv
#align add_hom.to_add_equiv AddHom.toAddEquiv
-/

/- warning: monoid_hom.to_mul_equiv -> MonoidHom.toMulEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u2, u1} N M _inst_2 _inst_1), (Eq.{succ u1} (MonoidHom.{u1, u1} M M _inst_1 _inst_1) (MonoidHom.comp.{u1, u2, u1} M N M _inst_1 _inst_2 _inst_1 g f) (MonoidHom.id.{u1} M _inst_1)) -> (Eq.{succ u2} (MonoidHom.{u2, u2} N N _inst_2 _inst_2) (MonoidHom.comp.{u2, u1, u2} N M N _inst_2 _inst_1 _inst_2 f g) (MonoidHom.id.{u2} N _inst_2)) -> (MulEquiv.{u1, u2} M N (MulOneClass.toHasMul.{u1} M _inst_1) (MulOneClass.toHasMul.{u2} N _inst_2))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_2 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_2) (g : MonoidHom.{u2, u1} N M _inst_2 _inst_1), (Eq.{succ u1} (MonoidHom.{u1, u1} M M _inst_1 _inst_1) (MonoidHom.comp.{u1, u2, u1} M N M _inst_1 _inst_2 _inst_1 g f) (MonoidHom.id.{u1} M _inst_1)) -> (Eq.{succ u2} (MonoidHom.{u2, u2} N N _inst_2 _inst_2) (MonoidHom.comp.{u2, u1, u2} N M N _inst_2 _inst_1 _inst_2 f g) (MonoidHom.id.{u2} N _inst_2)) -> (MulEquiv.{u1, u2} M N (MulOneClass.toMul.{u1} M _inst_1) (MulOneClass.toMul.{u2} N _inst_2))
Case conversion may be inaccurate. Consider using '#align monoid_hom.to_mul_equiv MonoidHom.toMulEquivₓ'. -/
/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive
      "Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`\nand `f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This\nconstructor is useful if the underlying type(s) have specialized `ext` lemmas for additive\nmonoid homomorphisms.",
  simps (config := { fullyApplied := false })]
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N
    where
  toFun := f
  invFun := g
  left_inv := MonoidHom.congr_fun h₁
  right_inv := MonoidHom.congr_fun h₂
  map_mul' := f.map_mul
#align monoid_hom.to_mul_equiv MonoidHom.toMulEquiv
#align add_monoid_hom.to_add_equiv AddMonoidHom.toAddEquiv

namespace Equiv

section InvolutiveNeg

variable (G) [InvolutiveInv G]

#print Equiv.inv /-
/-- Inversion on a `group` or `group_with_zero` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
protected def inv : Perm G :=
  inv_involutive.toPerm _
#align equiv.inv Equiv.inv
#align equiv.neg Equiv.neg
-/

variable {G}

#print Equiv.inv_symm /-
@[simp, to_additive]
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G :=
  rfl
#align equiv.inv_symm Equiv.inv_symm
#align equiv.neg_symm Equiv.neg_symm
-/

end InvolutiveNeg

end Equiv

