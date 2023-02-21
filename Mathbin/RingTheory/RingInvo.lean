/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau

! This file was ported from Lean 3 source module ring_theory.ring_invo
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Ring.Opposite

/-!
# Ring involutions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/


variable (R : Type _)

#print RingInvo /-
/-- A ring involution -/
structure RingInvo [Semiring R] extends R ≃+* Rᵐᵒᵖ where
  involution' : ∀ x, (to_fun (to_fun x).unop).unop = x
#align ring_invo RingInvo
-/

/-- The equivalence of rings underlying a ring involution. -/
add_decl_doc RingInvo.toRingEquiv

#print RingInvoClass /-
/-- `ring_invo_class F R S` states that `F` is a type of ring involutions.
You should extend this class when you extend `ring_invo`. -/
class RingInvoClass (F : Type _) (R : outParam (Type _)) [Semiring R] extends
  RingEquivClass F R Rᵐᵒᵖ where
  involution : ∀ (f : F) (x), (f (f x).unop).unop = x
#align ring_invo_class RingInvoClass
-/

namespace RingInvo

variable {R} [Semiring R]

instance (R : Type _) [Semiring R] : RingInvoClass (RingInvo R) R
    where
  coe := toFun
  inv := invFun
  coe_injective' e f h₁ h₂ := by
    cases e
    cases f
    congr
  map_add := map_add'
  map_mul := map_mul'
  left_inv := left_inv
  right_inv := right_inv
  involution := involution'

/- warning: ring_invo.mk' -> RingInvo.mk' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))), (forall (r : R), Eq.{succ u1} R (MulOpposite.unop.{u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) => R -> (MulOpposite.{u1} R)) (RingHom.hasCoeToFun.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f (MulOpposite.unop.{u1} R (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (fun (_x : RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) => R -> (MulOpposite.{u1} R)) (RingHom.hasCoeToFun.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) f r)))) r) -> (RingInvo.{u1} R _inst_1)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))), (forall (r : R), Eq.{succ u1} R (MulOpposite.unop.{u1} R (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => MulOpposite.{u1} R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (MulOpposite.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (MulOpposite.{u1} R) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (MulOpposite.{u1} R) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) f (MulOpposite.unop.{u1} R (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : R) => MulOpposite.{u1} R) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u1} (MulOpposite.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (MulOpposite.{u1} R) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} (MulOpposite.{u1} R) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (RingHom.instRingHomClassRingHom.{u1, u1} R (MulOpposite.{u1} R) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))))) f r)))) r) -> (RingInvo.{u1} R _inst_1)
Case conversion may be inaccurate. Consider using '#align ring_invo.mk' RingInvo.mk'ₓ'. -/
/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) : RingInvo R :=
  { f with
    invFun := fun r => (f r.unop).unop
    left_inv := fun r => involution r
    right_inv := fun r => MulOpposite.unop_injective <| involution _
    involution' := involution }
#align ring_invo.mk' RingInvo.mk'

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : CoeFun (RingInvo R) fun _ => R → Rᵐᵒᵖ :=
  ⟨fun f => f.toRingEquiv.toFun⟩

/- warning: ring_invo.to_fun_eq_coe clashes with [anonymous] -> [anonymous]
warning: ring_invo.to_fun_eq_coe -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u_1}} [_inst_1 : Semiring.{u_1} R] (f : RingInvo.{u_1} R _inst_1), Eq.{succ u_1} (R -> (MulOpposite.{u_1} R)) (RingInvo.toFun.{u_1} R _inst_1 f) (coeFn.{succ u_1, succ u_1} (RingInvo.{u_1} R _inst_1) (fun (_x : RingInvo.{u_1} R _inst_1) => R -> (MulOpposite.{u_1} R)) (RingInvo.hasCoeToFun.{u_1} R _inst_1) f)
but is expected to have type
  forall {R : Type.{u}} {_inst_1 : Type.{v}}, (Nat -> R -> _inst_1) -> Nat -> (List.{u} R) -> (List.{v} _inst_1)
Case conversion may be inaccurate. Consider using '#align ring_invo.to_fun_eq_coe [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (f : RingInvo R) : f.toFun = f :=
  rfl
#align ring_invo.to_fun_eq_coe [anonymous]

/- warning: ring_invo.involution -> RingInvo.involution is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingInvo.{u1} R _inst_1) (x : R), Eq.{succ u1} R (MulOpposite.unop.{u1} R (coeFn.{succ u1, succ u1} (RingInvo.{u1} R _inst_1) (fun (_x : RingInvo.{u1} R _inst_1) => R -> (MulOpposite.{u1} R)) (RingInvo.hasCoeToFun.{u1} R _inst_1) f (MulOpposite.unop.{u1} R (coeFn.{succ u1, succ u1} (RingInvo.{u1} R _inst_1) (fun (_x : RingInvo.{u1} R _inst_1) => R -> (MulOpposite.{u1} R)) (RingInvo.hasCoeToFun.{u1} R _inst_1) f x)))) x
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingInvo.{u1} R _inst_1) (x : R), Eq.{succ u1} R (MulOpposite.unop.{u1} R (FunLike.coe.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (fun (_x : R) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (MulEquivClass.toEquivLike.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (RingEquivClass.toMulEquivClass.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instAddMulOpposite.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (RingInvoClass.toRingEquivClass.{u1, u1} (RingInvo.{u1} R _inst_1) R _inst_1 (RingInvo.instRingInvoClassRingInvo.{u1} R _inst_1)))))) f (MulOpposite.unop.{u1} R (FunLike.coe.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (fun (_x : R) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (MulEquivClass.toEquivLike.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (RingEquivClass.toMulEquivClass.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instAddMulOpposite.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (RingInvoClass.toRingEquivClass.{u1, u1} (RingInvo.{u1} R _inst_1) R _inst_1 (RingInvo.instRingInvoClassRingInvo.{u1} R _inst_1)))))) f x)))) x
Case conversion may be inaccurate. Consider using '#align ring_invo.involution RingInvo.involutionₓ'. -/
@[simp]
theorem involution (f : RingInvo R) (x : R) : (f (f x).unop).unop = x :=
  f.involution' x
#align ring_invo.involution RingInvo.involution

instance hasCoeToRingEquiv : Coe (RingInvo R) (R ≃+* Rᵐᵒᵖ) :=
  ⟨RingInvo.toRingEquiv⟩
#align ring_invo.has_coe_to_ring_equiv RingInvo.hasCoeToRingEquiv

#print RingInvo.coe_ringEquiv /-
@[norm_cast]
theorem coe_ringEquiv (f : RingInvo R) (a : R) : (f : R ≃+* Rᵐᵒᵖ) a = f a :=
  rfl
#align ring_invo.coe_ring_equiv RingInvo.coe_ringEquiv
-/

/- warning: ring_invo.map_eq_zero_iff -> RingInvo.map_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingInvo.{u1} R _inst_1) {x : R}, Iff (Eq.{succ u1} (MulOpposite.{u1} R) (coeFn.{succ u1, succ u1} (RingInvo.{u1} R _inst_1) (fun (_x : RingInvo.{u1} R _inst_1) => R -> (MulOpposite.{u1} R)) (RingInvo.hasCoeToFun.{u1} R _inst_1) f x) (OfNat.ofNat.{u1} (MulOpposite.{u1} R) 0 (OfNat.mk.{u1} (MulOpposite.{u1} R) 0 (Zero.zero.{u1} (MulOpposite.{u1} R) (MulOpposite.hasZero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] (f : RingInvo.{u1} R _inst_1) {x : R}, Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) x) (FunLike.coe.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (fun (_x : R) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (MulEquivClass.toEquivLike.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (RingEquivClass.toMulEquivClass.{u1, u1, u1} (RingInvo.{u1} R _inst_1) R (MulOpposite.{u1} R) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instMulMulOpposite.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulOpposite.instAddMulOpposite.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))))) (RingInvoClass.toRingEquivClass.{u1, u1} (RingInvo.{u1} R _inst_1) R _inst_1 (RingInvo.instRingInvoClassRingInvo.{u1} R _inst_1)))))) f x) (OfNat.ofNat.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) x) 0 (Zero.toOfNat0.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : R) => MulOpposite.{u1} R) x) (MulOpposite.instZeroMulOpposite.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))) (Eq.{succ u1} R x (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)))))
Case conversion may be inaccurate. Consider using '#align ring_invo.map_eq_zero_iff RingInvo.map_eq_zero_iffₓ'. -/
@[simp]
theorem map_eq_zero_iff (f : RingInvo R) {x : R} : f x = 0 ↔ x = 0 :=
  f.toRingEquiv.map_eq_zero_iff
#align ring_invo.map_eq_zero_iff RingInvo.map_eq_zero_iff

end RingInvo

open RingInvo

section CommRing

variable [CommRing R]

#print RingInvo.id /-
/-- The identity function of a `comm_ring` is a ring involution. -/
protected def RingInvo.id : RingInvo R :=
  { RingEquiv.toOpposite R with involution' := fun r => rfl }
#align ring_invo.id RingInvo.id
-/

instance : Inhabited (RingInvo R) :=
  ⟨RingInvo.id _⟩

end CommRing

