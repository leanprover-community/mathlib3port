/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

! This file was ported from Lean 3 source module algebra.ring.opposite
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.Hom.Ring

/-!
# Ring structures on the multiplicative opposite

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe u v

variable (α : Type u)

namespace MulOpposite

instance [Distrib α] : Distrib αᵐᵒᵖ :=
  { MulOpposite.hasAdd α,
    MulOpposite.hasMul
      α with
    left_distrib := fun x y z => unop_injective <| add_mul (unop y) (unop z) (unop x)
    right_distrib := fun x y z => unop_injective <| mul_add (unop z) (unop x) (unop y) }

instance [MulZeroClass α] : MulZeroClass αᵐᵒᵖ
    where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| mul_zero <| unop x
  mul_zero x := unop_injective <| zero_mul <| unop x

instance [MulZeroOneClass α] : MulZeroOneClass αᵐᵒᵖ :=
  { MulOpposite.mulZeroClass α, MulOpposite.mulOneClass α with }

instance [SemigroupWithZero α] : SemigroupWithZero αᵐᵒᵖ :=
  { MulOpposite.semigroup α, MulOpposite.mulZeroClass α with }

instance [MonoidWithZero α] : MonoidWithZero αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.mulZeroOneClass α with }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.addCommMonoid α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with }

instance [NonUnitalSemiring α] : NonUnitalSemiring αᵐᵒᵖ :=
  { MulOpposite.semigroupWithZero α, MulOpposite.nonUnitalNonAssocSemiring α with }

instance [NonAssocSemiring α] : NonAssocSemiring αᵐᵒᵖ :=
  { MulOpposite.addMonoidWithOne α, MulOpposite.mulZeroOneClass α,
    MulOpposite.nonUnitalNonAssocSemiring α with }

instance [Semiring α] : Semiring αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.nonAssocSemiring α,
    MulOpposite.monoidWithZero α with }

instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵐᵒᵖ :=
  { MulOpposite.nonUnitalSemiring α, MulOpposite.commSemigroup α with }

instance [CommSemiring α] : CommSemiring αᵐᵒᵖ :=
  { MulOpposite.semiring α, MulOpposite.commSemigroup α with }

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.mulZeroClass α, MulOpposite.distrib α with }

instance [NonUnitalRing α] : NonUnitalRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.semigroupWithZero α, MulOpposite.distrib α with }

instance [NonAssocRing α] : NonAssocRing αᵐᵒᵖ :=
  { MulOpposite.addCommGroup α, MulOpposite.mulZeroOneClass α, MulOpposite.distrib α,
    MulOpposite.addGroupWithOne α with }

instance [Ring α] : Ring αᵐᵒᵖ :=
  { MulOpposite.monoid α, MulOpposite.nonAssocRing α with }

instance [NonUnitalCommRing α] : NonUnitalCommRing αᵐᵒᵖ :=
  { MulOpposite.nonUnitalRing α, MulOpposite.nonUnitalCommSemiring α with }

instance [CommRing α] : CommRing αᵐᵒᵖ :=
  { MulOpposite.ring α, MulOpposite.commSemiring α with }

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵐᵒᵖ
    where eq_zero_or_eq_zero_of_mul_eq_zero x y (H : op (_ * _) = op (0 : α)) :=
    Or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero <| op_injective H)
      (fun hy => Or.inr <| unop_injective <| hy) fun hx => Or.inl <| unop_injective <| hx

instance [Ring α] [IsDomain α] : IsDomain αᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance [GroupWithZero α] : GroupWithZero αᵐᵒᵖ :=
  { MulOpposite.monoidWithZero α, MulOpposite.divInvMonoid α,
    MulOpposite.nontrivial
      α with
    mul_inv_cancel := fun x hx => unop_injective <| inv_mul_cancel <| unop_injective.Ne hx
    inv_zero := unop_injective inv_zero }

end MulOpposite

namespace AddOpposite

instance [Distrib α] : Distrib αᵃᵒᵖ :=
  { AddOpposite.hasAdd α,
    @AddOpposite.hasMul α
      _ with
    left_distrib := fun x y z => unop_injective <| @mul_add α _ _ _ x z y
    right_distrib := fun x y z => unop_injective <| @add_mul α _ _ _ y x z }

instance [MulZeroClass α] : MulZeroClass αᵃᵒᵖ
    where
  zero := 0
  mul := (· * ·)
  zero_mul x := unop_injective <| zero_mul <| unop x
  mul_zero x := unop_injective <| mul_zero <| unop x

instance [MulZeroOneClass α] : MulZeroOneClass αᵃᵒᵖ :=
  { AddOpposite.mulZeroClass α, AddOpposite.mulOneClass α with }

instance [SemigroupWithZero α] : SemigroupWithZero αᵃᵒᵖ :=
  { AddOpposite.semigroup α, AddOpposite.mulZeroClass α with }

instance [MonoidWithZero α] : MonoidWithZero αᵃᵒᵖ :=
  { AddOpposite.monoid α, AddOpposite.mulZeroOneClass α with }

instance [NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.addCommMonoid α, AddOpposite.mulZeroClass α, AddOpposite.distrib α with }

instance [NonUnitalSemiring α] : NonUnitalSemiring αᵃᵒᵖ :=
  { AddOpposite.semigroupWithZero α, AddOpposite.nonUnitalNonAssocSemiring α with }

instance [NonAssocSemiring α] : NonAssocSemiring αᵃᵒᵖ :=
  { AddOpposite.mulZeroOneClass α, AddOpposite.nonUnitalNonAssocSemiring α with }

instance [Semiring α] : Semiring αᵃᵒᵖ :=
  { AddOpposite.nonUnitalSemiring α, AddOpposite.nonAssocSemiring α,
    AddOpposite.monoidWithZero α with }

instance [NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵃᵒᵖ :=
  { AddOpposite.nonUnitalSemiring α, AddOpposite.commSemigroup α with }

instance [CommSemiring α] : CommSemiring αᵃᵒᵖ :=
  { AddOpposite.semiring α, AddOpposite.commSemigroup α with }

instance [NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.mulZeroClass α, AddOpposite.distrib α with }

instance [NonUnitalRing α] : NonUnitalRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.semigroupWithZero α, AddOpposite.distrib α with }

instance [NonAssocRing α] : NonAssocRing αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.mulZeroOneClass α, AddOpposite.distrib α with }

instance [Ring α] : Ring αᵃᵒᵖ :=
  { AddOpposite.addCommGroup α, AddOpposite.monoid α, AddOpposite.semiring α with }

instance [NonUnitalCommRing α] : NonUnitalCommRing αᵃᵒᵖ :=
  { AddOpposite.nonUnitalRing α, AddOpposite.nonUnitalCommSemiring α with }

instance [CommRing α] : CommRing αᵃᵒᵖ :=
  { AddOpposite.ring α, AddOpposite.commSemiring α with }

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors αᵃᵒᵖ
    where eq_zero_or_eq_zero_of_mul_eq_zero x y (H : op (_ * _) = op (0 : α)) :=
    Or.imp (fun hx => unop_injective hx) (fun hy => unop_injective hy)
      (@eq_zero_or_eq_zero_of_mul_eq_zero α _ _ _ _ _ <| op_injective H)

instance [Ring α] [IsDomain α] : IsDomain αᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

instance [GroupWithZero α] : GroupWithZero αᵃᵒᵖ :=
  { AddOpposite.monoidWithZero α, AddOpposite.divInvMonoid α,
    AddOpposite.nontrivial
      α with
    mul_inv_cancel := fun x hx => unop_injective <| mul_inv_cancel <| unop_injective.Ne hx
    inv_zero := unop_injective inv_zero }

end AddOpposite

open MulOpposite

/- warning: non_unital_ring_hom.to_opposite -> NonUnitalRingHom.toOpposite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} S] (f : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2), (forall (x : R) (y : R), Commute.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (NonUnitalRingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (NonUnitalRingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f y)) -> (NonUnitalRingHom.{u1, u2} R (MulOpposite.{u2} S) _inst_1 (MulOpposite.nonUnitalNonAssocSemiring.{u2} S _inst_2))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} S] (f : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2), (forall (x : R) (y : R), Commute.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) _inst_2) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} S _inst_2) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} S _inst_2) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2))) f y)) -> (NonUnitalRingHom.{u1, u2} R (MulOpposite.{u2} S) _inst_1 (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u2} S _inst_2))
Case conversion may be inaccurate. Consider using '#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOppositeₓ'. -/
/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.toOpposite {R S : Type _} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : R →ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align non_unital_ring_hom.to_opposite NonUnitalRingHom.toOpposite

/- warning: non_unital_ring_hom.from_opposite -> NonUnitalRingHom.fromOpposite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} S] (f : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2), (forall (x : R) (y : R), Commute.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S _inst_2)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (NonUnitalRingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) (fun (_x : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) => R -> S) (NonUnitalRingHom.hasCoeToFun.{u1, u2} R S _inst_1 _inst_2) f y)) -> (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} R) S (MulOpposite.nonUnitalNonAssocSemiring.{u1} R _inst_1) _inst_2)
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] [_inst_2 : NonUnitalNonAssocSemiring.{u2} S] (f : NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2), (forall (x : R) (y : R), Commute.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) _inst_2) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} S _inst_2) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2))) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) (NonUnitalNonAssocSemiring.toMul.{u2} S _inst_2) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (NonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2) R S _inst_1 _inst_2 (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u1, u2} R S _inst_1 _inst_2))) f y)) -> (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} R) S (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u1} R _inst_1) _inst_2)
Case conversion may be inaccurate. Consider using '#align non_unital_ring_hom.from_opposite NonUnitalRingHom.fromOppositeₓ'. -/
/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def NonUnitalRingHom.fromOpposite {R S : Type _} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R →ₙ+* S) (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align non_unital_ring_hom.from_opposite NonUnitalRingHom.fromOpposite

/- warning: non_unital_ring_hom.op -> NonUnitalRingHom.op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} α β _inst_1 _inst_2) (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.nonUnitalNonAssocSemiring.{u1} α _inst_1) (MulOpposite.nonUnitalNonAssocSemiring.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (NonUnitalRingHom.{u1, u2} α β _inst_1 _inst_2) (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u1} α _inst_1) (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align non_unital_ring_hom.op NonUnitalRingHom.opₓ'. -/
/-- A non-unital ring hom `α →ₙ+* β` can equivalently be viewed as a non-unital ring hom
`αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def NonUnitalRingHom.op {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (α →ₙ+* β) ≃ (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ)
    where
  toFun f := { f.toAddMonoidHom.mulOp, f.toMulHom.op with }
  invFun f := { f.toAddMonoidHom.mulUnop, f.toMulHom.unop with }
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    simp
#align non_unital_ring_hom.op NonUnitalRingHom.op

/- warning: non_unital_ring_hom.unop -> NonUnitalRingHom.unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.nonUnitalNonAssocSemiring.{u1} α _inst_1) (MulOpposite.nonUnitalNonAssocSemiring.{u2} β _inst_2)) (NonUnitalRingHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] [_inst_2 : NonUnitalNonAssocSemiring.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (NonUnitalRingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u1} α _inst_1) (MulOpposite.instNonUnitalNonAssocSemiringMulOpposite.{u2} β _inst_2)) (NonUnitalRingHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align non_unital_ring_hom.unop NonUnitalRingHom.unopₓ'. -/
/-- The 'unopposite' of a non-unital ring hom `αᵐᵒᵖ →ₙ+* βᵐᵒᵖ`. Inverse to
`non_unital_ring_hom.op`. -/
@[simp]
def NonUnitalRingHom.unop {α β} [NonUnitalNonAssocSemiring α] [NonUnitalNonAssocSemiring β] :
    (αᵐᵒᵖ →ₙ+* βᵐᵒᵖ) ≃ (α →ₙ+* β) :=
  NonUnitalRingHom.op.symm
#align non_unital_ring_hom.unop NonUnitalRingHom.unop

/- warning: ring_hom.to_opposite -> RingHom.toOpposite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)), (forall (x : R) (y : R), Commute.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f y)) -> (RingHom.{u1, u2} R (MulOpposite.{u2} S) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.nonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)), (forall (x : R) (y : R), Commute.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) _inst_2))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f y)) -> (RingHom.{u1, u2} R (MulOpposite.{u2} S) (Semiring.toNonAssocSemiring.{u1} R _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)))
Case conversion may be inaccurate. Consider using '#align ring_hom.to_opposite RingHom.toOppositeₓ'. -/
/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def RingHom.toOpposite {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R →+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }
#align ring_hom.to_opposite RingHom.toOpposite

/- warning: ring_hom.from_opposite -> RingHom.fromOpposite is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)), (forall (x : R) (y : R), Commute.{u2} S (Distrib.toHasMul.{u2} S (NonUnitalNonAssocSemiring.toDistrib.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (fun (_x : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) => R -> S) (RingHom.hasCoeToFun.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) f y)) -> (RingHom.{u1, u2} (MulOpposite.{u1} R) S (MulOpposite.nonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2))
but is expected to have type
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : Semiring.{u1} R] [_inst_2 : Semiring.{u2} S] (f : RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)), (forall (x : R) (y : R), Commute.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonUnitalNonAssocSemiring.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) (Semiring.toNonAssocSemiring.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) x) _inst_2))) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f x) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R (fun (_x : R) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : R) => S) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1))) (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2))) (NonUnitalRingHomClass.toMulHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S _inst_2)) (RingHomClass.toNonUnitalRingHomClass.{max u1 u2, u1, u2} (RingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2)) R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2) (RingHom.instRingHomClassRingHom.{u1, u2} R S (Semiring.toNonAssocSemiring.{u1} R _inst_1) (Semiring.toNonAssocSemiring.{u2} S _inst_2))))) f y)) -> (RingHom.{u1, u2} (MulOpposite.{u1} R) S (MulOpposite.instNonAssocSemiringMulOpposite.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)) (Semiring.toNonAssocSemiring.{u2} S _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_hom.from_opposite RingHom.fromOppositeₓ'. -/
/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps (config := { fullyApplied := false })]
def RingHom.fromOpposite {R S : Type _} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : ∀ x y, Commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ →+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }
#align ring_hom.from_opposite RingHom.fromOpposite

/- warning: ring_hom.op -> RingHom.op is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : NonAssocSemiring.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} α β _inst_1 _inst_2) (RingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.nonAssocSemiring.{u1} α _inst_1) (MulOpposite.nonAssocSemiring.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : NonAssocSemiring.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RingHom.{u1, u2} α β _inst_1 _inst_2) (RingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} α _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align ring_hom.op RingHom.opₓ'. -/
/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def RingHom.op {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ)
    where
  toFun f := { f.toAddMonoidHom.mulOp, f.toMonoidHom.op with }
  invFun f := { f.toAddMonoidHom.mulUnop, f.toMonoidHom.unop with }
  left_inv f := by
    ext
    rfl
  right_inv f := by
    ext
    simp
#align ring_hom.op RingHom.op

/- warning: ring_hom.unop -> RingHom.unop is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : NonAssocSemiring.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.nonAssocSemiring.{u1} α _inst_1) (MulOpposite.nonAssocSemiring.{u2} β _inst_2)) (RingHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : NonAssocSemiring.{u1} α] [_inst_2 : NonAssocSemiring.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (RingHom.{u1, u2} (MulOpposite.{u1} α) (MulOpposite.{u2} β) (MulOpposite.instNonAssocSemiringMulOpposite.{u1} α _inst_1) (MulOpposite.instNonAssocSemiringMulOpposite.{u2} β _inst_2)) (RingHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align ring_hom.unop RingHom.unopₓ'. -/
/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp]
def RingHom.unop {α β} [NonAssocSemiring α] [NonAssocSemiring β] : (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) :=
  RingHom.op.symm
#align ring_hom.unop RingHom.unop

