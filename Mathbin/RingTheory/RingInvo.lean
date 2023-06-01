/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau

! This file was ported from Lean 3 source module ring_theory.ring_invo
! leanprover-community/mathlib commit fac369018417f980cec5fcdafc766a69f88d8cfe
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
  coe_injective' e f h₁ h₂ := by cases e; cases f; congr
  map_add := map_add'
  map_mul := map_mul'
  left_inv := left_inv
  right_inv := right_inv
  involution := involution'

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

@[simp]
theorem toFun_eq_coe (f : RingInvo R) : f.toFun = f :=
  rfl
#align ring_invo.to_fun_eq_coe RingInvo.toFun_eq_coe

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

