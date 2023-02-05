/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.ring.pi
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.PiInstances
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Hom.Ring

/-!
# Pi instances for ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ring, semiring and related structures on Pi Types
-/


namespace Pi

universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

#print Pi.distrib /-
instance distrib [∀ i, Distrib <| f i] : Distrib (∀ i : I, f i) := by
  refine_struct
      { add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.distrib Pi.distrib
-/

#print Pi.nonUnitalNonAssocSemiring /-
instance nonUnitalNonAssocSemiring [∀ i, NonUnitalNonAssocSemiring <| f i] :
    NonUnitalNonAssocSemiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.non_unital_non_assoc_semiring Pi.nonUnitalNonAssocSemiring
-/

#print Pi.nonUnitalSemiring /-
instance nonUnitalSemiring [∀ i, NonUnitalSemiring <| f i] : NonUnitalSemiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.non_unital_semiring Pi.nonUnitalSemiring
-/

#print Pi.nonAssocSemiring /-
instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := 1
        add := (· + ·)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.non_assoc_semiring Pi.nonAssocSemiring
-/

#print Pi.semiring /-
instance semiring [∀ i, Semiring <| f i] : Semiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.semiring Pi.semiring
-/

#print Pi.nonUnitalCommSemiring /-
instance nonUnitalCommSemiring [∀ i, NonUnitalCommSemiring <| f i] :
    NonUnitalCommSemiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul } <;>
    pi_instance_derive_field
#align pi.non_unital_comm_semiring Pi.nonUnitalCommSemiring
-/

#print Pi.commSemiring /-
instance commSemiring [∀ i, CommSemiring <| f i] : CommSemiring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        nsmul := AddMonoid.nsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_semiring Pi.commSemiring
-/

#print Pi.nonUnitalNonAssocRing /-
instance nonUnitalNonAssocRing [∀ i, NonUnitalNonAssocRing <| f i] :
    NonUnitalNonAssocRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align pi.non_unital_non_assoc_ring Pi.nonUnitalNonAssocRing
-/

#print Pi.nonUnitalRing /-
instance nonUnitalRing [∀ i, NonUnitalRing <| f i] : NonUnitalRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align pi.non_unital_ring Pi.nonUnitalRing
-/

#print Pi.nonAssocRing /-
instance nonAssocRing [∀ i, NonAssocRing <| f i] : NonAssocRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align pi.non_assoc_ring Pi.nonAssocRing
-/

#print Pi.ring /-
instance ring [∀ i, Ring <| f i] : Ring (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.ring Pi.ring
-/

#print Pi.nonUnitalCommRing /-
instance nonUnitalCommRing [∀ i, NonUnitalCommRing <| f i] : NonUnitalCommRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul } <;>
    pi_instance_derive_field
#align pi.non_unital_comm_ring Pi.nonUnitalCommRing
-/

#print Pi.commRing /-
instance commRing [∀ i, CommRing <| f i] : CommRing (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := 1
        add := (· + ·)
        mul := (· * ·)
        neg := Neg.neg
        nsmul := AddMonoid.nsmul
        zsmul := SubNegMonoid.zsmul
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_ring Pi.commRing
-/

#print Pi.nonUnitalRingHom /-
/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `pi.non_unital_ring_hom f : γ →+* Π a, β a` given by
`pi.non_unital_ring_hom f x b = f b x`. -/
@[simps]
protected def nonUnitalRingHom {γ : Type w} [∀ i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i) : γ →ₙ+* ∀ i, f i :=
  { Pi.mulHom fun i => (g i).toMulHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }
#align pi.non_unital_ring_hom Pi.nonUnitalRingHom
-/

/- warning: pi.non_unital_ring_hom_injective -> Pi.nonUnitalRingHom_injective is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), NonUnitalNonAssocSemiring.{u2} (f i)] [_inst_3 : NonUnitalNonAssocSemiring.{u3} γ] (g : forall (i : I), NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (fun (_x : NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) => γ -> (f i)) (NonUnitalRingHom.hasCoeToFun.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), (fun (i : I) => f i) i) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (NonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (fun (_x : NonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) => γ -> (forall (i : I), (fun (i : I) => f i) i)) (NonUnitalRingHom.hasCoeToFun.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (Pi.nonUnitalRingHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), NonUnitalNonAssocSemiring.{u2} (f i)] [_inst_3 : NonUnitalNonAssocSemiring.{u3} γ] (g : forall (i : I), NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : γ) => f i) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) (NonUnitalNonAssocSemiring.toMul.{u3} γ _inst_3) (NonUnitalNonAssocSemiring.toMul.{u2} (f i) (_inst_2 i)) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u3, u2} (NonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) _inst_3 (_inst_2 i) (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)))) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), f i) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u3, max (succ u1) (succ u2)} (NonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : γ) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max (max u1 u2) u3, u3, max u1 u2} (NonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) (NonUnitalNonAssocSemiring.toMul.{u3} γ _inst_3) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (forall (i : I), f i) (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (NonUnitalRingHomClass.toMulHomClass.{max (max u1 u2) u3, u3, max u1 u2} (NonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) (NonUnitalRingHom.instNonUnitalRingHomClassNonUnitalRingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonUnitalNonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))))) (Pi.nonUnitalRingHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
Case conversion may be inaccurate. Consider using '#align pi.non_unital_ring_hom_injective Pi.nonUnitalRingHom_injectiveₓ'. -/
theorem nonUnitalRingHom_injective {γ : Type w} [Nonempty I] [∀ i, NonUnitalNonAssocSemiring (f i)]
    [NonUnitalNonAssocSemiring γ] (g : ∀ i, γ →ₙ+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.nonUnitalRingHom g) :=
  mulHom_injective (fun i => (g i).toMulHom) hg
#align pi.non_unital_ring_hom_injective Pi.nonUnitalRingHom_injective

#print Pi.ringHom /-
/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
@[simps]
protected def ringHom {γ : Type w} [∀ i, NonAssocSemiring (f i)] [NonAssocSemiring γ]
    (g : ∀ i, γ →+* f i) : γ →+* ∀ i, f i :=
  { Pi.monoidHom fun i => (g i).toMonoidHom, Pi.addMonoidHom fun i => (g i).toAddMonoidHom with
    toFun := fun x b => g b x }
#align pi.ring_hom Pi.ringHom
-/

/- warning: pi.ring_hom_injective -> Pi.ringHom_injective is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), NonAssocSemiring.{u2} (f i)] [_inst_3 : NonAssocSemiring.{u3} γ] (g : forall (i : I), RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (coeFn.{max (succ u3) (succ u2), max (succ u3) (succ u2)} (RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (fun (_x : RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) => γ -> (f i)) (RingHom.hasCoeToFun.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), (fun (i : I) => f i) i) (coeFn.{max (succ u3) (succ (max u1 u2)), max (succ u3) (succ (max u1 u2))} (RingHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (fun (_x : RingHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) => γ -> (forall (i : I), (fun (i : I) => f i) i)) (RingHom.hasCoeToFun.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (Pi.ringHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), NonAssocSemiring.{u2} (f i)] [_inst_3 : NonAssocSemiring.{u3} γ] (g : forall (i : I), RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : γ) => f i) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_3)) (NonUnitalNonAssocSemiring.toMul.{u2} (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (f i) (_inst_2 i))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u3, u3, u2} (RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_3) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} (f i) (_inst_2 i)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u3, u3, u2} (RingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) _inst_3 (_inst_2 i) (RingHom.instRingHomClassRingHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i))))) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), f i) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u3, max (succ u1) (succ u2)} (RingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : γ) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max (max u1 u2) u3, u3, max u1 u2} (RingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) (NonUnitalNonAssocSemiring.toMul.{u3} γ (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_3)) (NonUnitalNonAssocSemiring.toMul.{max u1 u2} (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)))) (NonUnitalRingHomClass.toMulHomClass.{max (max u1 u2) u3, u3, max u1 u2} (RingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} γ _inst_3) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (forall (i : I), f i) (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (RingHomClass.toNonUnitalRingHomClass.{max (max u1 u2) u3, u3, max u1 u2} (RingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) (RingHom.instRingHomClassRingHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.nonAssocSemiring.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)))))) (Pi.ringHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
Case conversion may be inaccurate. Consider using '#align pi.ring_hom_injective Pi.ringHom_injectiveₓ'. -/
theorem ringHom_injective {γ : Type w} [Nonempty I] [∀ i, NonAssocSemiring (f i)]
    [NonAssocSemiring γ] (g : ∀ i, γ →+* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.ringHom g) :=
  monoidHom_injective (fun i => (g i).toMonoidHom) hg
#align pi.ring_hom_injective Pi.ringHom_injective

end Pi

section NonUnitalRingHom

universe u v

variable {I : Type u}

#print Pi.evalNonUnitalRingHom /-
/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `function.eval` as a `non_unital_ring_hom`. -/
@[simps]
def Pi.evalNonUnitalRingHom (f : I → Type v) [∀ i, NonUnitalNonAssocSemiring (f i)] (i : I) :
    (∀ i, f i) →ₙ+* f i :=
  { Pi.evalMulHom f i, Pi.evalAddMonoidHom f i with }
#align pi.eval_non_unital_ring_hom Pi.evalNonUnitalRingHom
-/

#print Pi.constNonUnitalRingHom /-
/-- `function.const` as a `non_unital_ring_hom`. -/
@[simps]
def Pi.constNonUnitalRingHom (α β : Type _) [NonUnitalNonAssocSemiring β] : β →ₙ+* α → β :=
  { Pi.nonUnitalRingHom fun _ => NonUnitalRingHom.id β with toFun := Function.const _ }
#align pi.const_non_unital_ring_hom Pi.constNonUnitalRingHom
-/

#print NonUnitalRingHom.compLeft /-
/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps]
protected def NonUnitalRingHom.compLeft {α β : Type _} [NonUnitalNonAssocSemiring α]
    [NonUnitalNonAssocSemiring β] (f : α →ₙ+* β) (I : Type _) : (I → α) →ₙ+* I → β :=
  { f.toMulHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }
#align non_unital_ring_hom.comp_left NonUnitalRingHom.compLeft
-/

end NonUnitalRingHom

section RingHom

universe u v

variable {I : Type u}

#print Pi.evalRingHom /-
/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `function.eval` as a `ring_hom`. -/
@[simps]
def Pi.evalRingHom (f : I → Type v) [∀ i, NonAssocSemiring (f i)] (i : I) : (∀ i, f i) →+* f i :=
  { Pi.evalMonoidHom f i, Pi.evalAddMonoidHom f i with }
#align pi.eval_ring_hom Pi.evalRingHom
-/

#print Pi.constRingHom /-
/-- `function.const` as a `ring_hom`. -/
@[simps]
def Pi.constRingHom (α β : Type _) [NonAssocSemiring β] : β →+* α → β :=
  { Pi.ringHom fun _ => RingHom.id β with toFun := Function.const _ }
#align pi.const_ring_hom Pi.constRingHom
-/

#print RingHom.compLeft /-
/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps]
protected def RingHom.compLeft {α β : Type _} [NonAssocSemiring α] [NonAssocSemiring β]
    (f : α →+* β) (I : Type _) : (I → α) →+* I → β :=
  { f.toMonoidHom.compLeft I, f.toAddMonoidHom.compLeft I with toFun := fun h => f ∘ h }
#align ring_hom.comp_left RingHom.compLeft
-/

end RingHom

