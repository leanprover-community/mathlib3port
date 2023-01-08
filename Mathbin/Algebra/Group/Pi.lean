/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot

! This file was ported from Lean 3 source module algebra.group.pi
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Pairwise
import Mathbin.Algebra.Hom.GroupInstances
import Mathbin.Data.Pi.Algebra
import Mathbin.Data.Set.Function
import Mathbin.Tactic.PiInstances

/-!
# Pi instances for groups and monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for group, monoid, semigroup and related structures on Pi types.
-/


universe u v w

variable {ι α : Type _}

variable {I : Type u}

-- The indexing type
variable {f : I → Type v}

-- The family of types already equipped with instances
variable (x y : ∀ i, f i) (i : I)

/- warning: set.preimage_one -> Set.preimage_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : One.{u2} β] (s : Set.{u2} β) [_inst_2 : Decidable (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_1))) s)], Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (OfNat.ofNat.{max u1 u2} (α -> β) 1 (OfNat.mk.{max u1 u2} (α -> β) 1 (One.one.{max u1 u2} (α -> β) (Pi.instOne.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => _inst_1))))) s) (ite.{succ u1} (Set.{u1} α) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (OfNat.ofNat.{u2} β 1 (OfNat.mk.{u2} β 1 (One.one.{u2} β _inst_1))) s) _inst_2 (Set.univ.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : One.{u1} β] (s : Set.{u1} β) [_inst_2 : Decidable (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β _inst_1)) s)], Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (OfNat.ofNat.{max u2 u1} (α -> β) 1 (One.toOfNat1.{max u2 u1} (α -> β) (Pi.instOne.{u2, u1} α (fun (a._@.Mathlib.Algebra.Group.Pi._hyg.92 : α) => β) (fun (i : α) => _inst_1)))) s) (ite.{succ u2} (Set.{u2} α) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (OfNat.ofNat.{u1} β 1 (One.toOfNat1.{u1} β _inst_1)) s) _inst_2 (Set.univ.{u2} α) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)))
Case conversion may be inaccurate. Consider using '#align set.preimage_one Set.preimage_oneₓ'. -/
@[to_additive]
theorem Set.preimage_one {α β : Type _} [One β] (s : Set β) [Decidable ((1 : β) ∈ s)] :
    (1 : α → β) ⁻¹' s = if (1 : β) ∈ s then Set.univ else ∅ :=
  Set.preimage_const 1 s
#align set.preimage_one Set.preimage_one

namespace Pi

#print Pi.semigroup /-
@[to_additive]
instance semigroup [∀ i, Semigroup <| f i] : Semigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;> pi_instance_derive_field
#align pi.semigroup Pi.semigroup
-/

#print Pi.semigroupWithZero /-
instance semigroupWithZero [∀ i, SemigroupWithZero <| f i] : SemigroupWithZero (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.semigroup_with_zero Pi.semigroupWithZero
-/

#print Pi.commSemigroup /-
@[to_additive]
instance commSemigroup [∀ i, CommSemigroup <| f i] : CommSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·).. } <;> pi_instance_derive_field
#align pi.comm_semigroup Pi.commSemigroup
-/

#print Pi.mulOneClass /-
@[to_additive]
instance mulOneClass [∀ i, MulOneClass <| f i] : MulOneClass (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_one_class Pi.mulOneClass
-/

#print Pi.monoid /-
@[to_additive]
instance monoid [∀ i, Monoid <| f i] : Monoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := fun n x i => x i ^ n } <;>
    pi_instance_derive_field
#align pi.monoid Pi.monoid
-/

#print Pi.commMonoid /-
@[to_additive]
instance commMonoid [∀ i, CommMonoid <| f i] : CommMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_monoid Pi.commMonoid
-/

@[to_additive Pi.subNegMonoid]
instance [∀ i, DivInvMonoid <| f i] : DivInvMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive]
instance [∀ i, InvolutiveInv <| f i] : InvolutiveInv (∀ i, f i) := by
  refine_struct { inv := Inv.inv } <;> pi_instance_derive_field

@[to_additive Pi.subtractionMonoid]
instance [∀ i, DivisionMonoid <| f i] : DivisionMonoid (∀ i, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := fun z x i => x i ^ z } <;>
    pi_instance_derive_field

@[to_additive Pi.subtractionCommMonoid]
instance [∀ i, DivisionCommMonoid <| f i] : DivisionCommMonoid (∀ i, f i) :=
  { Pi.divisionMonoid, Pi.commSemigroup with }

#print Pi.group /-
@[to_additive]
instance group [∀ i, Group <| f i] : Group (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field
#align pi.group Pi.group
-/

#print Pi.commGroup /-
@[to_additive]
instance commGroup [∀ i, CommGroup <| f i] : CommGroup (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        inv := Inv.inv
        div := Div.div
        npow := Monoid.npow
        zpow := DivInvMonoid.zpow } <;>
    pi_instance_derive_field
#align pi.comm_group Pi.commGroup
-/

#print Pi.leftCancelSemigroup /-
@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup <| f i] :
    LeftCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;> pi_instance_derive_field
#align pi.left_cancel_semigroup Pi.leftCancelSemigroup
-/

#print Pi.rightCancelSemigroup /-
@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup <| f i] :
    RightCancelSemigroup (∀ i : I, f i) := by
  refine_struct { mul := (· * ·) } <;> pi_instance_derive_field
#align pi.right_cancel_semigroup Pi.rightCancelSemigroup
-/

#print Pi.leftCancelMonoid /-
@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [∀ i, LeftCancelMonoid <| f i] : LeftCancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.left_cancel_monoid Pi.leftCancelMonoid
-/

#print Pi.rightCancelMonoid /-
@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [∀ i, RightCancelMonoid <| f i] : RightCancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow.. } <;>
    pi_instance_derive_field
#align pi.right_cancel_monoid Pi.rightCancelMonoid
-/

#print Pi.cancelMonoid /-
@[to_additive AddCancelMonoid]
instance cancelMonoid [∀ i, CancelMonoid <| f i] : CancelMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.cancel_monoid Pi.cancelMonoid
-/

#print Pi.cancelCommMonoid /-
@[to_additive AddCancelCommMonoid]
instance cancelCommMonoid [∀ i, CancelCommMonoid <| f i] : CancelCommMonoid (∀ i : I, f i) := by
  refine_struct
      { one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.cancel_comm_monoid Pi.cancelCommMonoid
-/

#print Pi.mulZeroClass /-
instance mulZeroClass [∀ i, MulZeroClass <| f i] : MulZeroClass (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_zero_class Pi.mulZeroClass
-/

#print Pi.mulZeroOneClass /-
instance mulZeroOneClass [∀ i, MulZeroOneClass <| f i] : MulZeroOneClass (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·).. } <;>
    pi_instance_derive_field
#align pi.mul_zero_one_class Pi.mulZeroOneClass
-/

#print Pi.monoidWithZero /-
instance monoidWithZero [∀ i, MonoidWithZero <| f i] : MonoidWithZero (∀ i : I, f i) := by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.monoid_with_zero Pi.monoidWithZero
-/

#print Pi.commMonoidWithZero /-
instance commMonoidWithZero [∀ i, CommMonoidWithZero <| f i] : CommMonoidWithZero (∀ i : I, f i) :=
  by
  refine_struct
      { zero := (0 : ∀ i, f i)
        one := (1 : ∀ i, f i)
        mul := (· * ·)
        npow := Monoid.npow } <;>
    pi_instance_derive_field
#align pi.comm_monoid_with_zero Pi.commMonoidWithZero
-/

end Pi

namespace MulHom

/- warning: mul_hom.coe_mul -> MulHom.coe_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {mM : Mul.{u1} M} {mN : CommSemigroup.{u2} N} (f : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (g : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))), Eq.{max (succ u1) (succ u2)} (M -> N) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (M -> N) (M -> N) (M -> N) (instHMul.{max u1 u2} (M -> N) (Pi.instMul.{u1, u2} M (fun (ᾰ : M) => N) (fun (i : M) => Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN)))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) g)) (fun (x : M) => HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) f x) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) (fun (_x : MulHom.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) => M -> N) (MulHom.hasCoeToFun.{u1, u2} M N mM (Semigroup.toHasMul.{u2} N (CommSemigroup.toSemigroup.{u2} N mN))) g x))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} {mM : Mul.{u2} M} {mN : CommSemigroup.{u1} N} (f : MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) (g : MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (instHMul.{max u2 u1} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (Pi.instMul.{u2, u1} M (fun (ᾰ : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (fun (i : M) => Semigroup.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) i) (CommSemigroup.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) i) mN)))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) g)) (fun (x : M) => HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (Semigroup.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) (CommSemigroup.toSemigroup.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) x) mN))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MulHom.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN))) M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)) (MulHom.mulHomClass.{u2, u1} M N mM (Semigroup.toMul.{u1} N (CommSemigroup.toSemigroup.{u1} N mN)))) g x))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_mul MulHom.coe_mulₓ'. -/
@[to_additive]
theorem coe_mul {M N} {mM : Mul M} {mN : CommSemigroup N} (f g : M →ₙ* N) :
    (f * g : M → N) = fun x => f x * g x :=
  rfl
#align mul_hom.coe_mul MulHom.coe_mul

end MulHom

section MulHom

#print Pi.mulHom /-
/-- A family of mul_hom `f a : γ →ₙ* β a` defines a mul_hom `pi.mul_hom f : γ →ₙ* Π a, β a`
given by `pi.mul_hom f x b = f b x`. -/
@[to_additive
      "A family of add_hom `f a : γ → β a` defines a add_hom `pi.add_hom\nf : γ → Π a, β a` given by `pi.add_hom f x b = f b x`.",
  simps]
def Pi.mulHom {γ : Type w} [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i) : γ →ₙ* ∀ i, f i
    where
  toFun x i := g i x
  map_mul' x y := funext fun i => (g i).map_mul x y
#align pi.mul_hom Pi.mulHom
-/

#print Pi.mulHom_injective /-
@[to_additive]
theorem Pi.mulHom_injective {γ : Type w} [Nonempty I] [∀ i, Mul (f i)] [Mul γ] (g : ∀ i, γ →ₙ* f i)
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (Pi.mulHom g) := fun x y h =>
  let ⟨i⟩ := ‹Nonempty I›
  hg i ((Function.funext_iff.mp h : _) i)
#align pi.mul_hom_injective Pi.mulHom_injective
-/

#print Pi.monoidHom /-
/-- A family of monoid homomorphisms `f a : γ →* β a` defines a monoid homomorphism
`pi.monoid_mul_hom f : γ →* Π a, β a` given by `pi.monoid_mul_hom f x b = f b x`. -/
@[to_additive
      "A family of additive monoid homomorphisms `f a : γ →+ β a` defines a monoid\nhomomorphism `pi.add_monoid_hom f : γ →+ Π a, β a` given by `pi.add_monoid_hom f x b\n= f b x`.",
  simps]
def Pi.monoidHom {γ : Type w} [∀ i, MulOneClass (f i)] [MulOneClass γ] (g : ∀ i, γ →* f i) :
    γ →* ∀ i, f i :=
  {
    Pi.mulHom fun i => (g i).toMulHom with
    toFun := fun x i => g i x
    map_one' := funext fun i => (g i).map_one }
#align pi.monoid_hom Pi.monoidHom
-/

/- warning: pi.monoid_hom_injective -> Pi.monoidHom_injective is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] [_inst_3 : MulOneClass.{u3} γ] (g : forall (i : I), MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (coeFn.{max (succ u2) (succ u3), max (succ u3) (succ u2)} (MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (fun (_x : MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) => γ -> (f i)) (MonoidHom.hasCoeToFun.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), (fun (i : I) => f i) i) (coeFn.{max (succ (max u1 u2)) (succ u3), max (succ u3) (succ (max u1 u2))} (MonoidHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (fun (_x : MonoidHom.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) => γ -> (forall (i : I), (fun (i : I) => f i) i)) (MonoidHom.hasCoeToFun.{u3, max u1 u2} γ (forall (i : I), (fun (i : I) => f i) i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => (fun (i : I) => f i) i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (Pi.monoidHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} {γ : Type.{u3}} [_inst_1 : Nonempty.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] [_inst_3 : MulOneClass.{u3} γ] (g : forall (i : I), MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)), (forall (i : I), Function.Injective.{succ u3, succ u2} γ (f i) (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : γ) => f i) _x) (MulHomClass.toFunLike.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) (MulOneClass.toMul.{u3} γ _inst_3) (MulOneClass.toMul.{u2} (f i) (_inst_2 i)) (MonoidHomClass.toMulHomClass.{max u2 u3, u3, u2} (MonoidHom.{u3, u2} γ (f i) _inst_3 (_inst_2 i)) γ (f i) _inst_3 (_inst_2 i) (MonoidHom.monoidHomClass.{u3, u2} γ (f i) _inst_3 (_inst_2 i)))) (g i))) -> (Function.Injective.{succ u3, max (succ u1) (succ u2)} γ (forall (i : I), f i) (FunLike.coe.{max (max (succ u1) (succ u2)) (succ u3), succ u3, max (succ u1) (succ u2)} (MonoidHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (fun (_x : γ) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : γ) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max (max u1 u2) u3, u3, max u1 u2} (MonoidHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) (MulOneClass.toMul.{u3} γ _inst_3) (MulOneClass.toMul.{max u1 u2} (forall (i : I), f i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (MonoidHomClass.toMulHomClass.{max (max u1 u2) u3, u3, max u1 u2} (MonoidHom.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) γ (forall (i : I), f i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) (MonoidHom.monoidHomClass.{u3, max u1 u2} γ (forall (i : I), f i) _inst_3 (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))))) (Pi.monoidHom.{u1, u2, u3} I (fun (i : I) => f i) γ (fun (i : I) => _inst_2 i) _inst_3 g)))
Case conversion may be inaccurate. Consider using '#align pi.monoid_hom_injective Pi.monoidHom_injectiveₓ'. -/
@[to_additive]
theorem Pi.monoidHom_injective {γ : Type w} [Nonempty I] [∀ i, MulOneClass (f i)] [MulOneClass γ]
    (g : ∀ i, γ →* f i) (hg : ∀ i, Function.Injective (g i)) :
    Function.Injective (Pi.monoidHom g) :=
  Pi.mulHom_injective (fun i => (g i).toMulHom) hg
#align pi.monoid_hom_injective Pi.monoidHom_injective

variable (f) [∀ i, Mul (f i)]

#print Pi.evalMulHom /-
/-- Evaluation of functions into an indexed collection of semigroups at a point is a semigroup
homomorphism.
This is `function.eval i` as a `mul_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive semigroups at a\npoint is an additive semigroup homomorphism.\nThis is `function.eval i` as an `add_hom`.",
  simps]
def Pi.evalMulHom (i : I) : (∀ i, f i) →ₙ* f i
    where
  toFun g := g i
  map_mul' x y := Pi.mul_apply _ _ i
#align pi.eval_mul_hom Pi.evalMulHom
-/

#print Pi.constMulHom /-
/-- `function.const` as a `mul_hom`. -/
@[to_additive "`function.const` as an `add_hom`.", simps]
def Pi.constMulHom (α β : Type _) [Mul β] : β →ₙ* α → β
    where
  toFun := Function.const α
  map_mul' _ _ := rfl
#align pi.const_mul_hom Pi.constMulHom
-/

/- warning: mul_hom.coe_fn -> MulHom.coeFn is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_2 : Mul.{u1} α] [_inst_3 : CommSemigroup.{u2} β], MulHom.{max u2 u1, max u1 u2} (MulHom.{u1, u2} α β _inst_2 (Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_3))) (α -> β) (MulHom.hasMul.{u1, u2} α β _inst_2 _inst_3) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Semigroup.toHasMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_3)))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_2 : Mul.{u1} α] [_inst_3 : CommSemigroup.{u2} β], MulHom.{max u2 u1, max u1 u2} (MulHom.{u1, u2} α β _inst_2 (Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_3))) (α -> β) (MulHom.instMulMulHomToMulToSemigroup.{u1, u2} α β _inst_2 _inst_3) (Pi.instMul.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => Semigroup.toMul.{u2} β (CommSemigroup.toSemigroup.{u2} β _inst_3)))
Case conversion may be inaccurate. Consider using '#align mul_hom.coe_fn MulHom.coeFnₓ'. -/
/-- Coercion of a `mul_hom` into a function is itself a `mul_hom`.
See also `mul_hom.eval`. -/
@[to_additive
      "Coercion of an `add_hom` into a function is itself a `add_hom`.\nSee also `add_hom.eval`. ",
  simps]
def MulHom.coeFn (α β : Type _) [Mul α] [CommSemigroup β] : (α →ₙ* β) →ₙ* α → β
    where
  toFun g := g
  map_mul' x y := rfl
#align mul_hom.coe_fn MulHom.coeFn

#print MulHom.compLeft /-
/-- Semigroup homomorphism between the function spaces `I → α` and `I → β`, induced by a semigroup
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive semigroup homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive semigroup homomorphism `f` between `α` and `β`",
  simps]
protected def MulHom.compLeft {α β : Type _} [Mul α] [Mul β] (f : α →ₙ* β) (I : Type _) :
    (I → α) →ₙ* I → β where
  toFun h := f ∘ h
  map_mul' _ _ := by ext <;> simp
#align mul_hom.comp_left MulHom.compLeft
-/

end MulHom

section MonoidHom

variable (f) [∀ i, MulOneClass (f i)]

#print Pi.evalMonoidHom /-
/-- Evaluation of functions into an indexed collection of monoids at a point is a monoid
homomorphism.
This is `function.eval i` as a `monoid_hom`. -/
@[to_additive
      "Evaluation of functions into an indexed collection of additive monoids at a\npoint is an additive monoid homomorphism.\nThis is `function.eval i` as an `add_monoid_hom`.",
  simps]
def Pi.evalMonoidHom (i : I) : (∀ i, f i) →* f i
    where
  toFun g := g i
  map_one' := Pi.one_apply i
  map_mul' x y := Pi.mul_apply _ _ i
#align pi.eval_monoid_hom Pi.evalMonoidHom
-/

#print Pi.constMonoidHom /-
/-- `function.const` as a `monoid_hom`. -/
@[to_additive "`function.const` as an `add_monoid_hom`.", simps]
def Pi.constMonoidHom (α β : Type _) [MulOneClass β] : β →* α → β
    where
  toFun := Function.const α
  map_one' := rfl
  map_mul' _ _ := rfl
#align pi.const_monoid_hom Pi.constMonoidHom
-/

#print MonoidHom.coeFn /-
/-- Coercion of a `monoid_hom` into a function is itself a `monoid_hom`.

See also `monoid_hom.eval`. -/
@[to_additive
      "Coercion of an `add_monoid_hom` into a function is itself a `add_monoid_hom`.\n\nSee also `add_monoid_hom.eval`. ",
  simps]
def MonoidHom.coeFn (α β : Type _) [MulOneClass α] [CommMonoid β] : (α →* β) →* α → β
    where
  toFun g := g
  map_one' := rfl
  map_mul' x y := rfl
#align monoid_hom.coe_fn MonoidHom.coeFn
-/

#print MonoidHom.compLeft /-
/-- Monoid homomorphism between the function spaces `I → α` and `I → β`, induced by a monoid
homomorphism `f` between `α` and `β`. -/
@[to_additive
      "Additive monoid homomorphism between the function spaces `I → α` and `I → β`,\ninduced by an additive monoid homomorphism `f` between `α` and `β`",
  simps]
protected def MonoidHom.compLeft {α β : Type _} [MulOneClass α] [MulOneClass β] (f : α →* β)
    (I : Type _) : (I → α) →* I → β where
  toFun h := f ∘ h
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp
#align monoid_hom.comp_left MonoidHom.compLeft
-/

end MonoidHom

section Single

variable [DecidableEq I]

open Pi

variable (f)

#print OneHom.single /-
/-- The one-preserving homomorphism including a single value
into a dependent family of values, as functions supported at a point.

This is the `one_hom` version of `pi.mul_single`. -/
@[to_additive ZeroHom.single
      "The zero-preserving homomorphism including a single value\ninto a dependent family of values, as functions supported at a point.\n\nThis is the `zero_hom` version of `pi.single`."]
def OneHom.single [∀ i, One <| f i] (i : I) : OneHom (f i) (∀ i, f i)
    where
  toFun := mulSingle i
  map_one' := mulSingle_one i
#align one_hom.single OneHom.single
-/

#print OneHom.single_apply /-
@[simp, to_additive]
theorem OneHom.single_apply [∀ i, One <| f i] (i : I) (x : f i) :
    OneHom.single f i x = mulSingle i x :=
  rfl
#align one_hom.single_apply OneHom.single_apply
-/

#print MonoidHom.single /-
/-- The monoid homomorphism including a single monoid into a dependent family of additive monoids,
as functions supported at a point.

This is the `monoid_hom` version of `pi.mul_single`. -/
@[to_additive
      "The additive monoid homomorphism including a single additive\nmonoid into a dependent family of additive monoids, as functions supported at a point.\n\nThis is the `add_monoid_hom` version of `pi.single`."]
def MonoidHom.single [∀ i, MulOneClass <| f i] (i : I) : f i →* ∀ i, f i :=
  { OneHom.single f i with map_mul' := mulSingle_op₂ (fun _ => (· * ·)) (fun _ => one_mul _) _ }
#align monoid_hom.single MonoidHom.single
-/

/- warning: monoid_hom.single_apply -> MonoidHom.single_apply is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} (f : I -> Type.{u2}) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (i : I) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (coeFn.{max (succ (max u1 u2)) (succ u2), max (succ u2) (succ (max u1 u2))} (MonoidHom.{u2, max u1 u2} (f i) (forall (i : I), f i) ((fun (i : I) => _inst_2 i) i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (fun (_x : MonoidHom.{u2, max u1 u2} (f i) (forall (i : I), f i) ((fun (i : I) => _inst_2 i) i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) => (f i) -> (forall (i : I), f i)) (MonoidHom.hasCoeToFun.{u2, max u1 u2} (f i) (forall (i : I), f i) ((fun (i : I) => _inst_2 i) i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => (fun (i : I) => _inst_2 i) i))) (MonoidHom.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i) x) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i x)
but is expected to have type
  forall {I : Type.{u1}} (f : I -> Type.{u2}) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (i : I) (x : f i), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : f i) => forall (i : I), f i) x) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (MonoidHom.{u2, max u1 u2} (f i) (forall (i : I), f i) (_inst_2 i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (f i) (fun (_x : f i) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : f i) => forall (i : I), f i) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (MonoidHom.{u2, max u1 u2} (f i) (forall (i : I), f i) (_inst_2 i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (f i) (forall (i : I), f i) (MulOneClass.toMul.{u2} (f i) (_inst_2 i)) (MulOneClass.toMul.{max u1 u2} (forall (i : I), f i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (MonoidHom.{u2, max u1 u2} (f i) (forall (i : I), f i) (_inst_2 i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))) (f i) (forall (i : I), f i) (_inst_2 i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i)) (MonoidHom.monoidHomClass.{u2, max u1 u2} (f i) (forall (i : I), f i) (_inst_2 i) (Pi.mulOneClass.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => _inst_2 i))))) (MonoidHom.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => _inst_2 i) i) x) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i x)
Case conversion may be inaccurate. Consider using '#align monoid_hom.single_apply MonoidHom.single_applyₓ'. -/
@[simp, to_additive]
theorem MonoidHom.single_apply [∀ i, MulOneClass <| f i] (i : I) (x : f i) :
    MonoidHom.single f i x = mulSingle i x :=
  rfl
#align monoid_hom.single_apply MonoidHom.single_apply

/- warning: mul_hom.single -> MulHom.single is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} (f : I -> Type.{u2}) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulZeroClass.{u2} (f i)] (i : I), MulHom.{u2, max u1 u2} (f i) (forall (i : I), f i) (MulZeroClass.toHasMul.{u2} (f i) (_inst_2 i)) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulZeroClass.toHasMul.{u2} (f i) (_inst_2 i)))
but is expected to have type
  forall {I : Type.{u1}} (f : I -> Type.{u2}) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulZeroClass.{u2} (f i)] (i : I), MulHom.{u2, max u1 u2} (f i) (forall (i : I), f i) (MulZeroClass.toMul.{u2} (f i) (_inst_2 i)) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulZeroClass.toMul.{u2} (f i) (_inst_2 i)))
Case conversion may be inaccurate. Consider using '#align mul_hom.single MulHom.singleₓ'. -/
/-- The multiplicative homomorphism including a single `mul_zero_class`
into a dependent family of `mul_zero_class`es, as functions supported at a point.

This is the `mul_hom` version of `pi.single`. -/
@[simps]
def MulHom.single [∀ i, MulZeroClass <| f i] (i : I) : f i →ₙ* ∀ i, f i
    where
  toFun := single i
  map_mul' := Pi.single_op₂ (fun _ => (· * ·)) (fun _ => zero_mul _) _
#align mul_hom.single MulHom.single

variable {f}

/- warning: pi.mul_single_mul -> Pi.mulSingle_mul is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i (HMul.hMul.{u2, u2, u2} (f i) (f i) (f i) (instHMul.{u2} (f i) (MulOneClass.toHasMul.{u2} (f i) (_inst_2 i))) x y)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHMul.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toHasMul.{u2} (f i) (_inst_2 i)))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i x) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i y))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i (HMul.hMul.{u2, u2, u2} (f i) (f i) (f i) (instHMul.{u2} (f i) (MulOneClass.toMul.{u2} (f i) (_inst_2 i))) x y)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHMul.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toMul.{u2} (f i) (_inst_2 i)))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i x) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i y))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_mul Pi.mulSingle_mulₓ'. -/
@[to_additive]
theorem Pi.mulSingle_mul [∀ i, MulOneClass <| f i] (i : I) (x y : f i) :
    mulSingle i (x * y) = mulSingle i x * mulSingle i y :=
  (MonoidHom.single f i).map_mul x y
#align pi.mul_single_mul Pi.mulSingle_mul

/- warning: pi.mul_single_inv -> Pi.mulSingle_inv is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (i : I) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i (Inv.inv.{u2} (f i) (DivInvMonoid.toHasInv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))) x)) (Inv.inv.{max u1 u2} (forall (i : I), f i) (Pi.instInv.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => DivInvMonoid.toHasInv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i)))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i x))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (i : I) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i (Inv.inv.{u2} (f i) (InvOneClass.toInv.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) x)) (Inv.inv.{max u2 u1} (forall (i : I), f i) (Pi.instInv.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => InvOneClass.toInv.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i)))))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i x))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_inv Pi.mulSingle_invₓ'. -/
@[to_additive]
theorem Pi.mulSingle_inv [∀ i, Group <| f i] (i : I) (x : f i) :
    mulSingle i x⁻¹ = (mulSingle i x)⁻¹ :=
  (MonoidHom.single f i).map_inv x
#align pi.mul_single_inv Pi.mulSingle_inv

/- warning: pi.single_div -> Pi.single_div is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i (HDiv.hDiv.{u2, u2, u2} (f i) (f i) (f i) (instHDiv.{u2} (f i) (DivInvMonoid.toHasDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i)))) x y)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHDiv.{max u1 u2} (forall (i : I), f i) (Pi.instDiv.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => DivInvMonoid.toHasDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i x) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i y))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i (HDiv.hDiv.{u2, u2, u2} (f i) (f i) (f i) (instHDiv.{u2} (f i) (DivInvMonoid.toDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i)))) x y)) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHDiv.{max u1 u2} (forall (i : I), f i) (Pi.instDiv.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => DivInvMonoid.toDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i x) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i y))
Case conversion may be inaccurate. Consider using '#align pi.single_div Pi.single_divₓ'. -/
@[to_additive]
theorem Pi.single_div [∀ i, Group <| f i] (i : I) (x y : f i) :
    mulSingle i (x / y) = mulSingle i x / mulSingle i y :=
  (MonoidHom.single f i).map_div x y
#align pi.single_div Pi.single_div

/- warning: pi.single_mul -> Pi.single_mul is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulZeroClass.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (_inst_2 i)) i (HMul.hMul.{u2, u2, u2} (f i) (f i) (f i) (instHMul.{u2} (f i) (MulZeroClass.toHasMul.{u2} (f i) (_inst_2 i))) x y)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHMul.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulZeroClass.toHasMul.{u2} (f i) (_inst_2 i)))) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (_inst_2 i)) i x) (Pi.single.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toHasZero.{u2} (f i) (_inst_2 i)) i y))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulZeroClass.{u2} (f i)] (i : I) (x : f i) (y : f i), Eq.{max (succ u1) (succ u2)} (forall (i : I), f i) (Pi.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toZero.{u2} (f i) (_inst_2 i)) i (HMul.hMul.{u2, u2, u2} (f i) (f i) (f i) (instHMul.{u2} (f i) (MulZeroClass.toMul.{u2} (f i) (_inst_2 i))) x y)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (i : I), f i) (forall (i : I), f i) (forall (i : I), f i) (instHMul.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulZeroClass.toMul.{u2} (f i) (_inst_2 i)))) (Pi.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toZero.{u2} (f i) (_inst_2 i)) i x) (Pi.single.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulZeroClass.toZero.{u2} (f i) (_inst_2 i)) i y))
Case conversion may be inaccurate. Consider using '#align pi.single_mul Pi.single_mulₓ'. -/
theorem Pi.single_mul [∀ i, MulZeroClass <| f i] (i : I) (x y : f i) :
    single i (x * y) = single i x * single i y :=
  (MulHom.single f i).map_mul x y
#align pi.single_mul Pi.single_mul

/- warning: pi.mul_single_commute -> Pi.mulSingle_commute is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)], Pairwise.{u1} I (fun (i : I) (j : I) => forall (x : f i) (y : f j), Commute.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toHasMul.{u2} (f i) (_inst_2 i))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i x) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) j y))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)], Pairwise.{u1} I (fun (i : I) (j : I) => forall (x : f i) (y : f j), Commute.{max u2 u1} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toMul.{u2} (f i) (_inst_2 i))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i x) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) j y))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_commute Pi.mulSingle_commuteₓ'. -/
/-- The injection into a pi group at different indices commutes.

For injections of commuting elements at the same index, see `commute.map` -/
@[to_additive
      "The injection into an additive pi group at different indices commutes.\n\nFor injections of commuting elements at the same index, see `add_commute.map`"]
theorem Pi.mulSingle_commute [∀ i, MulOneClass <| f i] :
    Pairwise fun i j => ∀ (x : f i) (y : f j), Commute (mulSingle i x) (mulSingle j y) :=
  by
  intro i j hij x y; ext k
  by_cases h1 : i = k;
  · subst h1
    simp [hij]
  by_cases h2 : j = k;
  · subst h2
    simp [hij]
  simp [h1, h2]
#align pi.mul_single_commute Pi.mulSingle_commute

/- warning: pi.mul_single_apply_commute -> Pi.mulSingle_apply_commute is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (x : forall (i : I), f i) (i : I) (j : I), Commute.{max u1 u2} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toHasMul.{u2} (f i) (_inst_2 i))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) i (x i)) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (_inst_2 i)) j (x j))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), MulOneClass.{u2} (f i)] (x : forall (i : I), f i) (i : I) (j : I), Commute.{max u2 u1} (forall (i : I), f i) (Pi.instMul.{u1, u2} I (fun (i : I) => f i) (fun (i : I) => MulOneClass.toMul.{u2} (f i) (_inst_2 i))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) i (x i)) (Pi.mulSingle.{u1, u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toOne.{u2} (f i) (_inst_2 i)) j (x j))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_apply_commute Pi.mulSingle_apply_commuteₓ'. -/
/-- The injection into a pi group with the same values commutes. -/
@[to_additive "The injection into an additive pi group with the same values commutes."]
theorem Pi.mulSingle_apply_commute [∀ i, MulOneClass <| f i] (x : ∀ i, f i) (i j : I) :
    Commute (mulSingle i (x i)) (mulSingle j (x j)) :=
  by
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · exact Pi.mulSingle_commute hij _ _
#align pi.mul_single_apply_commute Pi.mulSingle_apply_commute

/- warning: pi.update_eq_div_mul_single -> Pi.update_eq_div_mul_mulSingle is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} {f : I -> Type.{u2}} (i : I) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (g : forall (i : I), f i) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (a : I), f a) (Function.update.{succ u1, succ u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) g i x) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (a : I), f a) (forall (a : I), f a) (forall (a : I), f a) (instHMul.{max u1 u2} (forall (a : I), f a) (Pi.instMul.{u1, u2} I (fun (a : I) => f a) (fun (i : I) => MulOneClass.toHasMul.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))))) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (forall (a : I), f a) (forall (a : I), f a) (forall (a : I), f a) (instHDiv.{max u1 u2} (forall (a : I), f a) (Pi.instDiv.{u1, u2} I (fun (a : I) => f a) (fun (i : I) => DivInvMonoid.toHasDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) g (Pi.mulSingle.{u1, u2} I (fun (a : I) => f a) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i (g i))) (Pi.mulSingle.{u1, u2} I (fun (a : I) => f a) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) i x))
but is expected to have type
  forall {I : Type.{u1}} {f : I -> Type.{u2}} (i : I) [_inst_1 : DecidableEq.{succ u1} I] [_inst_2 : forall (i : I), Group.{u2} (f i)] (g : forall (i : I), f i) (x : f i), Eq.{max (succ u1) (succ u2)} (forall (a : I), f a) (Function.update.{succ u1, succ u2} I (fun (i : I) => f i) (fun (a : I) (b : I) => _inst_1 a b) g i x) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (forall (a : I), f a) (forall (a : I), f a) (forall (a : I), f a) (instHMul.{max u1 u2} (forall (a : I), f a) (Pi.instMul.{u1, u2} I (fun (a : I) => f a) (fun (i : I) => MulOneClass.toMul.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))))) (HDiv.hDiv.{max u1 u2, max u1 u2, max u1 u2} (forall (a : I), f a) (forall (a : I), f a) (forall (a : I), f a) (instHDiv.{max u1 u2} (forall (a : I), f a) (Pi.instDiv.{u1, u2} I (fun (a : I) => f a) (fun (i : I) => DivInvMonoid.toDiv.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_2 i))))) g (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i (g i))) (Pi.mulSingle.{u1, u2} I f (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => InvOneClass.toOne.{u2} (f i) (DivInvOneMonoid.toInvOneClass.{u2} (f i) (DivisionMonoid.toDivInvOneMonoid.{u2} (f i) (Group.toDivisionMonoid.{u2} (f i) (_inst_2 i))))) i x))
Case conversion may be inaccurate. Consider using '#align pi.update_eq_div_mul_single Pi.update_eq_div_mul_mulSingleₓ'. -/
@[to_additive update_eq_sub_add_single]
theorem Pi.update_eq_div_mul_mulSingle [∀ i, Group <| f i] (g : ∀ i : I, f i) (x : f i) :
    Function.update g i x = g / mulSingle i (g i) * mulSingle i x :=
  by
  ext j
  rcases eq_or_ne i j with (rfl | h)
  · simp
  · simp [Function.update_noteq h.symm, h]
#align pi.update_eq_div_mul_single Pi.update_eq_div_mul_mulSingle

/- warning: pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single -> Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle is a dubious translation:
lean 3 declaration is
  forall {I : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} I] {M : Type.{u2}} [_inst_2 : CommMonoid.{u2} M] {k : I} {l : I} {m : I} {n : I} {u : M} {v : M}, (Ne.{succ u2} M u (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))))) -> (Ne.{succ u2} M v (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))))) -> (Iff (Eq.{succ (max u1 u2)} (I -> M) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (I -> M) (I -> M) (I -> M) (instHMul.{max u1 u2} (I -> M) (Pi.instMul.{u1, u2} I (fun (i : I) => M) (fun (i : I) => MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))) (Pi.mulSingle.{u1, u2} I (fun {k : I} => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) k u) (Pi.mulSingle.{u1, u2} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) l v)) (HMul.hMul.{max u1 u2, max u1 u2, max u1 u2} (I -> M) (I -> M) (I -> M) (instHMul.{max u1 u2} (I -> M) (Pi.instMul.{u1, u2} I (fun (i : I) => M) (fun (i : I) => MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))) (Pi.mulSingle.{u1, u2} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) m u) (Pi.mulSingle.{u1, u2} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))) n v))) (Or (And (Eq.{succ u1} I k m) (Eq.{succ u1} I l n)) (Or (And (Eq.{succ u2} M u v) (And (Eq.{succ u1} I k n) (Eq.{succ u1} I l m))) (And (Eq.{succ u2} M (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toHasMul.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2)))) u v) (OfNat.ofNat.{u2} M 1 (OfNat.mk.{u2} M 1 (One.one.{u2} M (MulOneClass.toHasOne.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_2))))))) (And (Eq.{succ u1} I k l) (Eq.{succ u1} I m n))))))
but is expected to have type
  forall {I : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} I] {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] {k : I} {l : I} {m : I} {n : I} {u : M} {v : M}, (Ne.{succ u1} M u (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) -> (Ne.{succ u1} M v (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) -> (Iff (Eq.{succ (max u2 u1)} (I -> M) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (I -> M) (I -> M) (I -> M) (instHMul.{max u2 u1} (I -> M) (Pi.instMul.{u2, u1} I (fun (i : I) => M) (fun (i : I) => MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) (Pi.mulSingle.{u2, u1} I (fun (k : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) k u) (Pi.mulSingle.{u2, u1} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) l v)) (HMul.hMul.{max u2 u1, max u2 u1, max u2 u1} (I -> M) (I -> M) (I -> M) (instHMul.{max u2 u1} (I -> M) (Pi.instMul.{u2, u1} I (fun (i : I) => M) (fun (i : I) => MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) (Pi.mulSingle.{u2, u1} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) m u) (Pi.mulSingle.{u2, u1} I (fun (i : I) => M) (fun (a : I) (b : I) => _inst_1 a b) (fun (i : I) => Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) n v))) (Or (And (Eq.{succ u2} I k m) (Eq.{succ u2} I l n)) (Or (And (Eq.{succ u1} M u v) (And (Eq.{succ u2} I k n) (Eq.{succ u2} I l m))) (And (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) u v) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))))) (And (Eq.{succ u2} I k l) (Eq.{succ u2} I m n))))))
Case conversion may be inaccurate. Consider using '#align pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingleₓ'. -/
@[to_additive Pi.single_add_single_eq_single_add_single]
theorem Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle {M : Type _} [CommMonoid M]
    {k l m n : I} {u v : M} (hu : u ≠ 1) (hv : v ≠ 1) :
    mulSingle k u * mulSingle l v = mulSingle m u * mulSingle n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u * v = 1 ∧ k = l ∧ m = n :=
  by
  refine' ⟨fun h => _, _⟩
  · have hk := congr_fun h k
    have hl := congr_fun h l
    have hm := (congr_fun h m).symm
    have hn := (congr_fun h n).symm
    simp only [mul_apply, mul_single_apply, if_pos rfl] at hk hl hm hn
    rcases eq_or_ne k m with (rfl | hkm)
    · refine' Or.inl ⟨rfl, not_ne_iff.mp fun hln => (hv _).elim⟩
      rcases eq_or_ne k l with (rfl | hkl)
      · rwa [if_neg hln.symm, if_neg hln.symm, one_mul, one_mul] at hn
      · rwa [if_neg hkl.symm, if_neg hln, one_mul, one_mul] at hl
    · rcases eq_or_ne m n with (rfl | hmn)
      · rcases eq_or_ne k l with (rfl | hkl)
        · rw [if_neg hkm.symm, if_neg hkm.symm, one_mul, if_pos rfl] at hm
          exact Or.inr (Or.inr ⟨hm, rfl, rfl⟩)
        · simpa only [if_neg hkm, if_neg hkl, mul_one] using hk
      · rw [if_neg hkm.symm, if_neg hmn, one_mul, mul_one] at hm
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hm.symm hu)).1
        rw [if_neg hkm, if_neg hkm, one_mul, mul_one] at hk
        obtain rfl := (ite_ne_right_iff.mp (ne_of_eq_of_ne hk.symm hu)).1
        exact Or.inr (Or.inl ⟨hk.trans (if_pos rfl), rfl, rfl⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · rfl
    · apply mul_comm
    · simp_rw [← Pi.mulSingle_mul, h, mul_single_one]
#align
  pi.mul_single_mul_mul_single_eq_mul_single_mul_mul_single Pi.mulSingle_mul_mulSingle_eq_mulSingle_mul_mulSingle

end Single

namespace Function

#print Function.update_one /-
@[simp, to_additive]
theorem update_one [∀ i, One (f i)] [DecidableEq I] (i : I) : update (1 : ∀ i, f i) i 1 = 1 :=
  update_eq_self i 1
#align function.update_one Function.update_one
-/

#print Function.update_mul /-
@[to_additive]
theorem update_mul [∀ i, Mul (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ * f₂) i (x₁ * x₂) = update f₁ i x₁ * update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· * ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_mul Function.update_mul
-/

#print Function.update_inv /-
@[to_additive]
theorem update_inv [∀ i, Inv (f i)] [DecidableEq I] (f₁ : ∀ i, f i) (i : I) (x₁ : f i) :
    update f₁⁻¹ i x₁⁻¹ = (update f₁ i x₁)⁻¹ :=
  funext fun j => (apply_update (fun i => Inv.inv) f₁ i x₁ j).symm
#align function.update_inv Function.update_inv
-/

#print Function.update_div /-
@[to_additive]
theorem update_div [∀ i, Div (f i)] [DecidableEq I] (f₁ f₂ : ∀ i, f i) (i : I) (x₁ : f i)
    (x₂ : f i) : update (f₁ / f₂) i (x₁ / x₂) = update f₁ i x₁ / update f₂ i x₂ :=
  funext fun j => (apply_update₂ (fun i => (· / ·)) f₁ f₂ i x₁ x₂ j).symm
#align function.update_div Function.update_div
-/

variable [One α] [Nonempty ι] {a : α}

/- warning: function.const_eq_one -> Function.const_eq_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : Nonempty.{succ u1} ι] {a : α}, Iff (Eq.{max (succ u1) (succ u2)} (ι -> α) (Function.const.{succ u2, succ u1} α ι a) (OfNat.ofNat.{max u1 u2} (ι -> α) 1 (OfNat.mk.{max u1 u2} (ι -> α) 1 (One.one.{max u1 u2} (ι -> α) (Pi.instOne.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => _inst_1)))))) (Eq.{succ u2} α a (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α _inst_1))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : Nonempty.{succ u2} ι] {a : α}, Iff (Eq.{max (succ u2) (succ u1)} (ι -> α) (Function.const.{succ u1, succ u2} α ι a) (OfNat.ofNat.{max u2 u1} (ι -> α) 1 (One.toOfNat1.{max u2 u1} (ι -> α) (Pi.instOne.{u2, u1} ι (fun (a._@.Init.Prelude._hyg.54 : ι) => α) (fun (i : ι) => _inst_1))))) (Eq.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.const_eq_one Function.const_eq_oneₓ'. -/
@[simp, to_additive]
theorem const_eq_one : const ι a = 1 ↔ a = 1 :=
  @const_inj _ _ _ _ 1
#align function.const_eq_one Function.const_eq_one

/- warning: function.const_ne_one -> Function.const_ne_one is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : Type.{u2}} [_inst_1 : One.{u2} α] [_inst_2 : Nonempty.{succ u1} ι] {a : α}, Iff (Ne.{max (succ u1) (succ u2)} (ι -> α) (Function.const.{succ u2, succ u1} α ι a) (OfNat.ofNat.{max u1 u2} (ι -> α) 1 (OfNat.mk.{max u1 u2} (ι -> α) 1 (One.one.{max u1 u2} (ι -> α) (Pi.instOne.{u1, u2} ι (fun (ᾰ : ι) => α) (fun (i : ι) => _inst_1)))))) (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 1 (OfNat.mk.{u2} α 1 (One.one.{u2} α _inst_1))))
but is expected to have type
  forall {ι : Type.{u2}} {α : Type.{u1}} [_inst_1 : One.{u1} α] [_inst_2 : Nonempty.{succ u2} ι] {a : α}, Iff (Ne.{max (succ u2) (succ u1)} (ι -> α) (Function.const.{succ u1, succ u2} α ι a) (OfNat.ofNat.{max u2 u1} (ι -> α) 1 (One.toOfNat1.{max u2 u1} (ι -> α) (Pi.instOne.{u2, u1} ι (fun (a._@.Init.Prelude._hyg.54 : ι) => α) (fun (i : ι) => _inst_1))))) (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align function.const_ne_one Function.const_ne_oneₓ'. -/
@[to_additive]
theorem const_ne_one : const ι a ≠ 1 ↔ a ≠ 1 :=
  const_eq_one.Not
#align function.const_ne_one Function.const_ne_one

end Function

section Piecewise

#print Set.piecewise_mul /-
@[to_additive]
theorem Set.piecewise_mul [∀ i, Mul (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ * f₂) (g₁ * g₂) = s.piecewise f₁ g₁ * s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· * ·)
#align set.piecewise_mul Set.piecewise_mul
-/

#print Set.piecewise_inv /-
@[to_additive]
theorem Set.piecewise_inv [∀ i, Inv (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)] (f₁ g₁ : ∀ i, f i) :
    s.piecewise f₁⁻¹ g₁⁻¹ = (s.piecewise f₁ g₁)⁻¹ :=
  s.piecewise_op f₁ g₁ fun _ x => x⁻¹
#align set.piecewise_inv Set.piecewise_inv
-/

#print Set.piecewise_div /-
@[to_additive]
theorem Set.piecewise_div [∀ i, Div (f i)] (s : Set I) [∀ i, Decidable (i ∈ s)]
    (f₁ f₂ g₁ g₂ : ∀ i, f i) :
    s.piecewise (f₁ / f₂) (g₁ / g₂) = s.piecewise f₁ g₁ / s.piecewise f₂ g₂ :=
  s.piecewise_op₂ _ _ _ _ fun _ => (· / ·)
#align set.piecewise_div Set.piecewise_div
-/

end Piecewise

section Extend

variable {η : Type v} (R : Type w) (s : ι → η)

#print Function.ExtendByOne.hom /-
/-- `function.extend s f 1` as a bundled hom. -/
@[to_additive Function.ExtendByZero.hom "`function.extend s f 0` as a bundled hom.", simps]
noncomputable def Function.ExtendByOne.hom [MulOneClass R] : (ι → R) →* η → R
    where
  toFun f := Function.extend s f 1
  map_one' := Function.extend_one s
  map_mul' f g := by simpa using Function.extend_mul s f g 1 1
#align function.extend_by_one.hom Function.ExtendByOne.hom
-/

end Extend

