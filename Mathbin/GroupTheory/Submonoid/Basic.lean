/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.submonoid.basic
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Group.Units
import Mathbin.GroupTheory.Subsemigroup.Basic

/-!
# Submonoids: definition and `complete_lattice` structure

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines bundled multiplicative and additive submonoids. We also define
a `complete_lattice` structure on `submonoid`s, define the closure of a set as the minimal submonoid
that includes this set, and prove a few results about extending properties from a dense set (i.e.
a set with `closure s = ⊤`) to the whole monoid, see `submonoid.dense_induction` and
`monoid_hom.of_mclosure_eq_top_left`/`monoid_hom.of_mclosure_eq_top_right`.

## Main definitions

* `submonoid M`: the type of bundled submonoids of a monoid `M`; the underlying set is given in
  the `carrier` field of the structure, and should be accessed through coercion as in `(S : set M)`.
* `add_submonoid M` : the type of bundled submonoids of an additive monoid `M`.

For each of the following definitions in the `submonoid` namespace, there is a corresponding
definition in the `add_submonoid` namespace.

* `submonoid.copy` : copy of a submonoid with `carrier` replaced by a set that is equal but possibly
  not definitionally equal to the carrier of the original `submonoid`.
* `submonoid.closure` :  monoid closure of a set, i.e., the least submonoid that includes the set.
* `submonoid.gi` : `closure : set M → submonoid M` and coercion `coe : submonoid M → set M`
  form a `galois_insertion`;
* `monoid_hom.eq_mlocus`: the submonoid of elements `x : M` such that `f x = g x`;
* `monoid_hom.of_mclosure_eq_top_right`:  if a map `f : M → N` between two monoids satisfies
  `f 1 = 1` and `f (x * y) = f x * f y` for `y` from some dense set `s`, then `f` is a monoid
  homomorphism. E.g., if `f : ℕ → M` satisfies `f 0 = 0` and `f (x + 1) = f x + f 1`, then `f` is
  an additive monoid homomorphism.

## Implementation notes

Submonoid inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a submonoid's underlying set.

Note that `submonoid M` does not actually require `monoid M`, instead requiring only the weaker
`mul_one_class M`.

This file is designed to have very few dependencies. In particular, it should not use natural
numbers. `submonoid` is implemented by extending `subsemigroup` requiring `one_mem'`.

## Tags
submonoid, submonoids
-/


-- Only needed for notation
-- Only needed for notation
variable {M : Type _} {N : Type _}

variable {A : Type _}

section NonAssoc

variable [MulOneClass M] {s : Set M}

variable [AddZeroClass A] {t : Set A}

#print OneMemClass /-
/-- `one_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `1 ∈ s` for all `s`. -/
class OneMemClass (S : Type _) (M : outParam <| Type _) [One M] [SetLike S M] : Prop where
  one_mem : ∀ s : S, (1 : M) ∈ s
#align one_mem_class OneMemClass
-/

export OneMemClass (one_mem)

#print ZeroMemClass /-
/-- `zero_mem_class S M` says `S` is a type of subsets `s ≤ M`, such that `0 ∈ s` for all `s`. -/
class ZeroMemClass (S : Type _) (M : outParam <| Type _) [Zero M] [SetLike S M] : Prop where
  zero_mem : ∀ s : S, (0 : M) ∈ s
#align zero_mem_class ZeroMemClass
-/

export ZeroMemClass (zero_mem)

attribute [to_additive] OneMemClass

section

#print Submonoid /-
/-- A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication. -/
structure Submonoid (M : Type _) [MulOneClass M] extends Subsemigroup M where
  one_mem' : (1 : M) ∈ carrier
#align submonoid Submonoid
-/

end

/-- A submonoid of a monoid `M` can be considered as a subsemigroup of that monoid. -/
add_decl_doc Submonoid.toSubsemigroup

#print SubmonoidClass /-
/-- `submonoid_class S M` says `S` is a type of subsets `s ≤ M` that contain `1`
and are closed under `(*)` -/
class SubmonoidClass (S : Type _) (M : outParam <| Type _) [MulOneClass M] [SetLike S M] extends
  MulMemClass S M, OneMemClass S M : Prop
#align submonoid_class SubmonoidClass
-/

section

#print AddSubmonoid /-
/-- An additive submonoid of an additive monoid `M` is a subset containing 0 and
  closed under addition. -/
structure AddSubmonoid (M : Type _) [AddZeroClass M] extends AddSubsemigroup M where
  zero_mem' : (0 : M) ∈ carrier
#align add_submonoid AddSubmonoid
-/

end

/-- An additive submonoid of an additive monoid `M` can be considered as an
additive subsemigroup of that additive monoid. -/
add_decl_doc AddSubmonoid.toAddSubsemigroup

#print AddSubmonoidClass /-
/-- `add_submonoid_class S M` says `S` is a type of subsets `s ≤ M` that contain `0`
and are closed under `(+)` -/
class AddSubmonoidClass (S : Type _) (M : outParam <| Type _) [AddZeroClass M] [SetLike S M] extends
  AddMemClass S M, ZeroMemClass S M : Prop
#align add_submonoid_class AddSubmonoidClass
-/

attribute [to_additive] Submonoid SubmonoidClass

/- warning: pow_mem -> pow_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_3 : Monoid.{u1} M] {A : Type.{u2}} [_inst_4 : SetLike.{u2, u1} A M] [_inst_5 : SubmonoidClass.{u2, u1} A M (Monoid.toMulOneClass.{u1} M _inst_3) _inst_4] {S : A} {x : M}, (Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_4) x S) -> (forall (n : Nat), Membership.Mem.{u1, u2} M A (SetLike.hasMem.{u2, u1} A M _inst_4) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_3)) x n) S)
but is expected to have type
  forall {M : Type.{u2}} {_inst_3 : Type.{u1}} [A : Monoid.{u2} M] [_inst_4 : SetLike.{u1, u2} _inst_3 M] [_inst_5 : SubmonoidClass.{u1, u2} _inst_3 M (Monoid.toMulOneClass.{u2} M A) _inst_4] {S : _inst_3} {x : M}, (Membership.mem.{u2, u1} M _inst_3 (SetLike.instMembership.{u1, u2} _inst_3 M _inst_4) x S) -> (forall (n : Nat), Membership.mem.{u2, u1} M _inst_3 (SetLike.instMembership.{u1, u2} _inst_3 M _inst_4) (HPow.hPow.{u2, 0, u2} M Nat M (instHPow.{u2, 0} M Nat (Monoid.Pow.{u2} M A)) x n) S)
Case conversion may be inaccurate. Consider using '#align pow_mem pow_memₓ'. -/
@[to_additive]
theorem pow_mem {M} [Monoid M] {A : Type _} [SetLike A M] [SubmonoidClass A M] {S : A} {x : M}
    (hx : x ∈ S) : ∀ n : ℕ, x ^ n ∈ S
  | 0 => by
    rw [pow_zero]
    exact OneMemClass.one_mem S
  | n + 1 => by
    rw [pow_succ]
    exact MulMemClass.mul_mem hx (pow_mem n)
#align pow_mem pow_mem

namespace Submonoid

@[to_additive]
instance : SetLike (Submonoid M) M
    where
  coe := Submonoid.carrier
  coe_injective' p q h := by cases p <;> cases q <;> congr

@[to_additive]
instance : SubmonoidClass (Submonoid M) M
    where
  one_mem := Submonoid.one_mem'
  mul_mem := Submonoid.mul_mem'

#print Submonoid.Simps.coe /-
/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection]"]
def Simps.coe (S : Submonoid M) : Set M :=
  S
#align submonoid.simps.coe Submonoid.Simps.coe
#align add_submonoid.simps.coe AddSubmonoid.Simps.coe
-/

initialize_simps_projections Submonoid (carrier → coe)

initialize_simps_projections AddSubmonoid (carrier → coe)

/- warning: submonoid.mem_carrier -> Submonoid.mem_carrier is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Submonoid.{u1} M _inst_1} {x : M}, Iff (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x (Submonoid.carrier.{u1} M _inst_1 s)) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x s)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Submonoid.{u1} M _inst_1} {x : M}, Iff (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (Subsemigroup.carrier.{u1} M (MulOneClass.toMul.{u1} M _inst_1) (Submonoid.toSubsemigroup.{u1} M _inst_1 s))) (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s)
Case conversion may be inaccurate. Consider using '#align submonoid.mem_carrier Submonoid.mem_carrierₓ'. -/
@[simp, to_additive]
theorem mem_carrier {s : Submonoid M} {x : M} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_carrier Submonoid.mem_carrier
#align add_submonoid.mem_carrier AddSubmonoid.mem_carrier

/- warning: submonoid.mem_mk -> Submonoid.mem_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {x : M} (h_one : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) s)) (h_mul : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) s), Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.mk.{u1} M _inst_1 s h_one h_mul)) (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {x : M} (h_one : s (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (h_mul : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) s)), Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.mk.{u1} M _inst_1 (Subsemigroup.mk.{u1} M (MulOneClass.toMul.{u1} M _inst_1) s h_mul) h_one)) (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s)
Case conversion may be inaccurate. Consider using '#align submonoid.mem_mk Submonoid.mem_mkₓ'. -/
@[simp, to_additive]
theorem mem_mk {s : Set M} {x : M} (h_one) (h_mul) : x ∈ mk s h_one h_mul ↔ x ∈ s :=
  Iff.rfl
#align submonoid.mem_mk Submonoid.mem_mk
#align add_submonoid.mem_mk AddSubmonoid.mem_mk

/- warning: submonoid.coe_set_mk -> Submonoid.coe_set_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} (h_one : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) s)) (h_mul : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) s), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.mk.{u1} M _inst_1 s h_one h_mul)) s
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} (h_one : s (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (h_mul : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) s)), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.mk.{u1} M _inst_1 (Subsemigroup.mk.{u1} M (MulOneClass.toMul.{u1} M _inst_1) s h_mul) h_one)) s
Case conversion may be inaccurate. Consider using '#align submonoid.coe_set_mk Submonoid.coe_set_mkₓ'. -/
@[simp, to_additive]
theorem coe_set_mk {s : Set M} (h_one) (h_mul) : (mk s h_one h_mul : Set M) = s :=
  rfl
#align submonoid.coe_set_mk Submonoid.coe_set_mk
#align add_submonoid.coe_set_mk AddSubmonoid.coe_set_mk

/- warning: submonoid.mk_le_mk -> Submonoid.mk_le_mk is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} (h_one : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b s) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) s)) (h_mul : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) s) (h_one' : forall {a : M} {b : M}, (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a t) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b t) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) a b) t)) (h_mul' : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) t), Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.mk.{u1} M _inst_1 s h_one h_mul) (Submonoid.mk.{u1} M _inst_1 t h_one' h_mul')) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s t)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {t : Set.{u1} M} (h_one : s (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (h_mul : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b s) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) s)) (h_one' : t (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) (h_mul' : forall {a : M} {b : M}, (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a t) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b t) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) a b) t)), Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.instPartialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)))) (Submonoid.mk.{u1} M _inst_1 (Subsemigroup.mk.{u1} M (MulOneClass.toMul.{u1} M _inst_1) s h_mul) h_one) (Submonoid.mk.{u1} M _inst_1 (Subsemigroup.mk.{u1} M (MulOneClass.toMul.{u1} M _inst_1) t h_mul') h_one')) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s t)
Case conversion may be inaccurate. Consider using '#align submonoid.mk_le_mk Submonoid.mk_le_mkₓ'. -/
@[simp, to_additive]
theorem mk_le_mk {s t : Set M} (h_one) (h_mul) (h_one') (h_mul') :
    mk s h_one h_mul ≤ mk t h_one' h_mul' ↔ s ⊆ t :=
  Iff.rfl
#align submonoid.mk_le_mk Submonoid.mk_le_mk
#align add_submonoid.mk_le_mk AddSubmonoid.mk_le_mk

/- warning: submonoid.ext -> Submonoid.ext is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (forall (x : M), Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x T)) -> (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S T)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1}, (forall (x : M), Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x T)) -> (Eq.{succ u1} (Submonoid.{u1} M _inst_1) S T)
Case conversion may be inaccurate. Consider using '#align submonoid.ext Submonoid.extₓ'. -/
/-- Two submonoids are equal if they have the same elements. -/
@[ext, to_additive "Two `add_submonoid`s are equal if they have the same elements."]
theorem ext {S T : Submonoid M} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h
#align submonoid.ext Submonoid.ext
#align add_submonoid.ext AddSubmonoid.ext

/- warning: submonoid.copy -> Submonoid.copy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (s : Set.{u1} M), (Eq.{succ u1} (Set.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)) -> (Submonoid.{u1} M _inst_1)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) (s : Set.{u1} M), (Eq.{succ u1} (Set.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) -> (Submonoid.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align submonoid.copy Submonoid.copyₓ'. -/
/-- Copy a submonoid replacing `carrier` with a set that is equal to it. -/
@[to_additive "Copy an additive submonoid replacing `carrier` with a set that is equal to it."]
protected def copy (S : Submonoid M) (s : Set M) (hs : s = S) : Submonoid M
    where
  carrier := s
  one_mem' := hs.symm ▸ S.one_mem'
  mul_mem' _ _ := hs.symm ▸ S.mul_mem'
#align submonoid.copy Submonoid.copy
#align add_submonoid.copy AddSubmonoid.copy

variable {S : Submonoid M}

/- warning: submonoid.coe_copy -> Submonoid.coe_copy is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {s : Set.{u1} M} (hs : Eq.{succ u1} (Set.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.copy.{u1} M _inst_1 S s hs)) s
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {s : Set.{u1} M} (hs : Eq.{succ u1} (Set.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.copy.{u1} M _inst_1 S s hs)) s
Case conversion may be inaccurate. Consider using '#align submonoid.coe_copy Submonoid.coe_copyₓ'. -/
@[simp, to_additive]
theorem coe_copy {s : Set M} (hs : s = S) : (S.copy s hs : Set M) = s :=
  rfl
#align submonoid.coe_copy Submonoid.coe_copy
#align add_submonoid.coe_copy AddSubmonoid.coe_copy

/- warning: submonoid.copy_eq -> Submonoid.copy_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {s : Set.{u1} M} (hs : Eq.{succ u1} (Set.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.copy.{u1} M _inst_1 S s hs) S
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {s : Set.{u1} M} (hs : Eq.{succ u1} (Set.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.copy.{u1} M _inst_1 S s hs) S
Case conversion may be inaccurate. Consider using '#align submonoid.copy_eq Submonoid.copy_eqₓ'. -/
@[to_additive]
theorem copy_eq {s : Set M} (hs : s = S) : S.copy s hs = S :=
  SetLike.coe_injective hs
#align submonoid.copy_eq Submonoid.copy_eq
#align add_submonoid.copy_eq AddSubmonoid.copy_eq

variable (S)

/- warning: submonoid.one_mem -> Submonoid.one_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) S
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) S
Case conversion may be inaccurate. Consider using '#align submonoid.one_mem Submonoid.one_memₓ'. -/
/-- A submonoid contains the monoid's 1. -/
@[to_additive "An `add_submonoid` contains the monoid's 0."]
protected theorem one_mem : (1 : M) ∈ S :=
  one_mem S
#align submonoid.one_mem Submonoid.one_mem
#align add_submonoid.zero_mem AddSubmonoid.zero_mem

/- warning: submonoid.mul_mem -> Submonoid.mul_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) {x : M} {y : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y S) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1) {x : M} {y : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y S) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) S)
Case conversion may be inaccurate. Consider using '#align submonoid.mul_mem Submonoid.mul_memₓ'. -/
/-- A submonoid is closed under multiplication. -/
@[to_additive "An `add_submonoid` is closed under addition."]
protected theorem mul_mem {x y : M} : x ∈ S → y ∈ S → x * y ∈ S :=
  mul_mem
#align submonoid.mul_mem Submonoid.mul_mem
#align add_submonoid.add_mem AddSubmonoid.add_mem

/-- The submonoid `M` of the monoid `M`. -/
@[to_additive "The additive submonoid `M` of the `add_monoid M`."]
instance : Top (Submonoid M) :=
  ⟨{  carrier := Set.univ
      one_mem' := Set.mem_univ 1
      mul_mem' := fun _ _ _ _ => Set.mem_univ _ }⟩

/-- The trivial submonoid `{1}` of an monoid `M`. -/
@[to_additive "The trivial `add_submonoid` `{0}` of an `add_monoid` `M`."]
instance : Bot (Submonoid M) :=
  ⟨{  carrier := {1}
      one_mem' := Set.mem_singleton 1
      mul_mem' := fun a b ha hb =>
        by
        simp only [Set.mem_singleton_iff] at *
        rw [ha, hb, mul_one] }⟩

@[to_additive]
instance : Inhabited (Submonoid M) :=
  ⟨⊥⟩

/- warning: submonoid.mem_bot -> Submonoid.mem_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))) (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_bot Submonoid.mem_botₓ'. -/
@[simp, to_additive]
theorem mem_bot {x : M} : x ∈ (⊥ : Submonoid M) ↔ x = 1 :=
  Set.mem_singleton_iff
#align submonoid.mem_bot Submonoid.mem_bot
#align add_submonoid.mem_bot AddSubmonoid.mem_bot

/- warning: submonoid.mem_top -> Submonoid.mem_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (x : M), Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (x : M), Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_top Submonoid.mem_topₓ'. -/
@[simp, to_additive]
theorem mem_top (x : M) : x ∈ (⊤ : Submonoid M) :=
  Set.mem_univ x
#align submonoid.mem_top Submonoid.mem_top
#align add_submonoid.mem_top AddSubmonoid.mem_top

/- warning: submonoid.coe_top -> Submonoid.coe_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) (Set.univ.{u1} M)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) (Set.univ.{u1} M)
Case conversion may be inaccurate. Consider using '#align submonoid.coe_top Submonoid.coe_topₓ'. -/
@[simp, to_additive]
theorem coe_top : ((⊤ : Submonoid M) : Set M) = Set.univ :=
  rfl
#align submonoid.coe_top Submonoid.coe_top
#align add_submonoid.coe_top AddSubmonoid.coe_top

/- warning: submonoid.coe_bot -> Submonoid.coe_bot is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_bot Submonoid.coe_botₓ'. -/
@[simp, to_additive]
theorem coe_bot : ((⊥ : Submonoid M) : Set M) = {1} :=
  rfl
#align submonoid.coe_bot Submonoid.coe_bot
#align add_submonoid.coe_bot AddSubmonoid.coe_bot

/-- The inf of two submonoids is their intersection. -/
@[to_additive "The inf of two `add_submonoid`s is their intersection."]
instance : HasInf (Submonoid M) :=
  ⟨fun S₁ S₂ =>
    { carrier := S₁ ∩ S₂
      one_mem' := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem' := fun _ _ ⟨hx, hx'⟩ ⟨hy, hy'⟩ => ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

/- warning: submonoid.coe_inf -> Submonoid.coe_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (p : Submonoid.{u1} M _inst_1) (p' : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} M) (Set.hasInter.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) p) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) p'))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (p : Submonoid.{u1} M _inst_1) (p' : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instHasInfSubmonoid.{u1} M _inst_1) p p')) (Inter.inter.{u1} (Set.{u1} M) (Set.instInterSet.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) p) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) p'))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_inf Submonoid.coe_infₓ'. -/
@[simp, to_additive]
theorem coe_inf (p p' : Submonoid M) : ((p ⊓ p' : Submonoid M) : Set M) = p ∩ p' :=
  rfl
#align submonoid.coe_inf Submonoid.coe_inf
#align add_submonoid.coe_inf AddSubmonoid.coe_inf

/- warning: submonoid.mem_inf -> Submonoid.mem_inf is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p : Submonoid.{u1} M _inst_1} {p' : Submonoid.{u1} M _inst_1} {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) p p')) (And (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p'))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p : Submonoid.{u1} M _inst_1} {p' : Submonoid.{u1} M _inst_1} {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (HasInf.inf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instHasInfSubmonoid.{u1} M _inst_1) p p')) (And (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p) (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p'))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_inf Submonoid.mem_infₓ'. -/
@[simp, to_additive]
theorem mem_inf {p p' : Submonoid M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
#align submonoid.mem_inf Submonoid.mem_inf
#align add_submonoid.mem_inf AddSubmonoid.mem_inf

@[to_additive]
instance : InfSet (Submonoid M) :=
  ⟨fun s =>
    { carrier := ⋂ t ∈ s, ↑t
      one_mem' := Set.mem_binterᵢ fun i h => i.one_mem
      mul_mem' := fun x y hx hy =>
        Set.mem_binterᵢ fun i h =>
          i.mul_mem (by apply Set.mem_interᵢ₂.1 hx i h) (by apply Set.mem_interᵢ₂.1 hy i h) }⟩

/- warning: submonoid.coe_Inf -> Submonoid.coe_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (InfSet.infₛ.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) S)) (Set.interᵢ.{u1, succ u1} M (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => Set.interᵢ.{u1, 0} M (Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) s)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Set.{u1} (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (InfSet.infₛ.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instInfSetSubmonoid.{u1} M _inst_1) S)) (Set.interᵢ.{u1, succ u1} M (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => Set.interᵢ.{u1, 0} M (Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) (fun (H : Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) => SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_Inf Submonoid.coe_infₛₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_infₛ (S : Set (Submonoid M)) : ((infₛ S : Submonoid M) : Set M) = ⋂ s ∈ S, ↑s :=
  rfl
#align submonoid.coe_Inf Submonoid.coe_infₛ
#align add_submonoid.coe_Inf AddSubmonoid.coe_infₛ

/- warning: submonoid.mem_Inf -> Submonoid.mem_infₛ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)} {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (InfSet.infₛ.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) S)) (forall (p : Submonoid.{u1} M _inst_1), (Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) p S) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)} {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (InfSet.infₛ.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instInfSetSubmonoid.{u1} M _inst_1) S)) (forall (p : Submonoid.{u1} M _inst_1), (Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) p S) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_Inf Submonoid.mem_infₛₓ'. -/
@[to_additive]
theorem mem_infₛ {S : Set (Submonoid M)} {x : M} : x ∈ infₛ S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_interᵢ₂
#align submonoid.mem_Inf Submonoid.mem_infₛ
#align add_submonoid.mem_Inf AddSubmonoid.mem_infₛ

/- warning: submonoid.mem_infi -> Submonoid.mem_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)} {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (infᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (S i))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)} {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (infᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.instInfSetSubmonoid.{u1} M _inst_1) ι (fun (i : ι) => S i))) (forall (i : ι), Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (S i))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_infi Submonoid.mem_infᵢₓ'. -/
@[to_additive]
theorem mem_infᵢ {ι : Sort _} {S : ι → Submonoid M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [infᵢ, mem_Inf, Set.forall_range_iff]
#align submonoid.mem_infi Submonoid.mem_infᵢ
#align add_submonoid.mem_infi AddSubmonoid.mem_infᵢ

/- warning: submonoid.coe_infi -> Submonoid.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)}, Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (infᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.hasInf.{u1} M _inst_1) ι (fun (i : ι) => S i))) (Set.interᵢ.{u1, u2} M ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (S i)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)}, Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (infᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (Submonoid.instInfSetSubmonoid.{u1} M _inst_1) ι (fun (i : ι) => S i))) (Set.interᵢ.{u1, u2} M ι (fun (i : ι) => SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (S i)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_infi Submonoid.coe_infᵢₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_infᵢ {ι : Sort _} {S : ι → Submonoid M} : (↑(⨅ i, S i) : Set M) = ⋂ i, S i := by
  simp only [infᵢ, coe_Inf, Set.binterᵢ_range]
#align submonoid.coe_infi Submonoid.coe_infᵢ
#align add_submonoid.coe_infi AddSubmonoid.coe_infᵢ

/-- Submonoids of a monoid form a complete lattice. -/
@[to_additive "The `add_submonoid`s of an `add_monoid` form a complete lattice."]
instance : CompleteLattice (Submonoid M) :=
  {
    completeLatticeOfInf (Submonoid M) fun s =>
      IsGLB.of_image (fun S T => show (S : Set M) ≤ T ↔ S ≤ T from SetLike.coe_subset_coe)
        isGLB_binfᵢ with
    le := (· ≤ ·)
    lt := (· < ·)
    bot := ⊥
    bot_le := fun S x hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun S x hx => mem_top x
    inf := (· ⊓ ·)
    inf := InfSet.infₛ
    le_inf := fun a b c ha hb x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun a b x => And.left
    inf_le_right := fun a b x => And.right }

#print Submonoid.subsingleton_iff /-
@[simp, to_additive]
theorem subsingleton_iff : Subsingleton (Submonoid M) ↔ Subsingleton M :=
  ⟨fun h =>
    ⟨fun x y =>
      have : ∀ i : M, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Submonoid M) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun h =>
    ⟨fun x y => Submonoid.ext fun i => Subsingleton.elim 1 i ▸ by simp [Submonoid.one_mem]⟩⟩
#align submonoid.subsingleton_iff Submonoid.subsingleton_iff
#align add_submonoid.subsingleton_iff AddSubmonoid.subsingleton_iff
-/

#print Submonoid.nontrivial_iff /-
@[simp, to_additive]
theorem nontrivial_iff : Nontrivial (Submonoid M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)
#align submonoid.nontrivial_iff Submonoid.nontrivial_iff
#align add_submonoid.nontrivial_iff AddSubmonoid.nontrivial_iff
-/

@[to_additive]
instance [Subsingleton M] : Unique (Submonoid M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩

@[to_additive]
instance [Nontrivial M] : Nontrivial (Submonoid M) :=
  nontrivial_iff.mpr ‹_›

#print Submonoid.closure /-
/-- The `submonoid` generated by a set. -/
@[to_additive "The `add_submonoid` generated by a set"]
def closure (s : Set M) : Submonoid M :=
  infₛ { S | s ⊆ S }
#align submonoid.closure Submonoid.closure
#align add_submonoid.closure AddSubmonoid.closure
-/

/- warning: submonoid.mem_closure -> Submonoid.mem_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) (forall (S : Submonoid.{u1} M _inst_1), (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) (forall (S : Submonoid.{u1} M _inst_1), (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_closure Submonoid.mem_closureₓ'. -/
@[to_additive]
theorem mem_closure {x : M} : x ∈ closure s ↔ ∀ S : Submonoid M, s ⊆ S → x ∈ S :=
  mem_Inf
#align submonoid.mem_closure Submonoid.mem_closure
#align add_submonoid.mem_closure AddSubmonoid.mem_closure

/- warning: submonoid.subset_closure -> Submonoid.subset_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M}, HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M}, HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s))
Case conversion may be inaccurate. Consider using '#align submonoid.subset_closure Submonoid.subset_closureₓ'. -/
/-- The submonoid generated by a set includes the set. -/
@[simp, to_additive "The `add_submonoid` generated by a set includes the set."]
theorem subset_closure : s ⊆ closure s := fun x hx => mem_closure.2 fun S hS => hS hx
#align submonoid.subset_closure Submonoid.subset_closure
#align add_submonoid.subset_closure AddSubmonoid.subset_closure

/- warning: submonoid.not_mem_of_not_mem_closure -> Submonoid.not_mem_of_not_mem_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {P : M}, (Not (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) P (Submonoid.closure.{u1} M _inst_1 s))) -> (Not (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) P s))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {P : M}, (Not (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) P (Submonoid.closure.{u1} M _inst_1 s))) -> (Not (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) P s))
Case conversion may be inaccurate. Consider using '#align submonoid.not_mem_of_not_mem_closure Submonoid.not_mem_of_not_mem_closureₓ'. -/
@[to_additive]
theorem not_mem_of_not_mem_closure {P : M} (hP : P ∉ closure s) : P ∉ s := fun h =>
  hP (subset_closure h)
#align submonoid.not_mem_of_not_mem_closure Submonoid.not_mem_of_not_mem_closure
#align add_submonoid.not_mem_of_not_mem_closure AddSubmonoid.not_mem_of_not_mem_closure

variable {S}

open Set

/- warning: submonoid.closure_le -> Submonoid.closure_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {S : Submonoid.{u1} M _inst_1}, Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s) S) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {S : Submonoid.{u1} M _inst_1}, Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (Submonoid.closure.{u1} M _inst_1 s) S) (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_le Submonoid.closure_leₓ'. -/
/-- A submonoid `S` includes `closure s` if and only if it includes `s`. -/
@[simp, to_additive "An additive submonoid `S` includes `closure s` if and only if it includes `s`"]
theorem closure_le : closure s ≤ S ↔ s ⊆ S :=
  ⟨Subset.trans subset_closure, fun h => infₛ_le h⟩
#align submonoid.closure_le Submonoid.closure_le
#align add_submonoid.closure_le AddSubmonoid.closure_le

/- warning: submonoid.closure_mono -> Submonoid.closure_mono is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {{s : Set.{u1} M}} {{t : Set.{u1} M}}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s t) -> (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s) (Submonoid.closure.{u1} M _inst_1 t))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {{s : Set.{u1} M}} {{t : Set.{u1} M}}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s t) -> (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (Submonoid.closure.{u1} M _inst_1 s) (Submonoid.closure.{u1} M _inst_1 t))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_mono Submonoid.closure_monoₓ'. -/
/-- Submonoid closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure s ≤ closure t`. -/
@[to_additive
      "Additive submonoid closure of a set is monotone in its argument: if `s ⊆ t`,\nthen `closure s ≤ closure t`"]
theorem closure_mono ⦃s t : Set M⦄ (h : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 <| Subset.trans h subset_closure
#align submonoid.closure_mono Submonoid.closure_mono
#align add_submonoid.closure_mono AddSubmonoid.closure_mono

/- warning: submonoid.closure_eq_of_le -> Submonoid.closure_eq_of_le is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {S : Submonoid.{u1} M _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.hasSubset.{u1} M) s ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)) -> (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S (Submonoid.closure.{u1} M _inst_1 s)) -> (Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {S : Submonoid.{u1} M _inst_1}, (HasSubset.Subset.{u1} (Set.{u1} M) (Set.instHasSubsetSet.{u1} M) s (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) -> (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) S (Submonoid.closure.{u1} M _inst_1 s)) -> (Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s) S)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_eq_of_le Submonoid.closure_eq_of_leₓ'. -/
@[to_additive]
theorem closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure s) : closure s = S :=
  le_antisymm (closure_le.2 h₁) h₂
#align submonoid.closure_eq_of_le Submonoid.closure_eq_of_le
#align add_submonoid.closure_eq_of_le AddSubmonoid.closure_eq_of_le

variable (S)

/- warning: submonoid.closure_induction -> Submonoid.closure_induction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y))) -> (p x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y))) -> (p x)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_induction Submonoid.closure_inductionₓ'. -/
/-- An induction principle for closure membership. If `p` holds for `1` and all elements of `s`, and
is preserved under multiplication, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership. If `p`\nholds for `0` and all elements of `s`, and is preserved under addition, then `p` holds for all\nelements of the additive closure of `s`."]
theorem closure_induction {p : M → Prop} {x} (h : x ∈ closure s) (Hs : ∀ x ∈ s, p x) (H1 : p 1)
    (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  (@closure_le _ _ _ ⟨p, Hmul, H1⟩).2 Hs h
#align submonoid.closure_induction Submonoid.closure_induction
#align add_submonoid.closure_induction AddSubmonoid.closure_induction

/- warning: submonoid.closure_induction' -> Submonoid.closure_induction' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u1} M) {p : forall (x : M), (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> Prop}, (forall (x : M) (h : Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s), p x (Submonoid.subset_closure.{u1} M _inst_1 s x h)) -> (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (OneMemClass.one_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toHasOne.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (SubmonoidClass.to_oneMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoidClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s))) -> (forall (x : M) (hx : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) (y : M) (hy : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y (Submonoid.closure.{u1} M _inst_1 s)), (p x hx) -> (p y hy) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) (MulMemClass.mul_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toHasMul.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (SubmonoidClass.to_mulMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoidClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s) x y hx hy))) -> (forall {x : M} (hx : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)), p x hx)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u1} M) {p : forall (x : M), (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> Prop}, (forall (x : M) (h : Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s), p x (Submonoid.subset_closure.{u1} M _inst_1 s x h)) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (OneMemClass.one_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toOne.{u1} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (SubmonoidClass.toOneMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s))) -> (forall (x : M) (hx : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) (y : M) (hy : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y (Submonoid.closure.{u1} M _inst_1 s)), (p x hx) -> (p y hy) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) (MulMemClass.mul_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toMul.{u1} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (SubmonoidClass.toMulMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u1} M _inst_1)) (Submonoid.closure.{u1} M _inst_1 s) x y hx hy))) -> (forall {x : M} (hx : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)), p x hx)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_induction' Submonoid.closure_induction'ₓ'. -/
/-- A dependent version of `submonoid.closure_induction`.  -/
@[elab_as_elim, to_additive "A dependent version of `add_submonoid.closure_induction`. "]
theorem closure_induction' (s : Set M) {p : ∀ x, x ∈ closure s → Prop}
    (Hs : ∀ (x) (h : x ∈ s), p x (subset_closure h)) (H1 : p 1 (one_mem _))
    (Hmul : ∀ x hx y hy, p x hx → p y hy → p (x * y) (mul_mem hx hy)) {x} (hx : x ∈ closure s) :
    p x hx := by
  refine' Exists.elim _ fun (hx : x ∈ closure s) (hc : p x hx) => hc
  exact
    closure_induction hx (fun x hx => ⟨_, Hs x hx⟩) ⟨_, H1⟩ fun x y ⟨hx', hx⟩ ⟨hy', hy⟩ =>
      ⟨_, Hmul _ _ _ _ hx hy⟩
#align submonoid.closure_induction' Submonoid.closure_induction'
#align add_submonoid.closure_induction' AddSubmonoid.closure_induction'

/- warning: submonoid.closure_induction₂ -> Submonoid.closure_induction₂ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {p : M -> M -> Prop} {x : M} {y : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y (Submonoid.closure.{u1} M _inst_1 s)) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (p x y))) -> (forall (x : M), p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) x) -> (forall (x : M), p x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (forall (x : M) (y : M) (z : M), (p x z) -> (p y z) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) z)) -> (forall (x : M) (y : M) (z : M), (p z x) -> (p z y) -> (p z (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y))) -> (p x y)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {s : Set.{u1} M} {p : M -> M -> Prop} {x : M} {y : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (Submonoid.closure.{u1} M _inst_1 s)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y (Submonoid.closure.{u1} M _inst_1 s)) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s) -> (p x y))) -> (forall (x : M), p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) x) -> (forall (x : M), p x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M) (z : M), (p x z) -> (p y z) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) z)) -> (forall (x : M) (y : M) (z : M), (p z x) -> (p z y) -> (p z (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y))) -> (p x y)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_induction₂ Submonoid.closure_induction₂ₓ'. -/
/-- An induction principle for closure membership for predicates with two arguments.  -/
@[elab_as_elim,
  to_additive
      "An induction principle for additive closure membership for\npredicates with two arguments."]
theorem closure_induction₂ {p : M → M → Prop} {x} {y : M} (hx : x ∈ closure s) (hy : y ∈ closure s)
    (Hs : ∀ x ∈ s, ∀ y ∈ s, p x y) (H1_left : ∀ x, p 1 x) (H1_right : ∀ x, p x 1)
    (Hmul_left : ∀ x y z, p x z → p y z → p (x * y) z)
    (Hmul_right : ∀ x y z, p z x → p z y → p z (x * y)) : p x y :=
  closure_induction hx
    (fun x xs =>
      closure_induction hy (Hs x xs) (H1_right x) fun z y h₁ h₂ => Hmul_right z _ _ h₁ h₂)
    (H1_left y) fun x z h₁ h₂ => Hmul_left _ _ _ h₁ h₂
#align submonoid.closure_induction₂ Submonoid.closure_induction₂
#align add_submonoid.closure_induction₂ AddSubmonoid.closure_induction₂

/- warning: submonoid.dense_induction -> Submonoid.dense_induction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p : M -> Prop} (x : M) {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y))) -> (p x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p : M -> Prop} (x : M) {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (p x)) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (p x) -> (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y))) -> (p x)
Case conversion may be inaccurate. Consider using '#align submonoid.dense_induction Submonoid.dense_inductionₓ'. -/
/-- If `s` is a dense set in a monoid `M`, `submonoid.closure s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_elim,
  to_additive
      "If `s` is a dense set in an additive monoid `M`,\n`add_submonoid.closure s = ⊤`, then in order to prove that some predicate `p` holds for all `x : M`\nit suffices to verify `p x` for `x ∈ s`, verify `p 0`, and verify that `p x` and `p y` imply\n`p (x + y)`."]
theorem dense_induction {p : M → Prop} (x : M) {s : Set M} (hs : closure s = ⊤) (Hs : ∀ x ∈ s, p x)
    (H1 : p 1) (Hmul : ∀ x y, p x → p y → p (x * y)) : p x :=
  by
  have : ∀ x ∈ closure s, p x := fun x hx => closure_induction hx Hs H1 Hmul
  simpa [hs] using this x
#align submonoid.dense_induction Submonoid.dense_induction
#align add_submonoid.dense_induction AddSubmonoid.dense_induction

variable (M)

/- warning: submonoid.gi -> Submonoid.gi is a dubious translation:
lean 3 declaration is
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], GaloisInsertion.{u1, u1} (Set.{u1} M) (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} M) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} M) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} M) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} M) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} M) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} M) (Set.completeBooleanAlgebra.{u1} M))))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))) (Submonoid.closure.{u1} M _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))))
but is expected to have type
  forall (M : Type.{u1}) [_inst_1 : MulOneClass.{u1} M], GaloisInsertion.{u1, u1} (Set.{u1} M) (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Set.{u1} M) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} M) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} M) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} M) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} M) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} M) (Set.instCompleteBooleanAlgebraSet.{u1} M))))))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.gi Submonoid.giₓ'. -/
/-- `closure` forms a Galois insertion with the coercion to set. -/
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure M _) coe
    where
  choice s _ := closure s
  gc s t := closure_le
  le_l_u s := subset_closure
  choice_eq s h := rfl
#align submonoid.gi Submonoid.gi
#align add_submonoid.gi AddSubmonoid.gi

variable {M}

/- warning: submonoid.closure_eq -> Submonoid.closure_eq is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) S)) S
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (S : Submonoid.{u1} M _inst_1), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) S)) S
Case conversion may be inaccurate. Consider using '#align submonoid.closure_eq Submonoid.closure_eqₓ'. -/
/-- Closure of a submonoid `S` equals `S`. -/
@[simp, to_additive "Additive closure of an additive submonoid `S` equals `S`"]
theorem closure_eq : closure (S : Set M) = S :=
  (Submonoid.gi M).l_u_eq S
#align submonoid.closure_eq Submonoid.closure_eq
#align add_submonoid.closure_eq AddSubmonoid.closure_eq

/- warning: submonoid.closure_empty -> Submonoid.closure_empty is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} M) (Set.hasEmptyc.{u1} M))) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasBot.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (EmptyCollection.emptyCollection.{u1} (Set.{u1} M) (Set.instEmptyCollectionSet.{u1} M))) (Bot.bot.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instBotSubmonoid.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_empty Submonoid.closure_emptyₓ'. -/
@[simp, to_additive]
theorem closure_empty : closure (∅ : Set M) = ⊥ :=
  (Submonoid.gi M).gc.l_bot
#align submonoid.closure_empty Submonoid.closure_empty
#align add_submonoid.closure_empty AddSubmonoid.closure_empty

/- warning: submonoid.closure_univ -> Submonoid.closure_univ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Set.univ.{u1} M)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M], Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Set.univ.{u1} M)) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instTopSubmonoid.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_univ Submonoid.closure_univₓ'. -/
@[simp, to_additive]
theorem closure_univ : closure (univ : Set M) = ⊤ :=
  @coe_top M _ ▸ closure_eq ⊤
#align submonoid.closure_univ Submonoid.closure_univ
#align add_submonoid.closure_univ AddSubmonoid.closure_univ

/- warning: submonoid.closure_union -> Submonoid.closure_union is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u1} M) (t : Set.{u1} M), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Union.union.{u1} (Set.{u1} M) (Set.hasUnion.{u1} M) s t)) (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s) (Submonoid.closure.{u1} M _inst_1 t))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (s : Set.{u1} M) (t : Set.{u1} M), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Union.union.{u1} (Set.{u1} M) (Set.instUnionSet.{u1} M) s t)) (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s) (Submonoid.closure.{u1} M _inst_1 t))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_union Submonoid.closure_unionₓ'. -/
@[to_additive]
theorem closure_union (s t : Set M) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Submonoid.gi M).gc.l_sup
#align submonoid.closure_union Submonoid.closure_union
#align add_submonoid.closure_union AddSubmonoid.closure_union

/- warning: submonoid.closure_Union -> Submonoid.closure_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (s : ι -> (Set.{u1} M)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => s i))) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => Submonoid.closure.{u1} M _inst_1 (s i)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (s : ι -> (Set.{u1} M)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => s i))) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => Submonoid.closure.{u1} M _inst_1 (s i)))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_Union Submonoid.closure_unionᵢₓ'. -/
@[to_additive]
theorem closure_unionᵢ {ι} (s : ι → Set M) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Submonoid.gi M).gc.l_supr
#align submonoid.closure_Union Submonoid.closure_unionᵢ
#align add_submonoid.closure_Union AddSubmonoid.closure_unionᵢ

/- warning: submonoid.closure_singleton_le_iff_mem -> Submonoid.closure_singleton_le_iff_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (m : M) (p : Submonoid.{u1} M _inst_1), Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) m)) p) (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) m p)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] (m : M) (p : Submonoid.{u1} M _inst_1), Iff (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (Submonoid.closure.{u1} M _inst_1 (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) m)) p) (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) m p)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_singleton_le_iff_mem Submonoid.closure_singleton_le_iff_memₓ'. -/
@[simp, to_additive]
theorem closure_singleton_le_iff_mem (m : M) (p : Submonoid M) : closure {m} ≤ p ↔ m ∈ p := by
  rw [closure_le, singleton_subset_iff, SetLike.mem_coe]
#align submonoid.closure_singleton_le_iff_mem Submonoid.closure_singleton_le_iff_mem
#align add_submonoid.closure_singleton_le_iff_mem AddSubmonoid.closure_singleton_le_iff_mem

/- warning: submonoid.mem_supr -> Submonoid.mem_supᵢ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (p : ι -> (Submonoid.{u1} M _inst_1)) {m : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) m (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => p i))) (forall (N : Submonoid.{u1} M _inst_1), (forall (i : ι), LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (p i) N) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) m N))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (p : ι -> (Submonoid.{u1} M _inst_1)) {m : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) m (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => p i))) (forall (N : Submonoid.{u1} M _inst_1), (forall (i : ι), LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (p i) N) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) m N))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_supr Submonoid.mem_supᵢₓ'. -/
@[to_additive]
theorem mem_supᵢ {ι : Sort _} (p : ι → Submonoid M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N :=
  by
  rw [← closure_singleton_le_iff_mem, le_supᵢ_iff]
  simp only [closure_singleton_le_iff_mem]
#align submonoid.mem_supr Submonoid.mem_supᵢ
#align add_submonoid.mem_supr AddSubmonoid.mem_supᵢ

/- warning: submonoid.supr_eq_closure -> Submonoid.supᵢ_eq_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (p : ι -> (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => p i)) (Submonoid.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (p i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (p : ι -> (Submonoid.{u1} M _inst_1)), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => p i)) (Submonoid.closure.{u1} M _inst_1 (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (p i))))
Case conversion may be inaccurate. Consider using '#align submonoid.supr_eq_closure Submonoid.supᵢ_eq_closureₓ'. -/
@[to_additive]
theorem supᵢ_eq_closure {ι : Sort _} (p : ι → Submonoid M) :
    (⨆ i, p i) = Submonoid.closure (⋃ i, (p i : Set M)) := by
  simp_rw [Submonoid.closure_unionᵢ, Submonoid.closure_eq]
#align submonoid.supr_eq_closure Submonoid.supᵢ_eq_closure
#align add_submonoid.supr_eq_closure AddSubmonoid.supᵢ_eq_closure

/- warning: submonoid.disjoint_def -> Submonoid.disjoint_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p₁ : Submonoid.{u1} M _inst_1} {p₂ : Submonoid.{u1} M _inst_1}, Iff (Disjoint.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) p₁ p₂) (forall {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p₁) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p₂) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p₁ : Submonoid.{u1} M _inst_1} {p₂ : Submonoid.{u1} M _inst_1}, Iff (Disjoint.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))) p₁ p₂) (forall {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p₁) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p₂) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align submonoid.disjoint_def Submonoid.disjoint_defₓ'. -/
@[to_additive]
theorem disjoint_def {p₁ p₂ : Submonoid M} : Disjoint p₁ p₂ ↔ ∀ {x : M}, x ∈ p₁ → x ∈ p₂ → x = 1 :=
  by simp_rw [disjoint_iff_inf_le, SetLike.le_def, mem_inf, and_imp, mem_bot]
#align submonoid.disjoint_def Submonoid.disjoint_def
#align add_submonoid.disjoint_def AddSubmonoid.disjoint_def

/- warning: submonoid.disjoint_def' -> Submonoid.disjoint_def' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p₁ : Submonoid.{u1} M _inst_1} {p₂ : Submonoid.{u1} M _inst_1}, Iff (Disjoint.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) p₁ p₂) (forall {x : M} {y : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x p₁) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y p₂) -> (Eq.{succ u1} M x y) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {p₁ : Submonoid.{u1} M _inst_1} {p₂ : Submonoid.{u1} M _inst_1}, Iff (Disjoint.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))) p₁ p₂) (forall {x : M} {y : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x p₁) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y p₂) -> (Eq.{succ u1} M x y) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))))
Case conversion may be inaccurate. Consider using '#align submonoid.disjoint_def' Submonoid.disjoint_def'ₓ'. -/
@[to_additive]
theorem disjoint_def' {p₁ p₂ : Submonoid M} :
    Disjoint p₁ p₂ ↔ ∀ {x y : M}, x ∈ p₁ → y ∈ p₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h x y hx hy hxy => h hx <| hxy.symm ▸ hy, fun h x hx hx' => h hx hx' rfl⟩
#align submonoid.disjoint_def' Submonoid.disjoint_def'
#align add_submonoid.disjoint_def' AddSubmonoid.disjoint_def'

end Submonoid

namespace MonoidHom

variable [MulOneClass N]

open Submonoid

#print MonoidHom.eqLocusM /-
/-- The submonoid of elements `x : M` such that `f x = g x` -/
@[to_additive "The additive submonoid of elements `x : M` such that `f x = g x`"]
def eqLocusM (f g : M →* N) : Submonoid M
    where
  carrier := { x | f x = g x }
  one_mem' := by rw [Set.mem_setOf_eq, f.map_one, g.map_one]
  mul_mem' x y (hx : _ = _) (hy : _ = _) := by simp [*]
#align monoid_hom.eq_mlocus MonoidHom.eqLocusM
-/

/- warning: monoid_hom.eq_mlocus_same -> MonoidHom.eqLocusM_same is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} N] (f : MonoidHom.{u1, u2} M N _inst_1 _inst_3), Eq.{succ u1} (Submonoid.{u1} M _inst_1) (MonoidHom.eqLocusM.{u1, u2} M N _inst_1 _inst_3 f f) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} N] (f : MonoidHom.{u2, u1} M N _inst_1 _inst_3), Eq.{succ u2} (Submonoid.{u2} M _inst_1) (MonoidHom.eqLocusM.{u2, u1} M N _inst_1 _inst_3 f f) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))
Case conversion may be inaccurate. Consider using '#align monoid_hom.eq_mlocus_same MonoidHom.eqLocusM_sameₓ'. -/
@[simp, to_additive]
theorem eqLocusM_same (f : M →* N) : f.eqMlocus f = ⊤ :=
  SetLike.ext fun _ => eq_self_iff_true _
#align monoid_hom.eq_mlocus_same MonoidHom.eqLocusM_same
#align add_monoid_hom.eq_mlocus_same AddMonoidHom.eqLocusM_same

/- warning: monoid_hom.eq_on_mclosure -> MonoidHom.eqOn_closureM is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} N] {f : MonoidHom.{u1, u2} M N _inst_1 _inst_3} {g : MonoidHom.{u1, u2} M N _inst_1 _inst_3} {s : Set.{u1} M}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) s) -> (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Submonoid.closure.{u1} M _inst_1 s)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} N] {f : MonoidHom.{u2, u1} M N _inst_1 _inst_3} {g : MonoidHom.{u2, u1} M N _inst_1 _inst_3} {s : Set.{u2} M}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) g) s) -> (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) g) (SetLike.coe.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Submonoid.closure.{u2} M _inst_1 s)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.eq_on_mclosure MonoidHom.eqOn_closureMₓ'. -/
/-- If two monoid homomorphisms are equal on a set, then they are equal on its submonoid closure. -/
@[to_additive
      "If two monoid homomorphisms are equal on a set, then they are equal on its submonoid\nclosure."]
theorem eqOn_closureM {f g : M →* N} {s : Set M} (h : Set.EqOn f g s) : Set.EqOn f g (closure s) :=
  show closure s ≤ f.eqMlocus g from closure_le.2 h
#align monoid_hom.eq_on_mclosure MonoidHom.eqOn_closureM

/- warning: monoid_hom.eq_of_eq_on_mtop -> MonoidHom.eq_of_eqOn_topM is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} N] {f : MonoidHom.{u1, u2} M N _inst_1 _inst_3} {g : MonoidHom.{u1, u2} M N _inst_1 _inst_3}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1)))) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) f g)
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} N] {f : MonoidHom.{u2, u1} M N _inst_1 _inst_3} {g : MonoidHom.{u2, u1} M N _inst_1 _inst_3}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) g) (SetLike.coe.{u2, u2} (Submonoid.{u2} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u2} M _inst_1) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1)))) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) f g)
Case conversion may be inaccurate. Consider using '#align monoid_hom.eq_of_eq_on_mtop MonoidHom.eq_of_eqOn_topMₓ'. -/
@[to_additive]
theorem eq_of_eqOn_topM {f g : M →* N} (h : Set.EqOn f g (⊤ : Submonoid M)) : f = g :=
  ext fun x => h trivial
#align monoid_hom.eq_of_eq_on_mtop MonoidHom.eq_of_eqOn_topM

/- warning: monoid_hom.eq_of_eq_on_mdense -> MonoidHom.eq_of_eqOn_denseM is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulOneClass.{u1} M] [_inst_3 : MulOneClass.{u2} N] {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M _inst_1) (Submonoid.closure.{u1} M _inst_1 s) (Top.top.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.hasTop.{u1} M _inst_1))) -> (forall {f : MonoidHom.{u1, u2} M N _inst_1 _inst_3} {g : MonoidHom.{u1, u2} M N _inst_1 _inst_3}, (Set.EqOn.{u1, u2} M N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) f) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) (fun (_x : MonoidHom.{u1, u2} M N _inst_1 _inst_3) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N _inst_1 _inst_3) g) s) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u1, u2} M N _inst_1 _inst_3) f g))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : MulOneClass.{u2} M] [_inst_3 : MulOneClass.{u1} N] {s : Set.{u2} M}, (Eq.{succ u2} (Submonoid.{u2} M _inst_1) (Submonoid.closure.{u2} M _inst_1 s) (Top.top.{u2} (Submonoid.{u2} M _inst_1) (Submonoid.instTopSubmonoid.{u2} M _inst_1))) -> (forall {f : MonoidHom.{u2, u1} M N _inst_1 _inst_3} {g : MonoidHom.{u2, u1} M N _inst_1 _inst_3}, (Set.EqOn.{u2, u1} M N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N (MulOneClass.toMul.{u2} M _inst_1) (MulOneClass.toMul.{u1} N _inst_3) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) M N _inst_1 _inst_3 (MonoidHom.monoidHomClass.{u2, u1} M N _inst_1 _inst_3))) g) s) -> (Eq.{max (succ u2) (succ u1)} (MonoidHom.{u2, u1} M N _inst_1 _inst_3) f g))
Case conversion may be inaccurate. Consider using '#align monoid_hom.eq_of_eq_on_mdense MonoidHom.eq_of_eqOn_denseMₓ'. -/
@[to_additive]
theorem eq_of_eqOn_denseM {s : Set M} (hs : closure s = ⊤) {f g : M →* N} (h : s.EqOn f g) :
    f = g :=
  eq_of_eq_on_mtop <| hs ▸ eqOn_closureM h
#align monoid_hom.eq_of_eq_on_mdense MonoidHom.eq_of_eqOn_denseM

end MonoidHom

end NonAssoc

section Assoc

variable [Monoid M] [Monoid N] {s : Set M}

section IsUnit

#print IsUnit.submonoid /-
/-- The submonoid consisting of the units of a monoid -/
@[to_additive "The additive submonoid consisting of the additive units of an additive monoid"]
def IsUnit.submonoid (M : Type _) [Monoid M] : Submonoid M
    where
  carrier := setOf IsUnit
  one_mem' := by simp only [isUnit_one, Set.mem_setOf_eq]
  mul_mem' := by
    intro a b ha hb
    rw [Set.mem_setOf_eq] at *
    exact IsUnit.mul ha hb
#align is_unit.submonoid IsUnit.submonoid
#align is_add_unit.add_submonoid IsAddUnit.addSubmonoid
-/

/- warning: is_unit.mem_submonoid_iff -> IsUnit.mem_submonoid_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_3 : Monoid.{u1} M] (a : M), Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a (IsUnit.submonoid.{u1} M _inst_3)) (IsUnit.{u1} M _inst_3 a)
but is expected to have type
  forall {M : Type.{u1}} [_inst_3 : Monoid.{u1} M] (a : M), Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) a (IsUnit.submonoid.{u1} M _inst_3)) (IsUnit.{u1} M _inst_3 a)
Case conversion may be inaccurate. Consider using '#align is_unit.mem_submonoid_iff IsUnit.mem_submonoid_iffₓ'. -/
@[to_additive]
theorem IsUnit.mem_submonoid_iff {M : Type _} [Monoid M] (a : M) :
    a ∈ IsUnit.submonoid M ↔ IsUnit a :=
  by
  change a ∈ setOf IsUnit ↔ IsUnit a
  rw [Set.mem_setOf_eq]
#align is_unit.mem_submonoid_iff IsUnit.mem_submonoid_iff

end IsUnit

namespace MonoidHom

open Submonoid

/- warning: monoid_hom.of_mclosure_eq_top_left -> MonoidHom.ofClosureMEqTopLeft is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_3 : Monoid.{u1} M] [_inst_4 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) -> (Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4)))))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4))) (f x) (f y)))) -> (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_3) (Monoid.toMulOneClass.{u2} N _inst_4))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_3 : Monoid.{u1} M] [_inst_4 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) -> (Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3)))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N _inst_4)))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4))) (f x) (f y)))) -> (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_3) (Monoid.toMulOneClass.{u2} N _inst_4))
Case conversion may be inaccurate. Consider using '#align monoid_hom.of_mclosure_eq_top_left MonoidHom.ofClosureMEqTopLeftₓ'. -/
/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `monoid_hom.of_mclosure_eq_top_left` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `x ∈ s`. -/
@[to_additive
      "/-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is\nthe whole monoid. Then `add_monoid_hom.of_mclosure_eq_top_left` defines an additive monoid\nhomomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `x ∈ s`. -/"]
def ofClosureMEqTopLeft {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ x ∈ s, ∀ (y), f (x * y) = f x * f y) : M →* N
    where
  toFun := f
  map_one' := h1
  map_mul' x :=
    dense_induction x hs hmul (fun y => by rw [one_mul, h1, one_mul]) fun a b ha hb y => by
      rw [mul_assoc, ha, ha, hb, mul_assoc]
#align monoid_hom.of_mclosure_eq_top_left MonoidHom.ofClosureMEqTopLeft

/- warning: monoid_hom.coe_of_mclosure_eq_top_left -> MonoidHom.coe_ofClosureMEqTopLeft is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N) (hs : Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (h1 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)))))) (hmul : forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : M), Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (f x) (f y)))), Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHom.ofClosureMEqTopLeft.{u1, u2} M N _inst_1 _inst_2 s f hs h1 hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {s : Set.{u2} M} (f : M -> N) (hs : Eq.{succ u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.closure.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1) s) (Top.top.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instTopSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (h1 : Eq.{succ u1} N (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2)))) (hmul : forall (x : M), (Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x s) -> (forall (y : M), Eq.{succ u1} N (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (f x) (f y)))), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) (MonoidHom.ofClosureMEqTopLeft.{u2, u1} M N _inst_1 _inst_2 s f hs h1 hmul)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_of_mclosure_eq_top_left MonoidHom.coe_ofClosureMEqTopLeftₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_ofClosureMEqTopLeft (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopLeft f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_left MonoidHom.coe_ofClosureMEqTopLeft
#align add_monoid_hom.coe_of_mclosure_eq_top_left AddMonoidHom.coe_ofClosureMEqTopLeft

/- warning: monoid_hom.of_mclosure_eq_top_right -> MonoidHom.ofClosureMEqTopRight is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_3 : Monoid.{u1} M] [_inst_4 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) -> (Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4)))))) -> (forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4))) (f x) (f y)))) -> (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_3) (Monoid.toMulOneClass.{u2} N _inst_4))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_3 : Monoid.{u1} M] [_inst_4 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N), (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3)))) -> (Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_3)))) (OfNat.ofNat.{u2} N 1 (One.toOfNat1.{u2} N (Monoid.toOne.{u2} N _inst_4)))) -> (forall (x : M) (y : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_3))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_4))) (f x) (f y)))) -> (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_3) (Monoid.toMulOneClass.{u2} N _inst_4))
Case conversion may be inaccurate. Consider using '#align monoid_hom.of_mclosure_eq_top_right MonoidHom.ofClosureMEqTopRightₓ'. -/
/-- Let `s` be a subset of a monoid `M` such that the closure of `s` is the whole monoid.
Then `monoid_hom.of_mclosure_eq_top_right` defines a monoid homomorphism from `M` asking for
a proof of `f (x * y) = f x * f y` only for `y ∈ s`. -/
@[to_additive
      "/-- Let `s` be a subset of an additive monoid `M` such that the closure of `s` is\nthe whole monoid. Then `add_monoid_hom.of_mclosure_eq_top_right` defines an additive monoid\nhomomorphism from `M` asking for a proof of `f (x + y) = f x + f y` only for `y ∈ s`. -/"]
def ofClosureMEqTopRight {M N} [Monoid M] [Monoid N] {s : Set M} (f : M → N) (hs : closure s = ⊤)
    (h1 : f 1 = 1) (hmul : ∀ (x), ∀ y ∈ s, f (x * y) = f x * f y) : M →* N
    where
  toFun := f
  map_one' := h1
  map_mul' x y :=
    dense_induction y hs (fun y hy x => hmul x y hy) (by simp [h1])
      (fun y₁ y₂ h₁ h₂ x => by simp only [← mul_assoc, h₁, h₂]) x
#align monoid_hom.of_mclosure_eq_top_right MonoidHom.ofClosureMEqTopRight

/- warning: monoid_hom.coe_of_mclosure_eq_top_right -> MonoidHom.coe_ofClosureMEqTopRight is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {s : Set.{u1} M} (f : M -> N) (hs : Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (h1 : Eq.{succ u2} N (f (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (OfNat.ofNat.{u2} N 1 (OfNat.mk.{u2} N 1 (One.one.{u2} N (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)))))) (hmul : forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (Eq.{succ u2} N (f (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)) (HMul.hMul.{u2, u2, u2} N N N (instHMul.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (f x) (f y)))), Eq.{max (succ u1) (succ u2)} (M -> N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (fun (_x : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) => M -> N) (MonoidHom.hasCoeToFun.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHom.ofClosureMEqTopRight.{u1, u2} M N _inst_1 _inst_2 s f hs h1 hmul)) f
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {s : Set.{u2} M} (f : M -> N) (hs : Eq.{succ u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.closure.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1) s) (Top.top.{u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Submonoid.instTopSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)))) (h1 : Eq.{succ u1} N (f (OfNat.ofNat.{u2} M 1 (One.toOfNat1.{u2} M (Monoid.toOne.{u2} M _inst_1)))) (OfNat.ofNat.{u1} N 1 (One.toOfNat1.{u1} N (Monoid.toOne.{u1} N _inst_2)))) (hmul : forall (x : M) (y : M), (Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) y s) -> (Eq.{succ u1} N (f (HMul.hMul.{u2, u2, u2} M M M (instHMul.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) x y)) (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (f x) (f y)))), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : M), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : M) => N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)) M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2) (MonoidHom.monoidHomClass.{u2, u1} M N (Monoid.toMulOneClass.{u2} M _inst_1) (Monoid.toMulOneClass.{u1} N _inst_2)))) (MonoidHom.ofClosureMEqTopRight.{u2, u1} M N _inst_1 _inst_2 s f hs h1 hmul)) f
Case conversion may be inaccurate. Consider using '#align monoid_hom.coe_of_mclosure_eq_top_right MonoidHom.coe_ofClosureMEqTopRightₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_ofClosureMEqTopRight (f : M → N) (hs : closure s = ⊤) (h1 hmul) :
    ⇑(ofClosureMEqTopRight f hs h1 hmul) = f :=
  rfl
#align monoid_hom.coe_of_mclosure_eq_top_right MonoidHom.coe_ofClosureMEqTopRight
#align add_monoid_hom.coe_of_mclosure_eq_top_right AddMonoidHom.coe_ofClosureMEqTopRight

end MonoidHom

end Assoc

