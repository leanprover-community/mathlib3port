/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying

! This file was ported from Lean 3 source module group_theory.subgroup.finite
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Finite
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.Submonoid.Membership

/-!
# Subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/


open BigOperators

variable {G : Type _} [Group G]

variable {A : Type _} [AddGroup A]

namespace Subgroup

@[to_additive]
instance (K : Subgroup G) [d : DecidablePred (· ∈ K)] [Fintype G] : Fintype K :=
  show Fintype { g : G // g ∈ K } from inferInstance

@[to_additive]
instance (K : Subgroup G) [Finite G] : Finite K :=
  Subtype.finite

end Subgroup

/-!
### Conversion to/from `additive`/`multiplicative`
-/


namespace Subgroup

variable (H K : Subgroup G)

/- warning: subgroup.list_prod_mem -> Subgroup.list_prod_mem is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (K : Subgroup.{u1} G _inst_1) {l : List.{u1} G}, (forall (x : G), (Membership.Mem.{u1, u1} G (List.{u1} G) (List.hasMem.{u1} G) x l) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x K)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) l) K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (K : Subgroup.{u1} G _inst_1) {l : List.{u1} G}, (forall (x : G), (Membership.mem.{u1, u1} G (List.{u1} G) (List.instMembershipList.{u1} G) x l) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x K)) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) l) K)
Case conversion may be inaccurate. Consider using '#align subgroup.list_prod_mem Subgroup.list_prod_memₓ'. -/
/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive "Sum of a list of elements in an `add_subgroup` is in the `add_subgroup`."]
protected theorem list_prod_mem {l : List G} : (∀ x ∈ l, x ∈ K) → l.Prod ∈ K :=
  list_prod_mem
#align subgroup.list_prod_mem Subgroup.list_prod_mem
#align add_subgroup.list_sum_mem AddSubgroup.list_sum_mem

/- warning: subgroup.multiset_prod_mem -> Subgroup.multiset_prod_mem is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (K : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (g : Multiset.{u1} G), (forall (a : G), (Membership.Mem.{u1, u1} G (Multiset.{u1} G) (Multiset.hasMem.{u1} G) a g) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) a K)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) (Multiset.prod.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) g) K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (K : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (g : Multiset.{u1} G), (forall (a : G), (Membership.mem.{u1, u1} G (Multiset.{u1} G) (Multiset.instMembershipMultiset.{u1} G) a g) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) a K)) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) (Multiset.prod.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) g) K)
Case conversion may be inaccurate. Consider using '#align subgroup.multiset_prod_mem Subgroup.multiset_prod_memₓ'. -/
/-- Product of a multiset of elements in a subgroup of a `comm_group` is in the subgroup. -/
@[to_additive
      "Sum of a multiset of elements in an `add_subgroup` of an `add_comm_group`\nis in the `add_subgroup`."]
protected theorem multiset_prod_mem {G} [CommGroup G] (K : Subgroup G) (g : Multiset G) :
    (∀ a ∈ g, a ∈ K) → g.Prod ∈ K :=
  multiset_prod_mem g
#align subgroup.multiset_prod_mem Subgroup.multiset_prod_mem
#align add_subgroup.multiset_sum_mem AddSubgroup.multiset_sum_mem

/- warning: subgroup.multiset_noncomm_prod_mem -> Subgroup.multiset_noncommProd_mem is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (K : Subgroup.{u1} G _inst_1) (g : Multiset.{u1} G) (comm : Set.Pairwise.{u1} G (setOf.{u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Multiset.{u1} G) (Multiset.hasMem.{u1} G) x g)) (Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))), (forall (a : G), (Membership.Mem.{u1, u1} G (Multiset.{u1} G) (Multiset.hasMem.{u1} G) a g) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) a K)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Multiset.noncommProd.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g comm) K)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (K : Subgroup.{u1} G _inst_1) (g : Multiset.{u1} G) (comm : Set.Pairwise.{u1} G (setOf.{u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Multiset.{u1} G) (Multiset.instMembershipMultiset.{u1} G) x g)) (Commute.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))), (forall (a : G), (Membership.mem.{u1, u1} G (Multiset.{u1} G) (Multiset.instMembershipMultiset.{u1} G) a g) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) a K)) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) (Multiset.noncommProd.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) g comm) K)
Case conversion may be inaccurate. Consider using '#align subgroup.multiset_noncomm_prod_mem Subgroup.multiset_noncommProd_memₓ'. -/
@[to_additive]
theorem multiset_noncommProd_mem (K : Subgroup G) (g : Multiset G) (comm) :
    (∀ a ∈ g, a ∈ K) → g.noncommProd comm ∈ K :=
  K.toSubmonoid.multiset_noncommProd_mem g comm
#align subgroup.multiset_noncomm_prod_mem Subgroup.multiset_noncommProd_mem
#align add_subgroup.multiset_noncomm_sum_mem AddSubgroup.multiset_noncommSum_mem

/- warning: subgroup.prod_mem -> Subgroup.prod_mem is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (K : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> G}, (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) (f c) K)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) (Finset.prod.{u1, u2} G ι (CommGroup.toCommMonoid.{u1} G _inst_3) t (fun (c : ι) => f c)) K)
but is expected to have type
  forall {G : Type.{u2}} [_inst_3 : CommGroup.{u2} G] (K : Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> G}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} G (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) (f c) K)) -> (Membership.mem.{u2, u2} G (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) (Finset.prod.{u2, u1} G ι (CommGroup.toCommMonoid.{u2} G _inst_3) t (fun (c : ι) => f c)) K)
Case conversion may be inaccurate. Consider using '#align subgroup.prod_mem Subgroup.prod_memₓ'. -/
/-- Product of elements of a subgroup of a `comm_group` indexed by a `finset` is in the
    subgroup. -/
@[to_additive
      "Sum of elements in an `add_subgroup` of an `add_comm_group` indexed by a `finset`\nis in the `add_subgroup`."]
protected theorem prod_mem {G : Type _} [CommGroup G] (K : Subgroup G) {ι : Type _} {t : Finset ι}
    {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) : (∏ c in t, f c) ∈ K :=
  prod_mem h
#align subgroup.prod_mem Subgroup.prod_mem
#align add_subgroup.sum_mem AddSubgroup.sum_mem

/- warning: subgroup.noncomm_prod_mem -> Subgroup.noncommProd_mem is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (K : Subgroup.{u1} G _inst_1) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> G} (comm : Set.Pairwise.{u2} ι ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) t) (fun (a : ι) (b : ι) => Commute.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (f a) (f b))), (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (f c) K)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Finset.noncommProd.{u2, u1} ι G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) t f comm) K)
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : Group.{u2} G] (K : Subgroup.{u2} G _inst_1) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> G} (comm : Set.Pairwise.{u1} ι (Finset.toSet.{u1} ι t) (fun (a : ι) (b : ι) => Commute.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (f a) (f b))), (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) (f c) K)) -> (Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) (Finset.noncommProd.{u1, u2} ι G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) t f comm) K)
Case conversion may be inaccurate. Consider using '#align subgroup.noncomm_prod_mem Subgroup.noncommProd_memₓ'. -/
@[to_additive]
theorem noncommProd_mem (K : Subgroup G) {ι : Type _} {t : Finset ι} {f : ι → G} (comm) :
    (∀ c ∈ t, f c ∈ K) → t.noncommProd f comm ∈ K :=
  K.toSubmonoid.noncommProd_mem t f comm
#align subgroup.noncomm_prod_mem Subgroup.noncommProd_mem
#align add_subgroup.noncomm_sum_mem AddSubgroup.noncommSum_mem

/- warning: subgroup.coe_list_prod -> Subgroup.val_list_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (l : List.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)), Eq.{succ u1} G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (coeSubtype.{succ u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x H))))) (List.prod.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.mul.{u1} G _inst_1 H) (Subgroup.one.{u1} G _inst_1 H) l)) (List.prod.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (List.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) G (coeSubtype.{succ u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x H)))))) l))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) (l : List.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))), Eq.{succ u1} G (Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x (SetLike.coe.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1) H)) (List.prod.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Subgroup.mul.{u1} G _inst_1 H) (Subgroup.one.{u1} G _inst_1 H) l)) (List.prod.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))) (InvOneClass.toOne.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) (List.map.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) G (Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) l))
Case conversion may be inaccurate. Consider using '#align subgroup.coe_list_prod Subgroup.val_list_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_list_prod (l : List H) : (l.Prod : G) = (l.map coe).Prod :=
  SubmonoidClass.coe_list_prod l
#align subgroup.coe_list_prod Subgroup.val_list_prod
#align add_subgroup.coe_list_sum AddSubgroup.val_list_sum

/- warning: subgroup.coe_multiset_prod -> Subgroup.val_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (H : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (m : Multiset.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H)), Eq.{succ u1} G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (coeSubtype.{succ u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H))))) (Multiset.prod.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) (CommGroup.toCommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) (Subgroup.toCommGroup.{u1} G _inst_3 H)) m)) (Multiset.prod.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) (Multiset.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) H) G (coeSubtype.{succ u1} G (fun (x : G) => Membership.Mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H)))))) m))
but is expected to have type
  forall {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (H : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (m : Multiset.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H))), Eq.{succ u1} G (Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x (SetLike.coe.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) H)) (Multiset.prod.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H)) (Submonoid.toCommMonoid.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) (Subgroup.toSubmonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_3) H)) m)) (Multiset.prod.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) (Multiset.map.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H)) G (Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H)) m))
Case conversion may be inaccurate. Consider using '#align subgroup.coe_multiset_prod Subgroup.val_multiset_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_multiset_prod {G} [CommGroup G] (H : Subgroup G) (m : Multiset H) :
    (m.Prod : G) = (m.map coe).Prod :=
  SubmonoidClass.coe_multiset_prod m
#align subgroup.coe_multiset_prod Subgroup.val_multiset_prod
#align add_subgroup.coe_multiset_sum AddSubgroup.val_multiset_sum

/- warning: subgroup.coe_finset_prod -> Subgroup.val_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {G : Type.{u2}} [_inst_3 : CommGroup.{u2} G] (H : Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) (f : ι -> (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H)) (s : Finset.{u1} ι), Eq.{succ u2} G ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (coeSubtype.{succ u2} G (fun (x : G) => Membership.Mem.{u2, u2} G (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) (SetLike.hasMem.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) x H))))) (Finset.prod.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) ι (CommGroup.toCommMonoid.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) (Subgroup.toCommGroup.{u2} G _inst_3 H)) s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} G ι (CommGroup.toCommMonoid.{u2} G _inst_3) s (fun (i : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) H) G (coeSubtype.{succ u2} G (fun (x : G) => Membership.Mem.{u2, u2} G (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) (SetLike.hasMem.{u2, u2} (Subgroup.{u2} G (CommGroup.toGroup.{u2} G _inst_3)) G (Subgroup.setLike.{u2} G (CommGroup.toGroup.{u2} G _inst_3))) x H))))) (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {G : Type.{u1}} [_inst_3 : CommGroup.{u1} G] (H : Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (f : ι -> (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H))) (s : Finset.{u2} ι), Eq.{succ u1} G (Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x (SetLike.coe.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) H)) (Finset.prod.{u1, u2} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3))) x H)) ι (Submonoid.toCommMonoid.{u1} G (CommGroup.toCommMonoid.{u1} G _inst_3) (Subgroup.toSubmonoid.{u1} G (CommGroup.toGroup.{u1} G _inst_3) H)) s (fun (i : ι) => f i))) (Finset.prod.{u1, u2} G ι (CommGroup.toCommMonoid.{u1} G _inst_3) s (fun (i : ι) => Subtype.val.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) x (SetLike.coe.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_3)) H)) (f i)))
Case conversion may be inaccurate. Consider using '#align subgroup.coe_finset_prod Subgroup.val_finset_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem val_finset_prod {ι G} [CommGroup G] (H : Subgroup G) (f : ι → H) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : G) :=
  SubmonoidClass.coe_finset_prod f s
#align subgroup.coe_finset_prod Subgroup.val_finset_prod
#align add_subgroup.coe_finset_sum AddSubgroup.val_finset_sum

/- warning: subgroup.fintype_bot -> Subgroup.fintypeBot is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align subgroup.fintype_bot Subgroup.fintypeBotₓ'. -/
@[to_additive]
instance fintypeBot : Fintype (⊥ : Subgroup G) :=
  ⟨{1}, by
    rintro ⟨x, ⟨hx⟩⟩
    exact Finset.mem_singleton_self _⟩
#align subgroup.fintype_bot Subgroup.fintypeBot
#align add_subgroup.fintype_bot AddSubgroup.fintypeBot

/- warning: subgroup.card_bot -> Subgroup.card_bot is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {_x : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))}, Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1))) _x) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {_x : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1))))}, Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))) _x) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
Case conversion may be inaccurate. Consider using '#align subgroup.card_bot Subgroup.card_botₓ'. -/
/- curly brackets `{}` are used here instead of instance brackets `[]` because
  the instance in a goal is often not the same as the one inferred by type class inference.  -/
@[simp, to_additive]
theorem card_bot {_ : Fintype ↥(⊥ : Subgroup G)} : Fintype.card (⊥ : Subgroup G) = 1 :=
  Fintype.card_eq_one_iff.2
    ⟨⟨(1 : G), Set.mem_singleton 1⟩, fun ⟨y, hy⟩ => Subtype.eq <| Subgroup.mem_bot.1 hy⟩
#align subgroup.card_bot Subgroup.card_bot
#align add_subgroup.card_bot AddSubgroup.card_bot

/- warning: subgroup.eq_top_of_card_eq -> Subgroup.eq_top_of_card_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)] [_inst_4 : Fintype.{u1} G], (Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3) (Fintype.card.{u1} G _inst_4)) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))] [_inst_4 : Fintype.{u1} G], (Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3) (Fintype.card.{u1} G _inst_4)) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.eq_top_of_card_eq Subgroup.eq_top_of_card_eqₓ'. -/
@[to_additive]
theorem eq_top_of_card_eq [Fintype H] [Fintype G] (h : Fintype.card H = Fintype.card G) : H = ⊤ :=
  by
  haveI : Fintype (H : Set G) := ‹Fintype H›
  rw [SetLike.ext'_iff, coe_top, ← Finset.coe_univ, ← (H : Set G).coe_toFinset, Finset.coe_inj, ←
    Finset.card_eq_iff_eq_univ, ← h, Set.toFinset_card]
  congr
#align subgroup.eq_top_of_card_eq Subgroup.eq_top_of_card_eq
#align add_subgroup.eq_top_of_card_eq AddSubgroup.eq_top_of_card_eq

/- warning: subgroup.eq_top_of_le_card -> Subgroup.eq_top_of_le_card is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)] [_inst_4 : Fintype.{u1} G], (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} G _inst_4) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3)) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasTop.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))] [_inst_4 : Fintype.{u1} G], (LE.le.{0} Nat instLENat (Fintype.card.{u1} G _inst_4) (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3)) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Top.top.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instTopSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.eq_top_of_le_card Subgroup.eq_top_of_le_cardₓ'. -/
@[to_additive]
theorem eq_top_of_le_card [Fintype H] [Fintype G] (h : Fintype.card G ≤ Fintype.card H) : H = ⊤ :=
  eq_top_of_card_eq H (le_antisymm (Fintype.card_le_of_injective coe Subtype.coe_injective) h)
#align subgroup.eq_top_of_le_card Subgroup.eq_top_of_le_card
#align add_subgroup.eq_top_of_le_card AddSubgroup.eq_top_of_le_card

/- warning: subgroup.eq_bot_of_card_le -> Subgroup.eq_bot_of_card_le is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], (LE.le.{0} Nat instLENat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.eq_bot_of_card_le Subgroup.eq_bot_of_card_leₓ'. -/
@[to_additive]
theorem eq_bot_of_card_le [Fintype H] (h : Fintype.card H ≤ 1) : H = ⊥ :=
  let _ := Fintype.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H
#align subgroup.eq_bot_of_card_le Subgroup.eq_bot_of_card_le
#align add_subgroup.eq_bot_of_card_le AddSubgroup.eq_bot_of_card_le

/- warning: subgroup.eq_bot_of_card_eq -> Subgroup.eq_bot_of_card_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], (Eq.{1} Nat (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], (Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.eq_bot_of_card_eq Subgroup.eq_bot_of_card_eqₓ'. -/
@[to_additive]
theorem eq_bot_of_card_eq [Fintype H] (h : Fintype.card H = 1) : H = ⊥ :=
  H.eq_bot_of_card_le (le_of_eq h)
#align subgroup.eq_bot_of_card_eq Subgroup.eq_bot_of_card_eq
#align add_subgroup.eq_bot_of_card_eq AddSubgroup.eq_bot_of_card_eq

/- warning: subgroup.card_le_one_iff_eq_bot -> Subgroup.card_le_one_iff_eq_bot is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], Iff (LE.le.{0} Nat Nat.hasLe (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], Iff (LE.le.{0} Nat instLENat (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Eq.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.card_le_one_iff_eq_bot Subgroup.card_le_one_iff_eq_botₓ'. -/
@[to_additive]
theorem card_le_one_iff_eq_bot [Fintype H] : Fintype.card H ≤ 1 ↔ H = ⊥ :=
  ⟨fun h =>
    (eq_bot_iff_forall _).2 fun x hx => by
      simpa [Subtype.ext_iff] using Fintype.card_le_one_iff.1 h ⟨x, hx⟩ 1,
    fun h => by simp [h]⟩
#align subgroup.card_le_one_iff_eq_bot Subgroup.card_le_one_iff_eq_bot
#align add_subgroup.card_nonpos_iff_eq_bot AddSubgroup.card_nonpos_iff_eq_bot

/- warning: subgroup.one_lt_card_iff_ne_bot -> Subgroup.one_lt_card_iff_ne_bot is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H)], Iff (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Fintype.card.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) _inst_3)) (Ne.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.hasBot.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] (H : Subgroup.{u1} G _inst_1) [_inst_3 : Fintype.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H))], Iff (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Fintype.card.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) _inst_3)) (Ne.{succ u1} (Subgroup.{u1} G _inst_1) H (Bot.bot.{u1} (Subgroup.{u1} G _inst_1) (Subgroup.instBotSubgroup.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align subgroup.one_lt_card_iff_ne_bot Subgroup.one_lt_card_iff_ne_botₓ'. -/
@[to_additive]
theorem one_lt_card_iff_ne_bot [Fintype H] : 1 < Fintype.card H ↔ H ≠ ⊥ :=
  lt_iff_not_le.trans H.card_le_one_iff_eq_bot.Not
#align subgroup.one_lt_card_iff_ne_bot Subgroup.one_lt_card_iff_ne_bot
#align add_subgroup.pos_card_iff_ne_bot AddSubgroup.pos_card_iff_ne_bot

end Subgroup

namespace Subgroup

section Pi

open Set

variable {η : Type _} {f : η → Type _} [∀ i, Group (f i)]

/- warning: subgroup.pi_mem_of_mul_single_mem_aux -> Subgroup.pi_mem_of_mulSingle_mem_aux is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {f : η -> Type.{u2}} [_inst_3 : forall (i : η), Group.{u2} (f i)] [_inst_4 : DecidableEq.{succ u1} η] (I : Finset.{u1} η) {H : Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))} (x : forall (i : η), f i), (forall (i : η), (Not (Membership.Mem.{u1, u1} η (Finset.{u1} η) (Finset.hasMem.{u1} η) i I)) -> (Eq.{succ u2} (f i) (x i) (OfNat.ofNat.{u2} (f i) 1 (OfNat.mk.{u2} (f i) 1 (One.one.{u2} (f i) (MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_3 i)))))))))) -> (forall (i : η), (Membership.Mem.{u1, u1} η (Finset.{u1} η) (Finset.hasMem.{u1} η) i I) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : η), f i) (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) (Pi.mulSingle.{u1, u2} η (fun (i : η) => f i) (fun (a : η) (b : η) => _inst_4 a b) (fun (i : η) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_3 i))))) i (x i)) H)) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : η), f i) (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) x H)
but is expected to have type
  forall {η : Type.{u2}} {f : η -> Type.{u1}} [_inst_3 : forall (i : η), Group.{u1} (f i)] [_inst_4 : DecidableEq.{succ u2} η] (I : Finset.{u2} η) {H : Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))} (x : forall (i : η), f i), (forall (i : η), (Not (Membership.mem.{u2, u2} η (Finset.{u2} η) (Finset.instMembershipFinset.{u2} η) i I)) -> (Eq.{succ u1} (f i) (x i) (OfNat.ofNat.{u1} (f i) 1 (One.toOfNat1.{u1} (f i) (InvOneClass.toOne.{u1} (f i) (DivInvOneMonoid.toInvOneClass.{u1} (f i) (DivisionMonoid.toDivInvOneMonoid.{u1} (f i) (Group.toDivisionMonoid.{u1} (f i) (_inst_3 i))))))))) -> (forall (i : η), (Membership.mem.{u2, u2} η (Finset.{u2} η) (Finset.instMembershipFinset.{u2} η) i I) -> (Membership.mem.{max u1 u2, max u2 u1} (forall (i : η), f i) (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.instMembership.{max u2 u1, max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.instSetLikeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) (Pi.mulSingle.{u2, u1} η f (fun (a : η) (b : η) => _inst_4 a b) (fun (i : η) => InvOneClass.toOne.{u1} (f i) (DivInvOneMonoid.toInvOneClass.{u1} (f i) (DivisionMonoid.toDivInvOneMonoid.{u1} (f i) (Group.toDivisionMonoid.{u1} (f i) (_inst_3 i))))) i (x i)) H)) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : η), f i) (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.instMembership.{max u2 u1, max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.instSetLikeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) x H)
Case conversion may be inaccurate. Consider using '#align subgroup.pi_mem_of_mul_single_mem_aux Subgroup.pi_mem_of_mulSingle_mem_auxₓ'. -/
@[to_additive]
theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : Subgroup (∀ i, f i)}
    (x : ∀ i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) :
    x ∈ H := by
  induction' I using Finset.induction_on with i I hnmem ih generalizing x
  · convert one_mem H
    ext i
    exact h1 i (not_mem_empty i)
  · have : x = Function.update x i 1 * Pi.mulSingle i (x i) :=
      by
      ext j
      by_cases heq : j = i
      · subst HEq
        simp
      · simp [HEq]
    rw [this]
    clear this
    apply mul_mem
    · apply ih <;> clear ih
      · intro j hj
        by_cases heq : j = i
        · subst HEq
          simp
        · simp [HEq]
          apply h1 j
          simpa [HEq] using hj
      · intro j hj
        have : j ≠ i := by
          rintro rfl
          contradiction
        simp [this]
        exact h2 _ (Finset.mem_insert_of_mem hj)
    · apply h2
      simp
#align subgroup.pi_mem_of_mul_single_mem_aux Subgroup.pi_mem_of_mulSingle_mem_aux
#align add_subgroup.pi_mem_of_single_mem_aux AddSubgroup.pi_mem_of_single_mem_aux

/- warning: subgroup.pi_mem_of_mul_single_mem -> Subgroup.pi_mem_of_mulSingle_mem is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {f : η -> Type.{u2}} [_inst_3 : forall (i : η), Group.{u2} (f i)] [_inst_4 : Finite.{succ u1} η] [_inst_5 : DecidableEq.{succ u1} η] {H : Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))} (x : forall (i : η), f i), (forall (i : η), Membership.Mem.{max u1 u2, max u1 u2} (forall (i : η), f i) (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) (Pi.mulSingle.{u1, u2} η (fun (i : η) => f i) (fun (a : η) (b : η) => _inst_5 a b) (fun (i : η) => MulOneClass.toHasOne.{u2} (f i) (Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_3 i))))) i (x i)) H) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : η), f i) (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.hasMem.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) x H)
but is expected to have type
  forall {η : Type.{u2}} {f : η -> Type.{u1}} [_inst_3 : forall (i : η), Group.{u1} (f i)] [_inst_4 : Finite.{succ u2} η] [_inst_5 : DecidableEq.{succ u2} η] {H : Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))} (x : forall (i : η), f i), (forall (i : η), Membership.mem.{max u1 u2, max u2 u1} (forall (i : η), f i) (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.instMembership.{max u2 u1, max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.instSetLikeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) (Pi.mulSingle.{u2, u1} η f (fun (a : η) (b : η) => _inst_5 a b) (fun (i : η) => InvOneClass.toOne.{u1} (f i) (DivInvOneMonoid.toInvOneClass.{u1} (f i) (DivisionMonoid.toDivInvOneMonoid.{u1} (f i) (Group.toDivisionMonoid.{u1} (f i) (_inst_3 i))))) i (x i)) H) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : η), f i) (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.instMembership.{max u2 u1, max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.instSetLikeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))) x H)
Case conversion may be inaccurate. Consider using '#align subgroup.pi_mem_of_mul_single_mem Subgroup.pi_mem_of_mulSingle_memₓ'. -/
@[to_additive]
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : Subgroup (∀ i, f i)} (x : ∀ i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H :=
  by
  cases nonempty_fintype η
  exact pi_mem_of_mul_single_mem_aux Finset.univ x (by simp) fun i _ => h i
#align subgroup.pi_mem_of_mul_single_mem Subgroup.pi_mem_of_mulSingle_mem
#align add_subgroup.pi_mem_of_single_mem AddSubgroup.pi_mem_of_single_mem

/- warning: subgroup.pi_le_iff -> Subgroup.pi_le_iff is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {f : η -> Type.{u2}} [_inst_3 : forall (i : η), Group.{u2} (f i)] [_inst_4 : DecidableEq.{succ u1} η] [_inst_5 : Finite.{succ u1} η] {H : forall (i : η), Subgroup.{u2} (f i) (_inst_3 i)} {J : Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))}, Iff (LE.le.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Preorder.toLE.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (PartialOrder.toPreorder.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))))) (Subgroup.pi.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i) (Set.univ.{u1} η) H) J) (forall (i : η), LE.le.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Preorder.toLE.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (PartialOrder.toPreorder.{max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (SetLike.partialOrder.{max u1 u2, max u1 u2} (Subgroup.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (forall (i : η), f i) (Subgroup.setLike.{max u1 u2} (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)))))) (Subgroup.map.{u2, max u1 u2} (f i) (_inst_3 i) (forall (i : η), f i) (Pi.group.{u1, u2} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)) (MonoidHom.single.{u1, u2} η f (fun (a : η) (b : η) => _inst_4 a b) (fun (i : η) => Monoid.toMulOneClass.{u2} (f i) (DivInvMonoid.toMonoid.{u2} (f i) (Group.toDivInvMonoid.{u2} (f i) (_inst_3 i)))) i) (H i)) J)
but is expected to have type
  forall {η : Type.{u2}} {f : η -> Type.{u1}} [_inst_3 : forall (i : η), Group.{u1} (f i)] [_inst_4 : DecidableEq.{succ u2} η] [_inst_5 : Finite.{succ u2} η] {H : forall (i : η), Subgroup.{u1} (f i) (_inst_3 i)} {J : Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))}, Iff (LE.le.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Preorder.toLE.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (PartialOrder.toPreorder.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Subgroup.instCompleteLatticeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))))))) (Subgroup.pi.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i) (Set.univ.{u2} η) H) J) (forall (i : η), LE.le.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Preorder.toLE.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (PartialOrder.toPreorder.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Subgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))) (Subgroup.instCompleteLatticeSubgroup.{max u2 u1} (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i))))))) (Subgroup.map.{u1, max u2 u1} (f i) (_inst_3 i) (forall (i : η), f i) (Pi.group.{u2, u1} η (fun (i : η) => f i) (fun (i : η) => _inst_3 i)) (MonoidHom.single.{u2, u1} η f (fun (a : η) (b : η) => _inst_4 a b) (fun (i : η) => Monoid.toMulOneClass.{u1} (f i) (DivInvMonoid.toMonoid.{u1} (f i) (Group.toDivInvMonoid.{u1} (f i) (_inst_3 i)))) i) (H i)) J)
Case conversion may be inaccurate. Consider using '#align subgroup.pi_le_iff Subgroup.pi_le_iffₓ'. -/
/-- For finite index types, the `subgroup.pi` is generated by the embeddings of the groups.  -/
@[to_additive
      "For finite index types, the `subgroup.pi` is generated by the embeddings of the\nadditive groups."]
theorem pi_le_iff [DecidableEq η] [Finite η] {H : ∀ i, Subgroup (f i)} {J : Subgroup (∀ i, f i)} :
    pi univ H ≤ J ↔ ∀ i : η, map (MonoidHom.single f i) (H i) ≤ J :=
  by
  constructor
  · rintro h i _ ⟨x, hx, rfl⟩
    apply h
    simpa using hx
  · exact fun h x hx => pi_mem_of_mul_single_mem x fun i => h i (mem_map_of_mem _ (hx i trivial))
#align subgroup.pi_le_iff Subgroup.pi_le_iff
#align add_subgroup.pi_le_iff AddSubgroup.pi_le_iff

end Pi

end Subgroup

namespace Subgroup

section Normalizer

/- warning: subgroup.mem_normalizer_fintype -> Subgroup.mem_normalizer_fintype is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {S : Set.{u1} G} [_inst_3 : Finite.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} G) Type.{u1} (Set.hasCoeToSort.{u1} G) S)] {x : G}, (forall (n : G), (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) n S) -> (Membership.Mem.{u1, u1} G (Set.{u1} G) (Set.hasMem.{u1} G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x n) (Inv.inv.{u1} G (DivInvMonoid.toHasInv.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) x)) S)) -> (Membership.Mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.hasMem.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) x (Subgroup.setNormalizer.{u1} G _inst_1 S))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {S : Set.{u1} G} [_inst_3 : Finite.{succ u1} (Set.Elem.{u1} G S)] {x : G}, (forall (n : G), (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) n S) -> (Membership.mem.{u1, u1} G (Set.{u1} G) (Set.instMembershipSet.{u1} G) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) (HMul.hMul.{u1, u1, u1} G G G (instHMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))) x n) (Inv.inv.{u1} G (InvOneClass.toInv.{u1} G (DivInvOneMonoid.toInvOneClass.{u1} G (DivisionMonoid.toDivInvOneMonoid.{u1} G (Group.toDivisionMonoid.{u1} G _inst_1)))) x)) S)) -> (Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x (Subgroup.setNormalizer.{u1} G _inst_1 S))
Case conversion may be inaccurate. Consider using '#align subgroup.mem_normalizer_fintype Subgroup.mem_normalizer_fintypeₓ'. -/
theorem mem_normalizer_fintype {S : Set G} [Finite S] {x : G} (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) :
    x ∈ Subgroup.setNormalizer S := by
  haveI := Classical.propDecidable <;> cases nonempty_fintype S <;>
      haveI := Set.fintypeImage S fun n => x * n * x⁻¹ <;>
    exact fun n =>
      ⟨h n, fun h₁ =>
        have heq : (fun n => x * n * x⁻¹) '' S = S :=
          Set.eq_of_subset_of_card_le (fun n ⟨y, hy⟩ => hy.2 ▸ h y hy.1)
            (by rw [Set.card_image_of_injective S conj_injective])
        have : x * n * x⁻¹ ∈ (fun n => x * n * x⁻¹) '' S := HEq.symm ▸ h₁
        let ⟨y, hy⟩ := this
        conj_injective hy.2 ▸ hy.1⟩
#align subgroup.mem_normalizer_fintype Subgroup.mem_normalizer_fintype

end Normalizer

end Subgroup

namespace MonoidHom

variable {N : Type _} [Group N]

open Subgroup

/- warning: monoid_hom.decidable_mem_range -> MonoidHom.decidableMemRange is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) [_inst_4 : Fintype.{u1} G] [_inst_5 : DecidableEq.{succ u2} N], DecidablePred.{succ u2} N (fun (_x : N) => Membership.Mem.{u2, u2} N (Subgroup.{u2} N _inst_3) (SetLike.hasMem.{u2, u2} (Subgroup.{u2} N _inst_3) N (Subgroup.setLike.{u2} N _inst_3)) _x (MonoidHom.range.{u1, u2} G _inst_1 N _inst_3 f))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))) [_inst_4 : Fintype.{u1} G] [_inst_5 : DecidableEq.{succ u2} N], DecidablePred.{succ u2} N (fun (_x : N) => Membership.mem.{u2, u2} N (Subgroup.{u2} N _inst_3) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} N _inst_3) N (Subgroup.instSetLikeSubgroup.{u2} N _inst_3)) _x (MonoidHom.range.{u1, u2} G _inst_1 N _inst_3 f))
Case conversion may be inaccurate. Consider using '#align monoid_hom.decidable_mem_range MonoidHom.decidableMemRangeₓ'. -/
@[to_additive]
instance decidableMemRange (f : G →* N) [Fintype G] [DecidableEq N] : DecidablePred (· ∈ f.range) :=
  fun x => Fintype.decidableExistsFintype
#align monoid_hom.decidable_mem_range MonoidHom.decidableMemRange
#align add_monoid_hom.decidable_mem_range AddMonoidHom.decidableMemRange

/- warning: monoid_hom.fintype_mrange -> MonoidHom.fintypeMrange is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_4 : Monoid.{u1} M] [_inst_5 : Monoid.{u2} N] [_inst_6 : Fintype.{u1} M] [_inst_7 : DecidableEq.{succ u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)), Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5)) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5)) N (Submonoid.setLike.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5))) (MonoidHom.mrange.{u1, u2, max u2 u1} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5) (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)) (MonoidHom.monoidHomClass.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)) f))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_4 : Monoid.{u1} M] [_inst_5 : Monoid.{u2} N] [_inst_6 : Fintype.{u1} M] [_inst_7 : DecidableEq.{succ u2} N] (f : MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)), Fintype.{u2} (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Submonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5)) N (Submonoid.instSetLikeSubmonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_5))) x (MonoidHom.mrange.{u1, u2, max u1 u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5) (MonoidHom.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)) (MonoidHom.monoidHomClass.{u1, u2} M N (Monoid.toMulOneClass.{u1} M _inst_4) (Monoid.toMulOneClass.{u2} N _inst_5)) f)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.fintype_mrange MonoidHom.fintypeMrangeₓ'. -/
-- this instance can't go just after the definition of `mrange` because `fintype` is
-- not imported at that stage
/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
presence of `fintype N`. -/
@[to_additive
      "The range of a finite additive monoid under an additive monoid homomorphism is\nfinite.\n\nNote: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the\npresence of `fintype N`."]
instance fintypeMrange {M N : Type _} [Monoid M] [Monoid N] [Fintype M] [DecidableEq N]
    (f : M →* N) : Fintype (mrange f) :=
  Set.fintypeRange f
#align monoid_hom.fintype_mrange MonoidHom.fintypeMrange
#align add_monoid_hom.fintype_mrange AddMonoidHom.fintypeMrange

/- warning: monoid_hom.fintype_range -> MonoidHom.fintypeRange is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : Fintype.{u1} G] [_inst_5 : DecidableEq.{succ u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))), Fintype.{u2} (coeSort.{succ u2, succ (succ u2)} (Subgroup.{u2} N _inst_3) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Subgroup.{u2} N _inst_3) N (Subgroup.setLike.{u2} N _inst_3)) (MonoidHom.range.{u1, u2} G _inst_1 N _inst_3 f))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G] {N : Type.{u2}} [_inst_3 : Group.{u2} N] [_inst_4 : Fintype.{u1} G] [_inst_5 : DecidableEq.{succ u2} N] (f : MonoidHom.{u1, u2} G N (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} N (DivInvMonoid.toMonoid.{u2} N (Group.toDivInvMonoid.{u2} N _inst_3)))), Fintype.{u2} (Subtype.{succ u2} N (fun (x : N) => Membership.mem.{u2, u2} N (Subgroup.{u2} N _inst_3) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} N _inst_3) N (Subgroup.instSetLikeSubgroup.{u2} N _inst_3)) x (MonoidHom.range.{u1, u2} G _inst_1 N _inst_3 f)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.fintype_range MonoidHom.fintypeRangeₓ'. -/
/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the
presence of `fintype N`. -/
@[to_additive
      "The range of a finite additive group under an additive group homomorphism is finite.\n\nNote: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the\npresence of `fintype N`."]
instance fintypeRange [Fintype G] [DecidableEq N] (f : G →* N) : Fintype (range f) :=
  Set.fintypeRange f
#align monoid_hom.fintype_range MonoidHom.fintypeRange
#align add_monoid_hom.fintype_range AddMonoidHom.fintypeRange

end MonoidHom

