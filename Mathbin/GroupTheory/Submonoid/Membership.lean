/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov

! This file was ported from Lean 3 source module group_theory.submonoid.membership
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.FreeMonoid.Basic
import Mathbin.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
submonoid, submonoids
-/


open BigOperators

variable {M A B : Type _}

section Assoc

variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {S : B}

namespace SubmonoidClass

/- warning: submonoid_class.coe_list_prod -> SubmonoidClass.coe_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {B : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SetLike.{u2, u1} B M] [_inst_3 : SubmonoidClass.{u2, u1} B M (Monoid.toMulOneClass.{u1} M _inst_1) _inst_2] {S : B} (l : List.{u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S)), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M B (SetLike.hasMem.{u2, u1} B M _inst_2) x S))))) (List.prod.{u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) (MulMemClass.mul.{u1, u2} M B (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) _inst_2 (SubmonoidClass.to_mulMemClass.{u2, u1} B M (Monoid.toMulOneClass.{u1} M _inst_1) _inst_2 _inst_3) S) (OneMemClass.one.{u2, u1} B M _inst_2 (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SubmonoidClass.to_oneMemClass.{u2, u1} B M (Monoid.toMulOneClass.{u1} M _inst_1) _inst_2 _inst_3) S) l)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.map.{u1, u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u2, succ (succ u1)} B Type.{u1} (SetLike.hasCoeToSort.{u2, u1} B M _inst_2) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u2} M B (SetLike.hasMem.{u2, u1} B M _inst_2) x S)))))) l))
but is expected to have type
  forall {M : Type.{u2}} {B : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : SetLike.{u1, u2} B M] [_inst_3 : SubmonoidClass.{u1, u2} B M (Monoid.toMulOneClass.{u2} M _inst_1) _inst_2] {S : B} (l : List.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S))), Eq.{succ u2} M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} B M _inst_2 S)) (List.prod.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S)) (MulOneClass.toMul.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S)) (Monoid.toMulOneClass.{u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S)) (SubmonoidClass.toMonoid.{u2, u1} M _inst_1 B _inst_2 _inst_3 S))) (OneMemClass.one.{u1, u2} B M _inst_2 (Monoid.toOne.{u2} M _inst_1) (SubmonoidClass.toOneMemClass.{u1, u2} B M (Monoid.toMulOneClass.{u2} M _inst_1) _inst_2 _inst_3) S) l)) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) (List.map.{u2, u2} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S)) M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} B M _inst_2 S))) l))
Case conversion may be inaccurate. Consider using '#align submonoid_class.coe_list_prod SubmonoidClass.coe_list_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List S) : (l.Prod : M) = (l.map coe).Prod :=
  (SubmonoidClass.Subtype S : _ →* M).map_list_prod l
#align submonoid_class.coe_list_prod SubmonoidClass.coe_list_prod
#align add_submonoid_class.coe_list_sum AddSubmonoidClass.coe_list_sum

#print SubmonoidClass.coe_multiset_prod /-
@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.Prod : M) = (m.map coe).Prod :=
  (SubmonoidClass.Subtype S : _ →* M).map_multiset_prod m
#align submonoid_class.coe_multiset_prod SubmonoidClass.coe_multiset_prod
#align add_submonoid_class.coe_multiset_sum AddSubmonoidClass.coe_multiset_sum
-/

/- warning: submonoid_class.coe_finset_prod -> SubmonoidClass.coe_finset_prod is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {S : B} {ι : Type.{u2}} {M : Type.{u3}} [_inst_4 : CommMonoid.{u3} M] [_inst_5 : SetLike.{u1, u3} B M] [_inst_6 : SubmonoidClass.{u1, u3} B M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_4)) _inst_5] (f : ι -> (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S)) (s : Finset.{u2} ι), Eq.{succ u3} M ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (coeBase.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (coeSubtype.{succ u3} M (fun (x : M) => Membership.Mem.{u3, u1} M B (SetLike.hasMem.{u1, u3} B M _inst_5) x S))))) (Finset.prod.{u3, u2} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) ι (SubmonoidClass.toCommMonoid.{u3, u1} M _inst_4 B _inst_5 _inst_6 S) s (fun (i : ι) => f i))) (Finset.prod.{u3, u2} M ι _inst_4 s (fun (i : ι) => (fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (coeBase.{succ u3, succ u3} (coeSort.{succ u1, succ (succ u3)} B Type.{u3} (SetLike.hasCoeToSort.{u1, u3} B M _inst_5) S) M (coeSubtype.{succ u3} M (fun (x : M) => Membership.Mem.{u3, u1} M B (SetLike.hasMem.{u1, u3} B M _inst_5) x S))))) (f i)))
but is expected to have type
  forall {B : Type.{u1}} {S : B} {ι : Type.{u3}} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : SetLike.{u1, u2} B M] [_inst_6 : SubmonoidClass.{u1, u2} B M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) _inst_5] (f : ι -> (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_5) x S))) (s : Finset.{u3} ι), Eq.{succ u2} M (Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} B M _inst_5 S)) (Finset.prod.{u2, u3} (Subtype.{succ u2} M (fun (x : M) => Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_5) x S)) ι (SubmonoidClass.toCommMonoid.{u2, u1} M _inst_4 B _inst_5 _inst_6 S) s (fun (i : ι) => f i))) (Finset.prod.{u2, u3} M ι _inst_4 s (fun (i : ι) => Subtype.val.{succ u2} M (fun (x : M) => Membership.mem.{u2, u2} M (Set.{u2} M) (Set.instMembershipSet.{u2} M) x (SetLike.coe.{u1, u2} B M _inst_5 S)) (f i)))
Case conversion may be inaccurate. Consider using '#align submonoid_class.coe_finset_prod SubmonoidClass.coe_finset_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  (SubmonoidClass.Subtype S : _ →* M).map_prod f s
#align submonoid_class.coe_finset_prod SubmonoidClass.coe_finset_prod
#align add_submonoid_class.coe_finset_sum AddSubmonoidClass.coe_finset_sum

end SubmonoidClass

open SubmonoidClass

/- warning: list_prod_mem -> list_prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {B : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SetLike.{u2, u1} B M] [_inst_3 : SubmonoidClass.{u2, u1} B M (Monoid.toMulOneClass.{u1} M _inst_1) _inst_2] {S : B} {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Membership.Mem.{u1, u2} M B (SetLike.hasMem.{u2, u1} B M _inst_2) x S)) -> (Membership.Mem.{u1, u2} M B (SetLike.hasMem.{u2, u1} B M _inst_2) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) S)
but is expected to have type
  forall {M : Type.{u2}} {B : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : SetLike.{u1, u2} B M] [_inst_3 : SubmonoidClass.{u1, u2} B M (Monoid.toMulOneClass.{u2} M _inst_1) _inst_2] {S : B} {l : List.{u2} M}, (forall (x : M), (Membership.mem.{u2, u2} M (List.{u2} M) (List.instMembershipList.{u2} M) x l) -> (Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) x S)) -> (Membership.mem.{u2, u1} M B (SetLike.instMembership.{u1, u2} B M _inst_2) (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l) S)
Case conversion may be inaccurate. Consider using '#align list_prod_mem list_prod_memₓ'. -/
/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.Prod ∈ S :=
  by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop
#align list_prod_mem list_prod_mem
#align list_sum_mem list_sum_mem

#print multiset_prod_mem /-
/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.Prod ∈ S :=
  by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop
#align multiset_prod_mem multiset_prod_mem
#align multiset_sum_mem multiset_sum_mem
-/

/- warning: prod_mem -> prod_mem is a dubious translation:
lean 3 declaration is
  forall {B : Type.{u1}} {S : B} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] [_inst_5 : SetLike.{u1, u2} B M] [_inst_6 : SubmonoidClass.{u1, u2} B M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)) _inst_5] {ι : Type.{u3}} {t : Finset.{u3} ι} {f : ι -> M}, (forall (c : ι), (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) c t) -> (Membership.Mem.{u2, u1} M B (SetLike.hasMem.{u1, u2} B M _inst_5) (f c) S)) -> (Membership.Mem.{u2, u1} M B (SetLike.hasMem.{u1, u2} B M _inst_5) (Finset.prod.{u2, u3} M ι _inst_4 t (fun (c : ι) => f c)) S)
but is expected to have type
  forall {B : Type.{u2}} {S : B} {M : Type.{u3}} [_inst_4 : CommMonoid.{u3} M] [_inst_5 : SetLike.{u2, u3} B M] [_inst_6 : SubmonoidClass.{u2, u3} B M (Monoid.toMulOneClass.{u3} M (CommMonoid.toMonoid.{u3} M _inst_4)) _inst_5] {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> M}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u3, u2} M B (SetLike.instMembership.{u2, u3} B M _inst_5) (f c) S)) -> (Membership.mem.{u3, u2} M B (SetLike.instMembership.{u2, u3} B M _inst_5) (Finset.prod.{u3, u1} M ι _inst_4 t (fun (c : ι) => f c)) S)
Case conversion may be inaccurate. Consider using '#align prod_mem prod_memₓ'. -/
/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type _}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  multiset_prod_mem (t.1.map f) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align prod_mem prod_mem
#align sum_mem sum_mem

namespace Submonoid

variable (s : Submonoid M)

/- warning: submonoid.coe_list_prod -> Submonoid.coe_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (l : List.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s)), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s))))) (List.prod.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Submonoid.one.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) l)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) s) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s)))))) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (l : List.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s))), Eq.{succ u1} M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) s)) (List.prod.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s)) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Submonoid.one.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) l)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.map.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s)) M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) s))) l))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_list_prod Submonoid.coe_list_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_list_prod (l : List s) : (l.Prod : M) = (l.map coe).Prod :=
  s.Subtype.map_list_prod l
#align submonoid.coe_list_prod Submonoid.coe_list_prod
#align add_submonoid.coe_list_sum AddSubmonoid.coe_list_sum

/- warning: submonoid.coe_multiset_prod -> Submonoid.coe_multiset_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (m : Multiset.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S)), Eq.{succ u1} M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S))))) (Multiset.prod.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) (Submonoid.toCommMonoid.{u1} M _inst_4 S) m)) (Multiset.prod.{u1} M _inst_4 (Multiset.map.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) S) M (coeSubtype.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S)))))) m))
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (m : Multiset.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S))), Eq.{succ u1} M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) S)) (Multiset.prod.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S)) (Submonoid.toCommMonoid.{u1} M _inst_4 S) m)) (Multiset.prod.{u1} M _inst_4 (Multiset.map.{u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S)) M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) S))) m))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_multiset_prod Submonoid.coe_multiset_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.Prod : M) = (m.map coe).Prod :=
  S.Subtype.map_multiset_prod m
#align submonoid.coe_multiset_prod Submonoid.coe_multiset_prod
#align add_submonoid.coe_multiset_sum AddSubmonoid.coe_multiset_sum

/- warning: submonoid.coe_finset_prod -> Submonoid.coe_finset_prod is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] (S : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) (f : ι -> (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S)) (s : Finset.{u1} ι), Eq.{succ u2} M ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (coeSubtype.{succ u2} M (fun (x : M) => Membership.Mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) x S))))) (Finset.prod.{u2, u1} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) ι (Submonoid.toCommMonoid.{u2} M _inst_4 S) s (fun (i : ι) => f i))) (Finset.prod.{u2, u1} M ι _inst_4 s (fun (i : ι) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) Type.{u2} (SetLike.hasCoeToSort.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) S) M (coeSubtype.{succ u2} M (fun (x : M) => Membership.Mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) (SetLike.hasMem.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.setLike.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) x S))))) (f i)))
but is expected to have type
  forall {ι : Type.{u2}} {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (f : ι -> (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S))) (s : Finset.{u2} ι), Eq.{succ u1} M (Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) S)) (Finset.prod.{u1, u2} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) x S)) ι (Submonoid.toCommMonoid.{u1} M _inst_4 S) s (fun (i : ι) => f i))) (Finset.prod.{u1, u2} M ι _inst_4 s (fun (i : ι) => Subtype.val.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) S)) (f i)))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_finset_prod Submonoid.coe_finset_prodₓ'. -/
@[simp, norm_cast, to_additive]
theorem coe_finset_prod {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
  S.Subtype.map_prod f s
#align submonoid.coe_finset_prod Submonoid.coe_finset_prod
#align add_submonoid.coe_finset_sum AddSubmonoid.coe_finset_sum

/- warning: submonoid.list_prod_mem -> Submonoid.list_prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) {l : List.{u1} M}, (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) s)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) {l : List.{u1} M}, (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x s)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) s)
Case conversion may be inaccurate. Consider using '#align submonoid.list_prod_mem Submonoid.list_prod_memₓ'. -/
/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.Prod ∈ s :=
  by
  lift l to List s using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop
#align submonoid.list_prod_mem Submonoid.list_prod_mem
#align add_submonoid.list_sum_mem AddSubmonoid.list_sum_mem

/- warning: submonoid.multiset_prod_mem -> Submonoid.multiset_prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (m : Multiset.{u1} M), (forall (a : M), (Membership.Mem.{u1, u1} M (Multiset.{u1} M) (Multiset.hasMem.{u1} M) a m) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) a S)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (Multiset.prod.{u1} M _inst_4 m) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (m : Multiset.{u1} M), (forall (a : M), (Membership.mem.{u1, u1} M (Multiset.{u1} M) (Multiset.instMembershipMultiset.{u1} M) a m) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) a S)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (Multiset.prod.{u1} M _inst_4 m) S)
Case conversion may be inaccurate. Consider using '#align submonoid.multiset_prod_mem Submonoid.multiset_prod_memₓ'. -/
/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive
      "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is\nin the `add_submonoid`."]
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.Prod ∈ S :=
  by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop
#align submonoid.multiset_prod_mem Submonoid.multiset_prod_mem
#align add_submonoid.multiset_sum_mem AddSubmonoid.multiset_sum_mem

/- warning: submonoid.multiset_noncomm_prod_mem -> Submonoid.multiset_noncommProd_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (m : Multiset.{u1} M) (comm : Set.Pairwise.{u1} M (setOf.{u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Multiset.{u1} M) (Multiset.hasMem.{u1} M) x m)) (Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))), (forall (x : M), (Membership.Mem.{u1, u1} M (Multiset.{u1} M) (Multiset.hasMem.{u1} M) x m) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x S)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Multiset.noncommProd.{u1} M _inst_1 m comm) S)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (m : Multiset.{u1} M) (comm : Set.Pairwise.{u1} M (setOf.{u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Multiset.{u1} M) (Multiset.instMembershipMultiset.{u1} M) x m)) (Commute.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))), (forall (x : M), (Membership.mem.{u1, u1} M (Multiset.{u1} M) (Multiset.instMembershipMultiset.{u1} M) x m) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x S)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Multiset.noncommProd.{u1} M _inst_1 m comm) S)
Case conversion may be inaccurate. Consider using '#align submonoid.multiset_noncomm_prod_mem Submonoid.multiset_noncommProd_memₓ'. -/
@[to_additive]
theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S :=
  by
  induction' m using Quotient.inductionOn with l
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h
#align submonoid.multiset_noncomm_prod_mem Submonoid.multiset_noncommProd_mem
#align add_submonoid.multiset_noncomm_sum_mem AddSubmonoid.multiset_noncommSum_mem

/- warning: submonoid.prod_mem -> Submonoid.prod_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_4 : CommMonoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) {ι : Type.{u2}} {t : Finset.{u2} ι} {f : ι -> M}, (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (f c) S)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_4)))) (Finset.prod.{u1, u2} M ι _inst_4 t (fun (c : ι) => f c)) S)
but is expected to have type
  forall {M : Type.{u2}} [_inst_4 : CommMonoid.{u2} M] (S : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) {ι : Type.{u1}} {t : Finset.{u1} ι} {f : ι -> M}, (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) (f c) S)) -> (Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4))) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M (CommMonoid.toMonoid.{u2} M _inst_4)))) (Finset.prod.{u2, u1} M ι _inst_4 t (fun (c : ι) => f c)) S)
Case conversion may be inaccurate. Consider using '#align submonoid.prod_mem Submonoid.prod_memₓ'. -/
/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive
      "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`\nis in the `add_submonoid`."]
theorem prod_mem {M : Type _} [CommMonoid M] (S : Submonoid M) {ι : Type _} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c in t, f c) ∈ S :=
  S.multiset_prod_mem (t.1.map f) fun x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi
#align submonoid.prod_mem Submonoid.prod_mem
#align add_submonoid.sum_mem AddSubmonoid.sum_mem

/- warning: submonoid.noncomm_prod_mem -> Submonoid.noncommProd_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (S : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) {ι : Type.{u2}} (t : Finset.{u2} ι) (f : ι -> M) (comm : Set.Pairwise.{u2} ι ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) t) (fun (a : ι) (b : ι) => Commute.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (f a) (f b))), (forall (c : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) c t) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (f c) S)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Finset.noncommProd.{u2, u1} ι M _inst_1 t f comm) S)
but is expected to have type
  forall {M : Type.{u2}} [_inst_1 : Monoid.{u2} M] (S : Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) {ι : Type.{u1}} (t : Finset.{u1} ι) (f : ι -> M) (comm : Set.Pairwise.{u1} ι (Finset.toSet.{u1} ι t) (fun (a : ι) (b : ι) => Commute.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (f a) (f b))), (forall (c : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) c t) -> (Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (f c) S)) -> (Membership.mem.{u2, u2} M (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (SetLike.instMembership.{u2, u2} (Submonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1))) (Finset.noncommProd.{u1, u2} ι M _inst_1 t f comm) S)
Case conversion may be inaccurate. Consider using '#align submonoid.noncomm_prod_mem Submonoid.noncommProd_memₓ'. -/
@[to_additive]
theorem noncommProd_mem (S : Submonoid M) {ι : Type _} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S :=
  by
  apply multiset_noncomm_prod_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx
#align submonoid.noncomm_prod_mem Submonoid.noncommProd_mem
#align add_submonoid.noncomm_sum_mem AddSubmonoid.noncommSum_mem

end Submonoid

end Assoc

section NonAssoc

variable [MulOneClass M]

open Set

namespace Submonoid

/- warning: submonoid.mem_supr_of_directed -> Submonoid.mem_supᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} [hι : Nonempty.{u2} ι] {S : ι -> (Submonoid.{u1} M _inst_1)}, (Directed.{u1, u2} (Submonoid.{u1} M _inst_1) ι (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) S) -> (forall {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))) (Exists.{u2} ι (fun (i : ι) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (S i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} [hι : Nonempty.{u2} ι] {S : ι -> (Submonoid.{u1} M _inst_1)}, (Directed.{u1, u2} (Submonoid.{u1} M _inst_1) ι (fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1220 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1222 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1220 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1222) S) -> (forall {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))) (Exists.{u2} ι (fun (i : ι) => Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (S i))))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_supr_of_directed Submonoid.mem_supᵢ_of_directedₓ'. -/
-- TODO: this section can be generalized to `[submonoid_class B M] [complete_lattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`
@[to_additive]
theorem mem_supᵢ_of_directed {ι} [hι : Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S)
    {x : M} : (x ∈ ⨆ i, S i) ↔ ∃ i, x ∈ S i :=
  by
  refine' ⟨_, fun ⟨i, hi⟩ => (SetLike.le_def.1 <| le_supᵢ S i) hi⟩
  suffices x ∈ closure (⋃ i, (S i : Set M)) → ∃ i, x ∈ S i by
    simpa only [closure_unionᵢ, closure_eq (S _)] using this
  refine' fun hx => closure_induction hx (fun _ => mem_Union.1) _ _
  · exact hι.elim fun i => ⟨i, (S i).one_mem⟩
  · rintro x y ⟨i, hi⟩ ⟨j, hj⟩
    rcases hS i j with ⟨k, hki, hkj⟩
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩
#align submonoid.mem_supr_of_directed Submonoid.mem_supᵢ_of_directed
#align add_submonoid.mem_supr_of_directed AddSubmonoid.mem_supᵢ_of_directed

/- warning: submonoid.coe_supr_of_directed -> Submonoid.coe_supᵢ_of_directed is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} [_inst_2 : Nonempty.{u2} ι] {S : ι -> (Submonoid.{u1} M _inst_1)}, (Directed.{u1, u2} (Submonoid.{u1} M _inst_1) ι (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) S) -> (Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))) (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (S i))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} [_inst_2 : Nonempty.{u2} ι] {S : ι -> (Submonoid.{u1} M _inst_1)}, (Directed.{u1, u2} (Submonoid.{u1} M _inst_1) ι (fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1465 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1467 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1465 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1467) S) -> (Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))) (Set.unionᵢ.{u1, u2} M ι (fun (i : ι) => SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (S i))))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_supr_of_directed Submonoid.coe_supᵢ_of_directedₓ'. -/
@[to_additive]
theorem coe_supᵢ_of_directed {ι} [Nonempty ι] {S : ι → Submonoid M} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Submonoid M) : Set M) = ⋃ i, ↑(S i) :=
  Set.ext fun x => by simp [mem_supr_of_directed hS]
#align submonoid.coe_supr_of_directed Submonoid.coe_supᵢ_of_directed
#align add_submonoid.coe_supr_of_directed AddSubmonoid.coe_supᵢ_of_directed

/- warning: submonoid.mem_Sup_of_directed_on -> Submonoid.mem_supₛ_of_directedOn is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)}, (Set.Nonempty.{u1} (Submonoid.{u1} M _inst_1) S) -> (DirectedOn.{u1} (Submonoid.{u1} M _inst_1) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) S) -> (forall {x : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) S)) (Exists.{succ u1} (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => Exists.{0} (Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x s))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)}, (Set.Nonempty.{u1} (Submonoid.{u1} M _inst_1) S) -> (DirectedOn.{u1} (Submonoid.{u1} M _inst_1) (fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1555 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1557 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1555 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1557) S) -> (forall {x : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) S)) (Exists.{succ u1} (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => And (Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s))))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_Sup_of_directed_on Submonoid.mem_supₛ_of_directedOnₓ'. -/
@[to_additive]
theorem mem_supₛ_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) {x : M} : x ∈ supₛ S ↔ ∃ s ∈ S, x ∈ s :=
  by
  haveI : Nonempty S := Sne.to_subtype
  simp only [supₛ_eq_supᵢ', mem_supr_of_directed hS.directed_coe, SetCoe.exists, Subtype.coe_mk]
#align submonoid.mem_Sup_of_directed_on Submonoid.mem_supₛ_of_directedOn
#align add_submonoid.mem_Sup_of_directed_on AddSubmonoid.mem_supₛ_of_directedOn

/- warning: submonoid.coe_Sup_of_directed_on -> Submonoid.coe_supₛ_of_directedOn is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)}, (Set.Nonempty.{u1} (Submonoid.{u1} M _inst_1) S) -> (DirectedOn.{u1} (Submonoid.{u1} M _inst_1) (LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1))))) S) -> (Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) S)) (Set.unionᵢ.{u1, succ u1} M (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => Set.unionᵢ.{u1, 0} M (Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) (fun (H : Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M _inst_1) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M _inst_1) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)))) s))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)}, (Set.Nonempty.{u1} (Submonoid.{u1} M _inst_1) S) -> (DirectedOn.{u1} (Submonoid.{u1} M _inst_1) (fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1645 : Submonoid.{u1} M _inst_1) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1647 : Submonoid.{u1} M _inst_1) => LE.le.{u1} (Submonoid.{u1} M _inst_1) (Preorder.toLE.{u1} (Submonoid.{u1} M _inst_1) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1))))) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1645 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.1647) S) -> (Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) S)) (Set.unionᵢ.{u1, succ u1} M (Submonoid.{u1} M _inst_1) (fun (s : Submonoid.{u1} M _inst_1) => Set.unionᵢ.{u1, 0} M (Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) (fun (H : Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) => SetLike.coe.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align submonoid.coe_Sup_of_directed_on Submonoid.coe_supₛ_of_directedOnₓ'. -/
@[to_additive]
theorem coe_supₛ_of_directedOn {S : Set (Submonoid M)} (Sne : S.Nonempty)
    (hS : DirectedOn (· ≤ ·) S) : (↑(supₛ S) : Set M) = ⋃ s ∈ S, ↑s :=
  Set.ext fun x => by simp [mem_Sup_of_directed_on Sne hS]
#align submonoid.coe_Sup_of_directed_on Submonoid.coe_supₛ_of_directedOn
#align add_submonoid.coe_Sup_of_directed_on AddSubmonoid.coe_supₛ_of_directedOn

/- warning: submonoid.mem_sup_left -> Submonoid.mem_sup_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_sup_left Submonoid.mem_sup_leftₓ'. -/
@[to_additive]
theorem mem_sup_left {S T : Submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
  show S ≤ S ⊔ T from le_sup_left
#align submonoid.mem_sup_left Submonoid.mem_sup_left
#align add_submonoid.mem_sup_left AddSubmonoid.mem_sup_left

/- warning: submonoid.mem_sup_right -> Submonoid.mem_sup_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x T) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x T) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_sup_right Submonoid.mem_sup_rightₓ'. -/
@[to_additive]
theorem mem_sup_right {S T : Submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
  show T ≤ S ⊔ T from le_sup_right
#align submonoid.mem_sup_right Submonoid.mem_sup_right
#align add_submonoid.mem_sup_right AddSubmonoid.mem_sup_right

/- warning: submonoid.mul_mem_sup -> Submonoid.mul_mem_sup is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M} {y : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x S) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y T) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1)))) S T))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Submonoid.{u1} M _inst_1} {T : Submonoid.{u1} M _inst_1} {x : M} {y : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x S) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y T) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) (HasSup.sup.{u1} (Submonoid.{u1} M _inst_1) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)))) S T))
Case conversion may be inaccurate. Consider using '#align submonoid.mul_mem_sup Submonoid.mul_mem_supₓ'. -/
@[to_additive]
theorem mul_mem_sup {S T : Submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
#align submonoid.mul_mem_sup Submonoid.mul_mem_sup
#align add_submonoid.add_mem_sup AddSubmonoid.add_mem_sup

/- warning: submonoid.mem_supr_of_mem -> Submonoid.mem_supᵢ_of_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)} (i : ι) {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (S i)) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι S))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} {S : ι -> (Submonoid.{u1} M _inst_1)} (i : ι) {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (S i)) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι S))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_supr_of_mem Submonoid.mem_supᵢ_of_memₓ'. -/
@[to_additive]
theorem mem_supᵢ_of_mem {ι : Sort _} {S : ι → Submonoid M} (i : ι) :
    ∀ {x : M}, x ∈ S i → x ∈ supᵢ S :=
  show S i ≤ supᵢ S from le_supᵢ _ _
#align submonoid.mem_supr_of_mem Submonoid.mem_supᵢ_of_mem
#align add_submonoid.mem_supr_of_mem AddSubmonoid.mem_supᵢ_of_mem

/- warning: submonoid.mem_Sup_of_mem -> Submonoid.mem_supₛ_of_mem is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)} {s : Submonoid.{u1} M _inst_1}, (Membership.Mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.hasMem.{u1} (Submonoid.{u1} M _inst_1)) s S) -> (forall {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x s) -> (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) S)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {S : Set.{u1} (Submonoid.{u1} M _inst_1)} {s : Submonoid.{u1} M _inst_1}, (Membership.mem.{u1, u1} (Submonoid.{u1} M _inst_1) (Set.{u1} (Submonoid.{u1} M _inst_1)) (Set.instMembershipSet.{u1} (Submonoid.{u1} M _inst_1)) s S) -> (forall {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x s) -> (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (SupSet.supₛ.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) S)))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_Sup_of_mem Submonoid.mem_supₛ_of_memₓ'. -/
@[to_additive]
theorem mem_supₛ_of_mem {S : Set (Submonoid M)} {s : Submonoid M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ supₛ S :=
  show s ≤ supₛ S from le_supₛ hs
#align submonoid.mem_Sup_of_mem Submonoid.mem_supₛ_of_mem
#align add_submonoid.mem_Sup_of_mem AddSubmonoid.mem_supₛ_of_mem

/- warning: submonoid.supr_induction -> Submonoid.supᵢ_induction is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (S : ι -> (Submonoid.{u1} M _inst_1)) {C : M -> Prop} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))) -> (forall (i : ι) (x : M), (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (S i)) -> (C x)) -> (C (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1))))) -> (forall (x : M) (y : M), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y))) -> (C x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (S : ι -> (Submonoid.{u1} M _inst_1)) {C : M -> Prop} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))) -> (forall (i : ι) (x : M), (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (S i)) -> (C x)) -> (C (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (C x) -> (C y) -> (C (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y))) -> (C x)
Case conversion may be inaccurate. Consider using '#align submonoid.supr_induction Submonoid.supᵢ_inductionₓ'. -/
/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_elim,
  to_additive
      " An induction principle for elements of `⨆ i, S i`.\nIf `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,\nthen it holds for all elements of the supremum of `S`. "]
theorem supᵢ_induction {ι : Sort _} (S : ι → Submonoid M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
    (hp : ∀ (i), ∀ x ∈ S i, C x) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y)) : C x :=
  by
  rw [supr_eq_closure] at hx
  refine' closure_induction hx (fun x hx => _) h1 hmul
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx
  exact hp _ _ hi
#align submonoid.supr_induction Submonoid.supᵢ_induction
#align add_submonoid.supr_induction AddSubmonoid.supᵢ_induction

/- warning: submonoid.supr_induction' -> Submonoid.supᵢ_induction' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (S : ι -> (Submonoid.{u1} M _inst_1)) {C : forall (x : M), (Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))) -> Prop}, (forall (i : ι) (x : M) (H : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (S i)), C x (Submonoid.mem_supᵢ_of_mem.{u1, u2} M _inst_1 ι (fun (i : ι) => S i) i x H)) -> (C (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M _inst_1)))) (OneMemClass.one_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toHasOne.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (SubmonoidClass.to_oneMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoidClass.{u1} M _inst_1)) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i)))) -> (forall (x : M) (y : M) (hx : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))) (hy : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) y (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))), (C x hx) -> (C y hy) -> (C (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M _inst_1)) x y) (MulMemClass.mul_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toHasMul.{u1} M _inst_1) (Submonoid.setLike.{u1} M _inst_1) (SubmonoidClass.to_mulMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.setLike.{u1} M _inst_1) (Submonoid.submonoidClass.{u1} M _inst_1)) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i)) x y hx hy))) -> (forall {x : M} (hx : Membership.Mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.setLike.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteSemilatticeSup.toHasSup.{u1} (Submonoid.{u1} M _inst_1) (CompleteLattice.toCompleteSemilatticeSup.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.completeLattice.{u1} M _inst_1))) ι (fun (i : ι) => S i))), C x hx)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulOneClass.{u1} M] {ι : Sort.{u2}} (S : ι -> (Submonoid.{u1} M _inst_1)) {C : forall (x : M), (Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))) -> Prop}, (forall (i : ι) (x : M) (H : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (S i)), C x (Submonoid.mem_supᵢ_of_mem.{u1, u2} M _inst_1 ι (fun (i : ι) => S i) i x H)) -> (C (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (MulOneClass.toOne.{u1} M _inst_1))) (OneMemClass.one_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toOne.{u1} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (SubmonoidClass.toOneMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u1} M _inst_1)) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i)))) -> (forall (x : M) (y : M) (hx : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))) (hy : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) y (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))), (C x hx) -> (C y hy) -> (C (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M _inst_1)) x y) (MulMemClass.mul_mem.{u1, u1} (Submonoid.{u1} M _inst_1) M (MulOneClass.toMul.{u1} M _inst_1) (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (SubmonoidClass.toMulMemClass.{u1, u1} (Submonoid.{u1} M _inst_1) M _inst_1 (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1) (Submonoid.instSubmonoidClassSubmonoidInstSetLikeSubmonoid.{u1} M _inst_1)) (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i)) x y hx hy))) -> (forall {x : M} (hx : Membership.mem.{u1, u1} M (Submonoid.{u1} M _inst_1) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M _inst_1) M (Submonoid.instSetLikeSubmonoid.{u1} M _inst_1)) x (supᵢ.{u1, u2} (Submonoid.{u1} M _inst_1) (CompleteLattice.toSupSet.{u1} (Submonoid.{u1} M _inst_1) (Submonoid.instCompleteLatticeSubmonoid.{u1} M _inst_1)) ι (fun (i : ι) => S i))), C x hx)
Case conversion may be inaccurate. Consider using '#align submonoid.supr_induction' Submonoid.supᵢ_induction'ₓ'. -/
/-- A dependent version of `submonoid.supr_induction`. -/
@[elab_as_elim, to_additive "A dependent version of `add_submonoid.supr_induction`. "]
theorem supᵢ_induction' {ι : Sort _} (S : ι → Submonoid M) {C : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    (hp : ∀ (i), ∀ x ∈ S i, C x (mem_supᵢ_of_mem i ‹_›)) (h1 : C 1 (one_mem _))
    (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›)) {x : M}
    (hx : x ∈ ⨆ i, S i) : C x hx :=
  by
  refine' Exists.elim _ fun (hx : x ∈ ⨆ i, S i) (hc : C x hx) => hc
  refine' supr_induction S hx (fun i x hx => _) _ fun x y => _
  · exact ⟨_, hp _ _ hx⟩
  · exact ⟨_, h1⟩
  · rintro ⟨_, Cx⟩ ⟨_, Cy⟩
    refine' ⟨_, hmul _ _ _ _ Cx Cy⟩
#align submonoid.supr_induction' Submonoid.supᵢ_induction'
#align add_submonoid.supr_induction' AddSubmonoid.supᵢ_induction'

end Submonoid

end NonAssoc

namespace FreeMonoid

variable {α : Type _}

open Submonoid

/- warning: free_monoid.closure_range_of -> FreeMonoid.closure_range_of is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Submonoid.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))) (Submonoid.closure.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α)))) (Set.range.{u1, succ u1} (FreeMonoid.{u1} α) α (FreeMonoid.of.{u1} α))) (Top.top.{u1} (Submonoid.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))) (Submonoid.hasTop.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.cancelMonoid.{u1} α))))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Submonoid.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (Submonoid.closure.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α)))) (Set.range.{u1, succ u1} (FreeMonoid.{u1} α) α (FreeMonoid.of.{u1} α))) (Top.top.{u1} (Submonoid.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))) (Submonoid.instTopSubmonoid.{u1} (FreeMonoid.{u1} α) (Monoid.toMulOneClass.{u1} (FreeMonoid.{u1} α) (RightCancelMonoid.toMonoid.{u1} (FreeMonoid.{u1} α) (CancelMonoid.toRightCancelMonoid.{u1} (FreeMonoid.{u1} α) (FreeMonoid.instCancelMonoidFreeMonoid.{u1} α))))))
Case conversion may be inaccurate. Consider using '#align free_monoid.closure_range_of FreeMonoid.closure_range_ofₓ'. -/
@[to_additive]
theorem closure_range_of : closure (Set.range <| @of α) = ⊤ :=
  eq_top_iff.2 fun x hx =>
    FreeMonoid.recOn x (one_mem _) fun x xs hxs =>
      mul_mem (subset_closure <| Set.mem_range_self _) hxs
#align free_monoid.closure_range_of FreeMonoid.closure_range_of
#align free_add_monoid.closure_range_of FreeAddMonoid.closure_range_of

end FreeMonoid

namespace Submonoid

variable [Monoid M]

open MonoidHom

#print Submonoid.closure_singleton_eq /-
theorem closure_singleton_eq (x : M) : closure ({x} : Set M) = (powersHom M x).mrange :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨Multiplicative.ofAdd 1, pow_one x⟩) fun x ⟨n, hn⟩ =>
    hn ▸ pow_mem (subset_closure <| Set.mem_singleton _) _
#align submonoid.closure_singleton_eq Submonoid.closure_singleton_eq
-/

/- warning: submonoid.mem_closure_singleton -> Submonoid.mem_closure_singleton is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M} {y : M}, Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) x))) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x n) y))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M} {y : M}, Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) x))) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x n) y))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_closure_singleton Submonoid.mem_closure_singletonₓ'. -/
/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
theorem mem_closure_singleton {x y : M} : y ∈ closure ({x} : Set M) ↔ ∃ n : ℕ, x ^ n = y := by
  rw [closure_singleton_eq, mem_mrange] <;> rfl
#align submonoid.mem_closure_singleton Submonoid.mem_closure_singleton

/- warning: submonoid.mem_closure_singleton_self -> Submonoid.mem_closure_singleton_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {y : M}, Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) y))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {y : M}, Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) y (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) y))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_closure_singleton_self Submonoid.mem_closure_singleton_selfₓ'. -/
theorem mem_closure_singleton_self {y : M} : y ∈ closure ({y} : Set M) :=
  mem_closure_singleton.2 ⟨1, pow_one y⟩
#align submonoid.mem_closure_singleton_self Submonoid.mem_closure_singleton_self

/- warning: submonoid.closure_singleton_one -> Submonoid.closure_singleton_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.hasSingleton.{u1} M) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))))) (Bot.bot.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasBot.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Singleton.singleton.{u1, u1} M (Set.{u1} M) (Set.instSingletonSet.{u1} M) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1))))) (Bot.bot.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instBotSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_singleton_one Submonoid.closure_singleton_oneₓ'. -/
theorem closure_singleton_one : closure ({1} : Set M) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton]
#align submonoid.closure_singleton_one Submonoid.closure_singleton_one

#print FreeMonoid.mrange_lift /-
@[to_additive]
theorem FreeMonoid.mrange_lift {α} (f : α → M) :
    (FreeMonoid.lift f).mrange = closure (Set.range f) := by
  rw [mrange_eq_map, ← FreeMonoid.closure_range_of, map_mclosure, ← Set.range_comp,
    FreeMonoid.lift_comp_of]
#align free_monoid.mrange_lift FreeMonoid.mrange_lift
#align free_add_monoid.mrange_lift FreeAddMonoid.mrange_lift
-/

#print Submonoid.closure_eq_mrange /-
@[to_additive]
theorem closure_eq_mrange (s : Set M) : closure s = (FreeMonoid.lift (coe : s → M)).mrange := by
  rw [FreeMonoid.mrange_lift, Subtype.range_coe]
#align submonoid.closure_eq_mrange Submonoid.closure_eq_mrange
#align add_submonoid.closure_eq_mrange AddSubmonoid.closure_eq_mrange
-/

/- warning: submonoid.closure_eq_image_prod -> Submonoid.closure_eq_image_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Set.{u1} M), Eq.{succ u1} (Set.{u1} M) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) (Set.image.{u1, u1} (List.{u1} M) M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (setOf.{u1} (List.{u1} M) (fun (l : List.{u1} M) => forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (s : Set.{u1} M), Eq.{succ u1} (Set.{u1} M) (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) (Set.image.{u1, u1} (List.{u1} M) M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1)) (setOf.{u1} (List.{u1} M) (fun (l : List.{u1} M) => forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s))))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_eq_image_prod Submonoid.closure_eq_image_prodₓ'. -/
@[to_additive]
theorem closure_eq_image_prod (s : Set M) :
    (closure s : Set M) = List.prod '' { l : List M | ∀ x ∈ l, x ∈ s } :=
  by
  rw [closure_eq_mrange, coe_mrange, ← List.range_map_coe, ← Set.range_comp, Function.comp]
  exact congr_arg _ (funext <| FreeMonoid.lift_apply _)
#align submonoid.closure_eq_image_prod Submonoid.closure_eq_image_prod
#align add_submonoid.closure_eq_image_sum AddSubmonoid.closure_eq_image_sum

/- warning: submonoid.exists_list_of_mem_closure -> Submonoid.exists_list_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (Exists.{succ u1} (List.{u1} M) (fun (l : List.{u1} M) => Exists.{0} (forall (y : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) y l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s)) (fun (hl : forall (y : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) y l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s)) => Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l) x)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (Exists.{succ u1} (List.{u1} M) (fun (l : List.{u1} M) => Exists.{0} (forall (y : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) y l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s)) (fun (hl : forall (y : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) y l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s)) => Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l) x)))
Case conversion may be inaccurate. Consider using '#align submonoid.exists_list_of_mem_closure Submonoid.exists_list_of_mem_closureₓ'. -/
@[to_additive]
theorem exists_list_of_mem_closure {s : Set M} {x : M} (hx : x ∈ closure s) :
    ∃ (l : List M)(hl : ∀ y ∈ l, y ∈ s), l.Prod = x := by
  rwa [← SetLike.mem_coe, closure_eq_image_prod, Set.mem_image_iff_bex] at hx
#align submonoid.exists_list_of_mem_closure Submonoid.exists_list_of_mem_closure
#align add_submonoid.exists_list_of_mem_closure AddSubmonoid.exists_list_of_mem_closure

/- warning: submonoid.exists_multiset_of_mem_closure -> Submonoid.exists_multiset_of_mem_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] {s : Set.{u1} M} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) s)) -> (Exists.{succ u1} (Multiset.{u1} M) (fun (l : Multiset.{u1} M) => Exists.{0} (forall (y : M), (Membership.Mem.{u1, u1} M (Multiset.{u1} M) (Multiset.hasMem.{u1} M) y l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s)) (fun (hl : forall (y : M), (Membership.Mem.{u1, u1} M (Multiset.{u1} M) (Multiset.hasMem.{u1} M) y l) -> (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s)) => Eq.{succ u1} M (Multiset.prod.{u1} M _inst_2 l) x)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_2 : CommMonoid.{u1} M] {s : Set.{u1} M} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2))) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_2)) s)) -> (Exists.{succ u1} (Multiset.{u1} M) (fun (l : Multiset.{u1} M) => Exists.{0} (forall (y : M), (Membership.mem.{u1, u1} M (Multiset.{u1} M) (Multiset.instMembershipMultiset.{u1} M) y l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s)) (fun (hl : forall (y : M), (Membership.mem.{u1, u1} M (Multiset.{u1} M) (Multiset.instMembershipMultiset.{u1} M) y l) -> (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s)) => Eq.{succ u1} M (Multiset.prod.{u1} M _inst_2 l) x)))
Case conversion may be inaccurate. Consider using '#align submonoid.exists_multiset_of_mem_closure Submonoid.exists_multiset_of_mem_closureₓ'. -/
@[to_additive]
theorem exists_multiset_of_mem_closure {M : Type _} [CommMonoid M] {s : Set M} {x : M}
    (hx : x ∈ closure s) : ∃ (l : Multiset M)(hl : ∀ y ∈ l, y ∈ s), l.Prod = x :=
  by
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx
  exact ⟨l, h1, (Multiset.coe_prod l).trans h2⟩
#align submonoid.exists_multiset_of_mem_closure Submonoid.exists_multiset_of_mem_closure
#align add_submonoid.exists_multiset_of_mem_closure AddSubmonoid.exists_multiset_of_mem_closure

/- warning: submonoid.closure_induction_left -> Submonoid.closure_induction_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : M), (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)))) -> (p x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : M), (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)))) -> (p x)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_induction_left Submonoid.closure_induction_leftₓ'. -/
@[to_additive]
theorem closure_induction_left {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x :=
  by
  rw [closure_eq_mrange] at h
  obtain ⟨l, rfl⟩ := h
  induction' l using FreeMonoid.recOn with x y ih
  · exact H1
  · simpa only [map_mul, FreeMonoid.lift_eval_of] using Hmul _ x.prop _ ih
#align submonoid.closure_induction_left Submonoid.closure_induction_left
#align add_submonoid.closure_induction_left AddSubmonoid.closure_induction_left

/- warning: submonoid.induction_of_closure_eq_top_left -> Submonoid.induction_of_closure_eq_top_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : M), (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)))) -> (p x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : M), (p y) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y)))) -> (p x))
Case conversion may be inaccurate. Consider using '#align submonoid.induction_of_closure_eq_top_left Submonoid.induction_of_closure_eq_top_leftₓ'. -/
@[elab_as_elim, to_additive]
theorem induction_of_closure_eq_top_left {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ x ∈ s, ∀ (y), p y → p (x * y)) : p x :=
  closure_induction_left
    (by
      rw [hs]
      exact mem_top _)
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_left Submonoid.induction_of_closure_eq_top_left
#align add_submonoid.induction_of_closure_eq_top_left AddSubmonoid.induction_of_closure_eq_top_left

/- warning: submonoid.closure_induction_right -> Submonoid.closure_induction_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (p x) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y))) -> (p x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop} {x : M}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)) -> (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s) -> (p x) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y))) -> (p x)
Case conversion may be inaccurate. Consider using '#align submonoid.closure_induction_right Submonoid.closure_induction_rightₓ'. -/
@[to_additive]
theorem closure_induction_right {s : Set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
    (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  @closure_induction_left _ _ (MulOpposite.unop ⁻¹' s) (p ∘ MulOpposite.unop) (MulOpposite.op x)
    (closure_induction h (fun x hx => subset_closure hx) (one_mem _) fun x y hx hy => mul_mem hy hx)
    H1 fun x hx y => Hmul _ _ hx
#align submonoid.closure_induction_right Submonoid.closure_induction_right
#align add_submonoid.closure_induction_right AddSubmonoid.closure_induction_right

/- warning: submonoid.induction_of_closure_eq_top_right -> Submonoid.induction_of_closure_eq_top_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (p (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) -> (forall (x : M) (y : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) y s) -> (p x) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y))) -> (p x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M} {p : M -> Prop}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (p (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) -> (forall (x : M) (y : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) y s) -> (p x) -> (p (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x y))) -> (p x))
Case conversion may be inaccurate. Consider using '#align submonoid.induction_of_closure_eq_top_right Submonoid.induction_of_closure_eq_top_rightₓ'. -/
@[elab_as_elim, to_additive]
theorem induction_of_closure_eq_top_right {s : Set M} {p : M → Prop} (hs : closure s = ⊤) (x : M)
    (H1 : p 1) (Hmul : ∀ (x), ∀ y ∈ s, p x → p (x * y)) : p x :=
  closure_induction_right
    (by
      rw [hs]
      exact mem_top _)
    H1 Hmul
#align submonoid.induction_of_closure_eq_top_right Submonoid.induction_of_closure_eq_top_right
#align add_submonoid.induction_of_closure_eq_top_right AddSubmonoid.induction_of_closure_eq_top_right

#print Submonoid.powers /-
/-- The submonoid generated by an element. -/
def powers (n : M) : Submonoid M :=
  Submonoid.copy (powersHom M n).mrange (Set.range ((· ^ ·) n : ℕ → M)) <|
    Set.ext fun n => exists_congr fun i => by simp <;> rfl
#align submonoid.powers Submonoid.powers
-/

/- warning: submonoid.mem_powers -> Submonoid.mem_powers is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M), Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) n (Submonoid.powers.{u1} M _inst_1 n)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M), Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) n (Submonoid.powers.{u1} M _inst_1 n)
Case conversion may be inaccurate. Consider using '#align submonoid.mem_powers Submonoid.mem_powersₓ'. -/
@[simp]
theorem mem_powers (n : M) : n ∈ powers n :=
  ⟨1, pow_one _⟩
#align submonoid.mem_powers Submonoid.mem_powers

/- warning: submonoid.mem_powers_iff -> Submonoid.mem_powers_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (x : M) (z : M), Iff (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 z)) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) z n) x))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (x : M) (z : M), Iff (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 z)) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) z n) x))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_powers_iff Submonoid.mem_powers_iffₓ'. -/
theorem mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x :=
  Iff.rfl
#align submonoid.mem_powers_iff Submonoid.mem_powers_iff

#print Submonoid.powers_eq_closure /-
theorem powers_eq_closure (n : M) : powers n = closure {n} :=
  by
  ext
  exact mem_closure_singleton.symm
#align submonoid.powers_eq_closure Submonoid.powers_eq_closure
-/

/- warning: submonoid.powers_subset -> Submonoid.powers_subset is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {n : M} {P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)}, (Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) n P) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.powers.{u1} M _inst_1 n) P)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {n : M} {P : Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)}, (Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) n P) -> (LE.le.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Preorder.toLE.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instCompleteLatticeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Submonoid.powers.{u1} M _inst_1 n) P)
Case conversion may be inaccurate. Consider using '#align submonoid.powers_subset Submonoid.powers_subsetₓ'. -/
theorem powers_subset {n : M} {P : Submonoid M} (h : n ∈ P) : powers n ≤ P := fun x hx =>
  match x, hx with
  | _, ⟨i, rfl⟩ => pow_mem h i
#align submonoid.powers_subset Submonoid.powers_subset

/- warning: submonoid.powers_one -> Submonoid.powers_one is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.powers.{u1} M _inst_1 (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))))) (Bot.bot.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasBot.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M], Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.powers.{u1} M _inst_1 (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M _inst_1)))) (Bot.bot.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instBotSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))
Case conversion may be inaccurate. Consider using '#align submonoid.powers_one Submonoid.powers_oneₓ'. -/
@[simp]
theorem powers_one : powers (1 : M) = ⊥ :=
  bot_unique <| powers_subset (one_mem _)
#align submonoid.powers_one Submonoid.powers_one

/- warning: submonoid.pow -> Submonoid.pow is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M), Nat -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M), Nat -> (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n)))
Case conversion may be inaccurate. Consider using '#align submonoid.pow Submonoid.powₓ'. -/
/-- Exponentiation map from natural numbers to powers. -/
@[simps]
def pow (n : M) (m : ℕ) : powers n :=
  (powersHom M n).mrangeRestrict (Multiplicative.ofAdd m)
#align submonoid.pow Submonoid.pow

/- warning: submonoid.pow_apply -> Submonoid.pow_apply is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M) (m : Nat), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (Submonoid.pow.{u1} M _inst_1 n m) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.Mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m) (Exists.intro.{1} Nat (fun (y : Nat) => Eq.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n y) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) m (rfl.{succ u1} M (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (n : M) (m : Nat), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Submonoid.pow.{u1} M _inst_1 n m) (Subtype.mk.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n)) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m) (Exists.intro.{1} Nat (fun (y : Nat) => Eq.{succ u1} M ((fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3541 : M) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3543 : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3541 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3543) n y) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) m (rfl.{succ u1} M ((fun (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3541 : M) (x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3543 : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3541 x._@.Mathlib.GroupTheory.Submonoid.Membership._hyg.3543) n m))))
Case conversion may be inaccurate. Consider using '#align submonoid.pow_apply Submonoid.pow_applyₓ'. -/
theorem pow_apply (n : M) (m : ℕ) : Submonoid.pow n m = ⟨n ^ m, m, rfl⟩ :=
  rfl
#align submonoid.pow_apply Submonoid.pow_apply

/- warning: submonoid.log -> Submonoid.log is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) -> Nat
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) -> Nat
Case conversion may be inaccurate. Consider using '#align submonoid.log Submonoid.logₓ'. -/
/-- Logarithms from powers to natural numbers. -/
def log [DecidableEq M] {n : M} (p : powers n) : ℕ :=
  Nat.find <| (mem_powers_iff p.val n).mp p.Prop
#align submonoid.log Submonoid.log

/- warning: submonoid.pow_log_eq_self -> Submonoid.pow_log_eq_self is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M} (p : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)), Eq.{succ u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (Submonoid.pow.{u1} M _inst_1 n (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n p)) p
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M} (p : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))), Eq.{succ u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Submonoid.pow.{u1} M _inst_1 n (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n p)) p
Case conversion may be inaccurate. Consider using '#align submonoid.pow_log_eq_self Submonoid.pow_log_eq_selfₓ'. -/
@[simp]
theorem pow_log_eq_self [DecidableEq M] {n : M} (p : powers n) : pow n (log p) = p :=
  Subtype.ext <| Nat.find_spec p.Prop
#align submonoid.pow_log_eq_self Submonoid.pow_log_eq_self

/- warning: submonoid.pow_right_injective_iff_pow_injective -> Submonoid.pow_right_injective_iff_pow_injective is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {n : M}, Iff (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) (Function.Injective.{1, succ u1} Nat (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (Submonoid.pow.{u1} M _inst_1 n))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {n : M}, Iff (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) (Function.Injective.{1, succ u1} Nat (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Submonoid.pow.{u1} M _inst_1 n))
Case conversion may be inaccurate. Consider using '#align submonoid.pow_right_injective_iff_pow_injective Submonoid.pow_right_injective_iff_pow_injectiveₓ'. -/
theorem pow_right_injective_iff_pow_injective {n : M} :
    (Function.Injective fun m : ℕ => n ^ m) ↔ Function.Injective (pow n) :=
  Subtype.coe_injective.of_comp_iff (pow n)
#align submonoid.pow_right_injective_iff_pow_injective Submonoid.pow_right_injective_iff_pow_injective

#print Submonoid.log_pow_eq_self /-
@[simp]
theorem log_pow_eq_self [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (m : ℕ) : log (pow n m) = m :=
  pow_right_injective_iff_pow_injective.mp h <| pow_log_eq_self _
#align submonoid.log_pow_eq_self Submonoid.log_pow_eq_self
-/

/- warning: submonoid.pow_log_equiv -> Submonoid.powLogEquiv is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) -> (MulEquiv.{0, u1} (Multiplicative.{0} Nat) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (Multiplicative.hasMul.{0} Nat Nat.hasAdd) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.powers.{u1} M _inst_1 n)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) -> (MulEquiv.{0, u1} (Multiplicative.{0} Nat) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Multiplicative.mul.{0} Nat instAddNat) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.powers.{u1} M _inst_1 n)))
Case conversion may be inaccurate. Consider using '#align submonoid.pow_log_equiv Submonoid.powLogEquivₓ'. -/
/-- The exponentiation map is an isomorphism from the additive monoid on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def powLogEquiv [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m) :
    Multiplicative ℕ ≃* powers n where
  toFun m := pow n m.toAdd
  invFun m := Multiplicative.ofAdd (log m)
  left_inv := log_pow_eq_self h
  right_inv := pow_log_eq_self
  map_mul' _ _ := by simp only [pow, map_mul, ofAdd_add, toAdd_mul]
#align submonoid.pow_log_equiv Submonoid.powLogEquiv

/- warning: submonoid.log_mul -> Submonoid.log_mul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) -> (forall (x : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (y : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)), Eq.{1} Nat (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n (HMul.hMul.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (instHMul.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.powers.{u1} M _inst_1 n)) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.powers.{u1} M _inst_1 n))) x y)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n x) (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n y)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : DecidableEq.{succ u1} M] {n : M}, (Function.Injective.{1, succ u1} Nat M (fun (m : Nat) => HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n m)) -> (forall (x : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (y : Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))), Eq.{1} Nat (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n (HMul.hMul.{u1, u1, u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (instHMul.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.powers.{u1} M _inst_1 n))) (Submonoid.mul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) (Submonoid.powers.{u1} M _inst_1 n))) x y)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n x) (Submonoid.log.{u1} M _inst_1 (fun (a : M) (b : M) => _inst_2 a b) n y)))
Case conversion may be inaccurate. Consider using '#align submonoid.log_mul Submonoid.log_mulₓ'. -/
theorem log_mul [DecidableEq M] {n : M} (h : Function.Injective fun m : ℕ => n ^ m)
    (x y : powers (n : M)) : log (x * y) = log x + log y :=
  (powLogEquiv h).symm.map_mul x y
#align submonoid.log_mul Submonoid.log_mul

/- warning: submonoid.log_pow_int_eq_self -> Submonoid.log_pow_int_eq_self is a dubious translation:
lean 3 declaration is
  forall {x : Int}, (LT.lt.{0} Nat Nat.hasLt (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))) (Int.natAbs x)) -> (forall (m : Nat), Eq.{1} Nat (Submonoid.log.{0} Int Int.monoid (fun (a : Int) (b : Int) => Int.decidableEq a b) x (Submonoid.pow.{0} Int Int.monoid x m)) m)
but is expected to have type
  forall {x : Int}, (LT.lt.{0} Nat instLTNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) (Int.natAbs x)) -> (forall (m : Nat), Eq.{1} Nat (Submonoid.log.{0} Int Int.instMonoidInt (fun (a : Int) (b : Int) => Int.instDecidableEqInt a b) x (Submonoid.pow.{0} Int Int.instMonoidInt x m)) m)
Case conversion may be inaccurate. Consider using '#align submonoid.log_pow_int_eq_self Submonoid.log_pow_int_eq_selfₓ'. -/
theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.natAbs) (m : ℕ) : log (pow x m) = m :=
  (powLogEquiv (Int.pow_right_injective h)).symm_apply_apply _
#align submonoid.log_pow_int_eq_self Submonoid.log_pow_int_eq_self

/- warning: submonoid.map_powers -> Submonoid.map_powers is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {N : Type.{u2}} {F : Type.{u3}} [_inst_2 : Monoid.{u2} N] [_inst_3 : MonoidHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2)] (f : F) (m : M), Eq.{succ u2} (Submonoid.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (Submonoid.map.{u1, u2, u3} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) F _inst_3 f (Submonoid.powers.{u1} M _inst_1 m)) (Submonoid.powers.{u2} N _inst_2 (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> N) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => N) (MulHomClass.toFunLike.{u3, u1, u2} F M N (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u2} N _inst_2) _inst_3))) f m))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {N : Type.{u3}} {F : Type.{u2}} [_inst_2 : Monoid.{u3} N] [_inst_3 : MonoidHomClass.{u2, u1, u3} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2)] (f : F) (m : M), Eq.{succ u3} (Submonoid.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (Submonoid.map.{u1, u3, u2} M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2) F _inst_3 f (Submonoid.powers.{u1} M _inst_1 m)) (Submonoid.powers.{u3} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) m) _inst_2 (FunLike.coe.{succ u2, succ u1, succ u3} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => N) _x) (MulHomClass.toFunLike.{u2, u1, u3} F M N (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toMul.{u3} N (Monoid.toMulOneClass.{u3} N _inst_2)) (MonoidHomClass.toMulHomClass.{u2, u1, u3} F M N (Monoid.toMulOneClass.{u1} M _inst_1) (Monoid.toMulOneClass.{u3} N _inst_2) _inst_3)) f m))
Case conversion may be inaccurate. Consider using '#align submonoid.map_powers Submonoid.map_powersₓ'. -/
@[simp]
theorem map_powers {N : Type _} {F : Type _} [Monoid N] [MonoidHomClass F M N] (f : F) (m : M) :
    (powers m).map f = powers (f m) := by
  simp only [powers_eq_closure, map_mclosure f, Set.image_singleton]
#align submonoid.map_powers Submonoid.map_powers

/- warning: submonoid.closure_comm_monoid_of_comm -> Submonoid.closureCommMonoidOfComm is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M}, (forall (a : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) a s) -> (forall (b : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) b s) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a)))) -> (CommMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {s : Set.{u1} M}, (forall (a : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) a s) -> (forall (b : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) b s) -> (Eq.{succ u1} M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) a b) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) b a)))) -> (CommMonoid.{u1} (Subtype.{succ u1} M (fun (x : M) => Membership.mem.{u1, u1} M (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align submonoid.closure_comm_monoid_of_comm Submonoid.closureCommMonoidOfCommₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (a b «expr ∈ » s) -/
/-- If all the elements of a set `s` commute, then `closure s` is a commutative monoid. -/
@[to_additive
      "If all the elements of a set `s` commute, then `closure s` forms an additive\ncommutative monoid."]
def closureCommMonoidOfComm {s : Set M} (hcomm : ∀ (a) (_ : a ∈ s) (b) (_ : b ∈ s), a * b = b * a) :
    CommMonoid (closure s) :=
  { (closure s).toMonoid with
    mul_comm := fun x y => by
      ext
      simp only [Submonoid.coe_mul]
      exact
        closure_induction₂ x.prop y.prop hcomm Commute.one_left Commute.one_right
          (fun x y z => Commute.mul_left) fun x y z => Commute.mul_right }
#align submonoid.closure_comm_monoid_of_comm Submonoid.closureCommMonoidOfComm
#align add_submonoid.closure_add_comm_monoid_of_comm AddSubmonoid.closureAddCommMonoidOfComm

end Submonoid

/- warning: is_scalar_tower.of_mclosure_eq_top -> IsScalarTower.of_mclosure_eq_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u2} M N _inst_1] [_inst_3 : SMul.{u2, u3} N α] [_inst_4 : MulAction.{u1, u3} M α _inst_1] {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : N) (z : α), Eq.{succ u3} α (SMul.smul.{u2, u3} N α _inst_3 (SMul.smul.{u1, u2} M N (MulAction.toHasSmul.{u1, u2} M N _inst_1 _inst_2) x y) z) (SMul.smul.{u1, u3} M α (MulAction.toHasSmul.{u1, u3} M α _inst_1 _inst_4) x (SMul.smul.{u2, u3} N α _inst_3 y z)))) -> (IsScalarTower.{u1, u2, u3} M N α (MulAction.toHasSmul.{u1, u2} M N _inst_1 _inst_2) _inst_3 (MulAction.toHasSmul.{u1, u3} M α _inst_1 _inst_4))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : MulAction.{u1, u3} M N _inst_1] [_inst_3 : SMul.{u3, u2} N α] [_inst_4 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : N) (z : α), Eq.{succ u2} α (HSMul.hSMul.{u3, u2, u2} N α α (instHSMul.{u3, u2} N α _inst_3) (HSMul.hSMul.{u1, u3, u3} M N N (instHSMul.{u1, u3} M N (MulAction.toSMul.{u1, u3} M N _inst_1 _inst_2)) x y) z) (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_4)) x (HSMul.hSMul.{u3, u2, u2} N α α (instHSMul.{u3, u2} N α _inst_3) y z)))) -> (IsScalarTower.{u1, u3, u2} M N α (MulAction.toSMul.{u1, u3} M N _inst_1 _inst_2) _inst_3 (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_4))
Case conversion may be inaccurate. Consider using '#align is_scalar_tower.of_mclosure_eq_top IsScalarTower.of_mclosure_eq_topₓ'. -/
@[to_additive]
theorem IsScalarTower.of_mclosure_eq_top {N α} [Monoid M] [MulAction M N] [SMul N α] [MulAction M α]
    {s : Set M} (htop : Submonoid.closure s = ⊤)
    (hs : ∀ x ∈ s, ∀ (y : N) (z : α), (x • y) • z = x • y • z) : IsScalarTower M N α :=
  by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  · intro y z
    rw [one_smul, one_smul]
  · clear x
    intro x hx x' hx' y z
    rw [mul_smul, mul_smul, hs x hx, hx']
#align is_scalar_tower.of_mclosure_eq_top IsScalarTower.of_mclosure_eq_top
#align vadd_assoc_class.of_mclosure_eq_top VAddAssocClass.of_mclosure_eq_top

/- warning: smul_comm_class.of_mclosure_eq_top -> SMulCommClass.of_mclosure_eq_top is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} {α : Type.{u3}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SMul.{u2, u3} N α] [_inst_3 : MulAction.{u1, u3} M α _inst_1] {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.hasTop.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (Membership.Mem.{u1, u1} M (Set.{u1} M) (Set.hasMem.{u1} M) x s) -> (forall (y : N) (z : α), Eq.{succ u3} α (SMul.smul.{u1, u3} M α (MulAction.toHasSmul.{u1, u3} M α _inst_1 _inst_3) x (SMul.smul.{u2, u3} N α _inst_2 y z)) (SMul.smul.{u2, u3} N α _inst_2 y (SMul.smul.{u1, u3} M α (MulAction.toHasSmul.{u1, u3} M α _inst_1 _inst_3) x z)))) -> (SMulCommClass.{u1, u2, u3} M N α (MulAction.toHasSmul.{u1, u3} M α _inst_1 _inst_3) _inst_2)
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u3}} {α : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : SMul.{u3, u2} N α] [_inst_3 : MulAction.{u1, u2} M α _inst_1] {s : Set.{u1} M}, (Eq.{succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.closure.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1) s) (Top.top.{u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.instTopSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) -> (forall (x : M), (Membership.mem.{u1, u1} M (Set.{u1} M) (Set.instMembershipSet.{u1} M) x s) -> (forall (y : N) (z : α), Eq.{succ u2} α (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_3)) x (HSMul.hSMul.{u3, u2, u2} N α α (instHSMul.{u3, u2} N α _inst_2) y z)) (HSMul.hSMul.{u3, u2, u2} N α α (instHSMul.{u3, u2} N α _inst_2) y (HSMul.hSMul.{u1, u2, u2} M α α (instHSMul.{u1, u2} M α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_3)) x z)))) -> (SMulCommClass.{u1, u3, u2} M N α (MulAction.toSMul.{u1, u2} M α _inst_1 _inst_3) _inst_2)
Case conversion may be inaccurate. Consider using '#align smul_comm_class.of_mclosure_eq_top SMulCommClass.of_mclosure_eq_topₓ'. -/
@[to_additive]
theorem SMulCommClass.of_mclosure_eq_top {N α} [Monoid M] [SMul N α] [MulAction M α] {s : Set M}
    (htop : Submonoid.closure s = ⊤) (hs : ∀ x ∈ s, ∀ (y : N) (z : α), x • y • z = y • x • z) :
    SMulCommClass M N α :=
  by
  refine' ⟨fun x => Submonoid.induction_of_closure_eq_top_left htop x _ _⟩
  · intro y z
    rw [one_smul, one_smul]
  · clear x
    intro x hx x' hx' y z
    rw [mul_smul, mul_smul, hx', hs x hx]
#align smul_comm_class.of_mclosure_eq_top SMulCommClass.of_mclosure_eq_top
#align vadd_comm_class.of_mclosure_eq_top VAddCommClass.of_mclosure_eq_top

namespace Submonoid

variable {N : Type _} [CommMonoid N]

open MonoidHom

/- warning: submonoid.sup_eq_range -> Submonoid.sup_eq_range is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_1 : CommMonoid.{u1} N] (s : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (t : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))), Eq.{succ u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (HasSup.sup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Submonoid.completeLattice.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))))) s t) (MonoidHom.mrange.{u1, u1, u1} (Prod.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t)) N (Prod.mulOneClass.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) (MonoidHom.{u1, u1} (Prod.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t)) N (Prod.mulOneClass.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} (Prod.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t)) N (Prod.mulOneClass.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (MonoidHom.coprod.{u1, u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) s) (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) t) N (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t) _inst_1 (Submonoid.subtype.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.subtype.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)))
but is expected to have type
  forall {N : Type.{u1}} [_inst_1 : CommMonoid.{u1} N] (s : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (t : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))), Eq.{succ u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (HasSup.sup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Submonoid.instCompleteLatticeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))))) s t) (MonoidHom.mrange.{u1, u1, u1} (Prod.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t))) N (Prod.instMulOneClassProd.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t)) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) (MonoidHom.{u1, u1} (Prod.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t))) N (Prod.instMulOneClassProd.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t)) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (MonoidHom.monoidHomClass.{u1, u1} (Prod.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t))) N (Prod.instMulOneClassProd.{u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t)) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)) (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (MonoidHom.coprod.{u1, u1, u1} (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x s)) (Subtype.{succ u1} N (fun (x : N) => Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x t)) N (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.toMulOneClass.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t) _inst_1 (Submonoid.subtype.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) s) (Submonoid.subtype.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)) t)))
Case conversion may be inaccurate. Consider using '#align submonoid.sup_eq_range Submonoid.sup_eq_rangeₓ'. -/
@[to_additive]
theorem sup_eq_range (s t : Submonoid N) : s ⊔ t = (s.Subtype.coprod t.Subtype).mrange := by
  rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl, map_mrange,
    coprod_comp_inr, range_subtype, range_subtype]
#align submonoid.sup_eq_range Submonoid.sup_eq_range
#align add_submonoid.sup_eq_range AddSubmonoid.sup_eq_range

/- warning: submonoid.mem_sup -> Submonoid.mem_sup is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_1 : CommMonoid.{u1} N] {s : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))} {t : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))} {x : N}, Iff (Membership.Mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x (HasSup.sup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Submonoid.completeLattice.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))))) s t)) (Exists.{succ u1} N (fun (y : N) => Exists.{0} (Membership.Mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) y s) (fun (H : Membership.Mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) y s) => Exists.{succ u1} N (fun (z : N) => Exists.{0} (Membership.Mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) z t) (fun (H : Membership.Mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.setLike.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) z t) => Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toHasMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) y z) x)))))
but is expected to have type
  forall {N : Type.{u1}} [_inst_1 : CommMonoid.{u1} N] {s : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))} {t : Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))} {x : N}, Iff (Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) x (HasSup.sup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SemilatticeSup.toHasSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Lattice.toSemilatticeSup.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (CompleteLattice.toLattice.{u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (Submonoid.instCompleteLatticeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))))) s t)) (Exists.{succ u1} N (fun (y : N) => And (Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) y s) (Exists.{succ u1} N (fun (z : N) => And (Membership.mem.{u1, u1} N (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1))) N (Submonoid.instSetLikeSubmonoid.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) z t) (Eq.{succ u1} N (HMul.hMul.{u1, u1, u1} N N N (instHMul.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N (CommMonoid.toMonoid.{u1} N _inst_1)))) y z) x)))))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_sup Submonoid.mem_supₓ'. -/
@[to_additive]
theorem mem_sup {s t : Submonoid N} {x : N} : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x := by
  simp only [sup_eq_range, mem_mrange, coprod_apply, Prod.exists, SetLike.exists, coeSubtype,
    Subtype.coe_mk]
#align submonoid.mem_sup Submonoid.mem_sup
#align add_submonoid.mem_sup AddSubmonoid.mem_sup

end Submonoid

namespace AddSubmonoid

variable [AddMonoid A]

open Set

#print AddSubmonoid.closure_singleton_eq /-
theorem closure_singleton_eq (x : A) : closure ({x} : Set A) = (multiplesHom A x).mrange :=
  closure_eq_of_le (Set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩) fun x ⟨n, hn⟩ =>
    hn ▸ nsmul_mem (subset_closure <| Set.mem_singleton _) _
#align add_submonoid.closure_singleton_eq AddSubmonoid.closure_singleton_eq
-/

/- warning: add_submonoid.mem_closure_singleton -> AddSubmonoid.mem_closure_singleton is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {x : A} {y : A}, Iff (Membership.Mem.{u1, u1} A (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (SetLike.hasMem.{u1, u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) A (AddSubmonoid.setLike.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1))) y (AddSubmonoid.closure.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1) (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.hasSingleton.{u1} A) x))) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} A (SMul.smul.{0, u1} Nat A (AddMonoid.SMul.{u1} A _inst_1) n x) y))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {x : A} {y : A}, Iff (Membership.mem.{u1, u1} A (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (SetLike.instMembership.{u1, u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) A (AddSubmonoid.instSetLikeAddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1))) y (AddSubmonoid.closure.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1) (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.instSingletonSet.{u1} A) x))) (Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} A (HSMul.hSMul.{0, u1, u1} Nat A A (instHSMul.{0, u1} Nat A (AddMonoid.SMul.{u1} A _inst_1)) n x) y))
Case conversion may be inaccurate. Consider using '#align add_submonoid.mem_closure_singleton AddSubmonoid.mem_closure_singletonₓ'. -/
/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
theorem mem_closure_singleton {x y : A} : y ∈ closure ({x} : Set A) ↔ ∃ n : ℕ, n • x = y := by
  rw [closure_singleton_eq, AddMonoidHom.mem_mrange] <;> rfl
#align add_submonoid.mem_closure_singleton AddSubmonoid.mem_closure_singleton

/- warning: add_submonoid.closure_singleton_zero -> AddSubmonoid.closure_singleton_zero is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A], Eq.{succ u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddSubmonoid.closure.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1) (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.hasSingleton.{u1} A) (OfNat.ofNat.{u1} A 0 (OfNat.mk.{u1} A 0 (Zero.zero.{u1} A (AddZeroClass.toHasZero.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1))))))) (Bot.bot.{u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddSubmonoid.hasBot.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A], Eq.{succ u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddSubmonoid.closure.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1) (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.instSingletonSet.{u1} A) (OfNat.ofNat.{u1} A 0 (Zero.toOfNat0.{u1} A (AddMonoid.toZero.{u1} A _inst_1))))) (Bot.bot.{u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddSubmonoid.instBotAddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)))
Case conversion may be inaccurate. Consider using '#align add_submonoid.closure_singleton_zero AddSubmonoid.closure_singleton_zeroₓ'. -/
theorem closure_singleton_zero : closure ({0} : Set A) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]
#align add_submonoid.closure_singleton_zero AddSubmonoid.closure_singleton_zero

#print AddSubmonoid.multiples /-
/-- The additive submonoid generated by an element. -/
def multiples (x : A) : AddSubmonoid A :=
  AddSubmonoid.copy (multiplesHom A x).mrange (Set.range (fun i => i • x : ℕ → A)) <|
    Set.ext fun n => exists_congr fun i => by simp <;> rfl
#align add_submonoid.multiples AddSubmonoid.multiples
-/

attribute [to_additive multiples] Submonoid.powers

attribute [to_additive mem_multiples] Submonoid.mem_powers

attribute [to_additive mem_multiples_iff] Submonoid.mem_powers_iff

attribute [to_additive multiples_eq_closure] Submonoid.powers_eq_closure

attribute [to_additive multiples_subset] Submonoid.powers_subset

attribute [to_additive multiples_zero] Submonoid.powers_one

end AddSubmonoid

/-! Lemmas about additive closures of `subsemigroup`. -/


namespace MulMemClass

variable {R : Type _} [NonUnitalNonAssocSemiring R] [SetLike M R] [MulMemClass M R] {S : M}
  {a b : R}

/- warning: mul_mem_class.mul_right_mem_add_closure -> MulMemClass.mul_right_mem_add_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) _inst_2] {S : M} {a : R} {b : R}, (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) a (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S))) -> (Membership.Mem.{u2, u1} R M (SetLike.hasMem.{u1, u2} M R _inst_2) b S) -> (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S)))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1) _inst_2] {S : M} {a : R} {b : R}, (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) a (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S))) -> (Membership.mem.{u2, u1} R M (SetLike.instMembership.{u1, u2} M R _inst_2) b S) -> (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S)))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.mul_right_mem_add_closure MulMemClass.mul_right_mem_add_closureₓ'. -/
/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
theorem mul_right_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R)) (hb : b ∈ S) :
    a * b ∈ AddSubmonoid.closure (S : Set R) :=
  by
  revert b
  refine' AddSubmonoid.closure_induction ha _ _ _ <;> clear ha a
  · exact fun r hr b hb => add_submonoid.mem_closure.mpr fun y hy => hy (mul_mem hr hb)
  · exact fun b hb => by simp only [zero_mul, (AddSubmonoid.closure (S : Set R)).zero_mem]
  · simp_rw [add_mul]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
#align mul_mem_class.mul_right_mem_add_closure MulMemClass.mul_right_mem_add_closure

/- warning: mul_mem_class.mul_mem_add_closure -> MulMemClass.mul_mem_add_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) _inst_2] {S : M} {a : R} {b : R}, (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) a (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S))) -> (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) b (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S))) -> (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S)))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1) _inst_2] {S : M} {a : R} {b : R}, (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) a (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S))) -> (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) b (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S))) -> (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S)))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.mul_mem_add_closure MulMemClass.mul_mem_add_closureₓ'. -/
/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
theorem mul_mem_add_closure (ha : a ∈ AddSubmonoid.closure (S : Set R))
    (hb : b ∈ AddSubmonoid.closure (S : Set R)) : a * b ∈ AddSubmonoid.closure (S : Set R) :=
  by
  revert a
  refine' AddSubmonoid.closure_induction hb _ _ _ <;> clear hb b
  · exact fun r hr b hb => MulMemClass.mul_right_mem_add_closure hb hr
  · exact fun b hb => by simp only [mul_zero, (AddSubmonoid.closure (S : Set R)).zero_mem]
  · simp_rw [mul_add]
    exact fun r s hr hs b hb => (AddSubmonoid.closure (S : Set R)).add_mem (hr hb) (hs hb)
#align mul_mem_class.mul_mem_add_closure MulMemClass.mul_mem_add_closure

/- warning: mul_mem_class.mul_left_mem_add_closure -> MulMemClass.mul_left_mem_add_closure is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) _inst_2] {S : M} {a : R} {b : R}, (Membership.Mem.{u2, u1} R M (SetLike.hasMem.{u1, u2} M R _inst_2) a S) -> (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) b (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S))) -> (Membership.Mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.hasMem.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.setLike.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) ((fun (a : Type.{u1}) (b : Type.{u2}) [self : HasLiftT.{succ u1, succ u2} a b] => self.0) M (Set.{u2} R) (HasLiftT.mk.{succ u1, succ u2} M (Set.{u2} R) (CoeTCₓ.coe.{succ u1, succ u2} M (Set.{u2} R) (SetLike.Set.hasCoeT.{u1, u2} M R _inst_2))) S)))
but is expected to have type
  forall {M : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] [_inst_2 : SetLike.{u1, u2} M R] [_inst_3 : MulMemClass.{u1, u2} M R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1) _inst_2] {S : M} {a : R} {b : R}, (Membership.mem.{u2, u1} R M (SetLike.instMembership.{u1, u2} M R _inst_2) a S) -> (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) b (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S))) -> (Membership.mem.{u2, u2} R (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) (SetLike.instMembership.{u2, u2} (AddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1)))) R (AddSubmonoid.instSetLikeAddSubmonoid.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))))) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) a b) (AddSubmonoid.closure.{u2} R (AddMonoid.toAddZeroClass.{u2} R (AddCommMonoid.toAddMonoid.{u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R _inst_1))) (SetLike.coe.{u1, u2} M R _inst_2 S)))
Case conversion may be inaccurate. Consider using '#align mul_mem_class.mul_left_mem_add_closure MulMemClass.mul_left_mem_add_closureₓ'. -/
/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
theorem mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ AddSubmonoid.closure (S : Set R)) :
    a * b ∈ AddSubmonoid.closure (S : Set R) :=
  mul_mem_add_closure (AddSubmonoid.mem_closure.mpr fun sT hT => hT ha) hb
#align mul_mem_class.mul_left_mem_add_closure MulMemClass.mul_left_mem_add_closure

end MulMemClass

namespace Submonoid

/- warning: submonoid.mem_closure_pair -> Submonoid.mem_closure_pair is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : CommMonoid.{u1} A] (a : A) (b : A) (c : A), Iff (Membership.Mem.{u1, u1} A (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) (SetLike.hasMem.{u1, u1} (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) A (Submonoid.setLike.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)))) c (Submonoid.closure.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)) (Insert.insert.{u1, u1} A (Set.{u1} A) (Set.hasInsert.{u1} A) a (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.hasSingleton.{u1} A) b)))) (Exists.{1} Nat (fun (m : Nat) => Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (MulOneClass.toHasMul.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)))) (HPow.hPow.{u1, 0, u1} A Nat A (instHPow.{u1, 0} A Nat (Monoid.Pow.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) a m) (HPow.hPow.{u1, 0, u1} A Nat A (instHPow.{u1, 0} A Nat (Monoid.Pow.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) b n)) c)))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : CommMonoid.{u1} A] (a : A) (b : A) (c : A), Iff (Membership.mem.{u1, u1} A (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) A (Submonoid.instSetLikeSubmonoid.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)))) c (Submonoid.closure.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)) (Insert.insert.{u1, u1} A (Set.{u1} A) (Set.instInsertSet.{u1} A) a (Singleton.singleton.{u1, u1} A (Set.{u1} A) (Set.instSingletonSet.{u1} A) b)))) (Exists.{1} Nat (fun (m : Nat) => Exists.{1} Nat (fun (n : Nat) => Eq.{succ u1} A (HMul.hMul.{u1, u1, u1} A A A (instHMul.{u1} A (MulOneClass.toMul.{u1} A (Monoid.toMulOneClass.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1)))) (HPow.hPow.{u1, 0, u1} A Nat A (instHPow.{u1, 0} A Nat (Monoid.Pow.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) a m) (HPow.hPow.{u1, 0, u1} A Nat A (instHPow.{u1, 0} A Nat (Monoid.Pow.{u1} A (CommMonoid.toMonoid.{u1} A _inst_1))) b n)) c)))
Case conversion may be inaccurate. Consider using '#align submonoid.mem_closure_pair Submonoid.mem_closure_pairₓ'. -/
/-- An element is in the closure of a two-element set if it is a linear combination of those two
elements. -/
@[to_additive
      "An element is in the closure of a two-element set if it is a linear combination of\nthose two elements."]
theorem mem_closure_pair {A : Type _} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c :=
  by
  rw [← Set.singleton_union, Submonoid.closure_union, mem_sup]
  simp_rw [exists_prop, mem_closure_singleton, exists_exists_eq_and]
#align submonoid.mem_closure_pair Submonoid.mem_closure_pair
#align add_submonoid.mem_closure_pair AddSubmonoid.mem_closure_pair

end Submonoid

section mul_add

/- warning: of_mul_image_powers_eq_multiples_of_mul -> ofMul_image_powers_eq_multiples_ofMul is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M}, Eq.{succ u1} (Set.{u1} (Additive.{u1} M)) (Set.image.{u1, u1} M (Additive.{u1} M) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) (fun (_x : Equiv.{succ u1, succ u1} M (Additive.{u1} M)) => M -> (Additive.{u1} M)) (Equiv.hasCoeToFun.{succ u1, succ u1} M (Additive.{u1} M)) (Additive.ofMul.{u1} M)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Set.{u1} M) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.setLike.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (Submonoid.powers.{u1} M _inst_1 x))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubmonoid.{u1} (Additive.{u1} M) (AddMonoid.toAddZeroClass.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1))) (Set.{u1} (Additive.{u1} M)) (HasLiftT.mk.{succ u1, succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (AddMonoid.toAddZeroClass.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1))) (Set.{u1} (Additive.{u1} M)) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubmonoid.{u1} (Additive.{u1} M) (AddMonoid.toAddZeroClass.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1))) (Set.{u1} (Additive.{u1} M)) (SetLike.Set.hasCoeT.{u1, u1} (AddSubmonoid.{u1} (Additive.{u1} M) (AddMonoid.toAddZeroClass.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1))) (Additive.{u1} M) (AddSubmonoid.setLike.{u1} (Additive.{u1} M) (AddMonoid.toAddZeroClass.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1)))))) (AddSubmonoid.multiples.{u1} (Additive.{u1} M) (Additive.addMonoid.{u1} M _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) (fun (_x : Equiv.{succ u1, succ u1} M (Additive.{u1} M)) => M -> (Additive.{u1} M)) (Equiv.hasCoeToFun.{succ u1, succ u1} M (Additive.{u1} M)) (Additive.ofMul.{u1} M) x)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] {x : M}, Eq.{succ u1} (Set.{u1} (Additive.{u1} M)) (Set.image.{u1, u1} M (Additive.{u1} M) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (Additive.{u1} M) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (Additive.{u1} M) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} M (Additive.{u1} M)))) (Additive.ofMul.{u1} M)) (SetLike.coe.{u1, u1} (Submonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) M (Submonoid.instSetLikeSubmonoid.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Submonoid.powers.{u1} M _inst_1 x))) (SetLike.coe.{u1, u1} (AddSubmonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) x) (AddMonoid.toAddZeroClass.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) x) (Additive.addMonoid.{u1} M _inst_1))) (Additive.{u1} M) (AddSubmonoid.instSetLikeAddSubmonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) x) (AddMonoid.toAddZeroClass.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) x) (Additive.addMonoid.{u1} M _inst_1))) (AddSubmonoid.multiples.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) x) (Additive.addMonoid.{u1} M _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (fun (_x : M) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : M) => Additive.{u1} M) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (Additive.{u1} M) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} M (Additive.{u1} M)) M (Additive.{u1} M) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} M (Additive.{u1} M)))) (Additive.ofMul.{u1} M) x)))
Case conversion may be inaccurate. Consider using '#align of_mul_image_powers_eq_multiples_of_mul ofMul_image_powers_eq_multiples_ofMulₓ'. -/
theorem ofMul_image_powers_eq_multiples_ofMul [Monoid M] {x : M} :
    Additive.ofMul '' (Submonoid.powers x : Set M) = AddSubmonoid.multiples (Additive.ofMul x) :=
  by
  ext
  constructor
  · rintro ⟨y, ⟨n, hy1⟩, hy2⟩
    use n
    simpa [← ofMul_pow, hy1]
  · rintro ⟨n, hn⟩
    refine' ⟨x ^ n, ⟨n, rfl⟩, _⟩
    rwa [ofMul_pow]
#align of_mul_image_powers_eq_multiples_of_mul ofMul_image_powers_eq_multiples_ofMul

/- warning: of_add_image_multiples_eq_powers_of_add -> ofAdd_image_multiples_eq_powers_ofAdd is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {x : A}, Eq.{succ u1} (Set.{u1} (Multiplicative.{u1} A)) (Set.image.{u1, u1} A (Multiplicative.{u1} A) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) (fun (_x : Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) => A -> (Multiplicative.{u1} A)) (Equiv.hasCoeToFun.{succ u1, succ u1} A (Multiplicative.{u1} A)) (Multiplicative.ofAdd.{u1} A)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (Set.{u1} A) (HasLiftT.mk.{succ u1, succ u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (Set.{u1} A) (CoeTCₓ.coe.{succ u1, succ u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (Set.{u1} A) (SetLike.Set.hasCoeT.{u1, u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) A (AddSubmonoid.setLike.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1))))) (AddSubmonoid.multiples.{u1} A _inst_1 x))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Submonoid.{u1} (Multiplicative.{u1} A) (Monoid.toMulOneClass.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1))) (Set.{u1} (Multiplicative.{u1} A)) (HasLiftT.mk.{succ u1, succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Monoid.toMulOneClass.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1))) (Set.{u1} (Multiplicative.{u1} A)) (CoeTCₓ.coe.{succ u1, succ u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Monoid.toMulOneClass.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1))) (Set.{u1} (Multiplicative.{u1} A)) (SetLike.Set.hasCoeT.{u1, u1} (Submonoid.{u1} (Multiplicative.{u1} A) (Monoid.toMulOneClass.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1))) (Multiplicative.{u1} A) (Submonoid.setLike.{u1} (Multiplicative.{u1} A) (Monoid.toMulOneClass.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1)))))) (Submonoid.powers.{u1} (Multiplicative.{u1} A) (Multiplicative.monoid.{u1} A _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) (fun (_x : Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) => A -> (Multiplicative.{u1} A)) (Equiv.hasCoeToFun.{succ u1, succ u1} A (Multiplicative.{u1} A)) (Multiplicative.ofAdd.{u1} A) x)))
but is expected to have type
  forall {A : Type.{u1}} [_inst_1 : AddMonoid.{u1} A] {x : A}, Eq.{succ u1} (Set.{u1} (Multiplicative.{u1} A)) (Set.image.{u1, u1} A (Multiplicative.{u1} A) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (fun (_x : A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (Multiplicative.{u1} A) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (Multiplicative.{u1} A) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} A (Multiplicative.{u1} A)))) (Multiplicative.ofAdd.{u1} A)) (SetLike.coe.{u1, u1} (AddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) A (AddSubmonoid.instSetLikeAddSubmonoid.{u1} A (AddMonoid.toAddZeroClass.{u1} A _inst_1)) (AddSubmonoid.multiples.{u1} A _inst_1 x))) (SetLike.coe.{u1, u1} (Submonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) x) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) x) (Multiplicative.monoid.{u1} A _inst_1))) (Multiplicative.{u1} A) (Submonoid.instSetLikeSubmonoid.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) x) (Monoid.toMulOneClass.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) x) (Multiplicative.monoid.{u1} A _inst_1))) (Submonoid.powers.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) x) (Multiplicative.monoid.{u1} A _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (fun (_x : A) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : A) => Multiplicative.{u1} A) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (Multiplicative.{u1} A) (EquivLike.toEmbeddingLike.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} A (Multiplicative.{u1} A)) A (Multiplicative.{u1} A) (Equiv.instEquivLikeEquiv.{succ u1, succ u1} A (Multiplicative.{u1} A)))) (Multiplicative.ofAdd.{u1} A) x)))
Case conversion may be inaccurate. Consider using '#align of_add_image_multiples_eq_powers_of_add ofAdd_image_multiples_eq_powers_ofAddₓ'. -/
theorem ofAdd_image_multiples_eq_powers_ofAdd [AddMonoid A] {x : A} :
    Multiplicative.ofAdd '' (AddSubmonoid.multiples x : Set A) =
      Submonoid.powers (Multiplicative.ofAdd x) :=
  by
  symm
  rw [Equiv.eq_image_iff_symm_image_eq]
  exact ofMul_image_powers_eq_multiples_ofMul
#align of_add_image_multiples_eq_powers_of_add ofAdd_image_multiples_eq_powers_ofAdd

end mul_add

