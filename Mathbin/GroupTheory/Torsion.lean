/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman

! This file was ported from Lean 3 source module group_theory.torsion
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Exponent
import Mathbin.GroupTheory.OrderOfElement
import Mathbin.GroupTheory.PGroup
import Mathbin.GroupTheory.QuotientGroup
import Mathbin.GroupTheory.Submonoid.Operations

/-!
# Torsion groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `comm_group.torsion G`, the torsion subgroup of an abelian group `G`
* `comm_monoid.torsion G`, the above stated for commutative monoids
* `monoid.is_torsion_free`, asserting no nontrivial elements have finite order in `G`
* `add_monoid.is_torsion` and `add_monoid.is_torsion_free` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `monoid.is_torsion.group`), but since
the definition can be stated on monoids it is implemented on `monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/


variable {G H : Type _}

namespace Monoid

variable (G) [Monoid G]

#print Monoid.IsTorsion /-
/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def IsTorsion :=
  ∀ g : G, IsOfFinOrder g
#align monoid.is_torsion Monoid.IsTorsion
#align add_monoid.is_torsion AddMonoid.IsTorsion
-/

#print Monoid.not_isTorsion_iff /-
/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[simp,
  to_additive "An additive monoid is not a torsion monoid if it has an element of infinite order."]
theorem not_isTorsion_iff : ¬IsTorsion G ↔ ∃ g : G, ¬IsOfFinOrder g := by
  rw [is_torsion, not_forall]
#align monoid.not_is_torsion_iff Monoid.not_isTorsion_iff
#align add_monoid.not_is_torsion_iff AddMonoid.not_isTorsion_iff
-/

end Monoid

open Monoid

#print IsTorsion.group /-
/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def IsTorsion.group [Monoid G] (tG : IsTorsion G) : Group G :=
  { ‹Monoid G› with
    inv := fun g => g ^ (orderOf g - 1)
    mul_left_inv := fun g =>
      by
      erw [← pow_succ', tsub_add_cancel_of_le, pow_orderOf_eq_one]
      exact orderOf_pos' (tG g) }
#align is_torsion.group IsTorsion.group
#align is_torsion.add_group IsTorsion.addGroup
-/

section Group

variable [Group G] {N : Subgroup G} [Group H]

/- warning: is_torsion.subgroup -> IsTorsion.subgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], (Monoid.IsTorsion.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) -> (forall (H : Subgroup.{u1} G _inst_1), Monoid.IsTorsion.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], (Monoid.IsTorsion.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) -> (forall (H : Subgroup.{u1} G _inst_1), Monoid.IsTorsion.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Submonoid.toMonoid.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Subgroup.toSubmonoid.{u1} G _inst_1 H)))
Case conversion may be inaccurate. Consider using '#align is_torsion.subgroup IsTorsion.subgroupₓ'. -/
/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
theorem IsTorsion.subgroup (tG : IsTorsion G) (H : Subgroup G) : IsTorsion H := fun h =>
  (isOfFinOrder_iff_coe H.toSubmonoid h).mpr <| tG h
#align is_torsion.subgroup IsTorsion.subgroup
#align is_torsion.add_subgroup IsTorsion.addSubgroup

/- warning: is_torsion.of_surjective -> IsTorsion.of_surjective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Group.{u1} G] [_inst_2 : Group.{u2} H] {f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) f)) -> (Monoid.IsTorsion.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) -> (Monoid.IsTorsion.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Group.{u2} G] [_inst_2 : Group.{u1} H] {f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))}, (Function.Surjective.{succ u2, succ u1} G H (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))))) f)) -> (Monoid.IsTorsion.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) -> (Monoid.IsTorsion.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align is_torsion.of_surjective IsTorsion.of_surjectiveₓ'. -/
/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive AddIsTorsion.of_surjective
      "The image of a surjective additive torsion group homomorphism is torsion."]
theorem IsTorsion.of_surjective {f : G →* H} (hf : Function.Surjective f) (tG : IsTorsion G) :
    IsTorsion H := fun h => by
  obtain ⟨g, hg⟩ := hf h
  rw [← hg]
  exact f.is_of_fin_order (tG g)
#align is_torsion.of_surjective IsTorsion.of_surjective
#align add_is_torsion.of_surjective AddIsTorsion.of_surjective

/- warning: is_torsion.extension_closed -> IsTorsion.extension_closed is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Group.{u1} G] {N : Subgroup.{u1} G _inst_1} [_inst_2 : Group.{u2} H] {f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))}, (Eq.{succ u1} (Subgroup.{u1} G _inst_1) N (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f)) -> (Monoid.IsTorsion.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) -> (Monoid.IsTorsion.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (Subgroup.toGroup.{u1} G _inst_1 N)))) -> (Monoid.IsTorsion.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Group.{u2} G] {N : Subgroup.{u2} G _inst_1} [_inst_2 : Group.{u1} H] {f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))}, (Eq.{succ u2} (Subgroup.{u2} G _inst_1) N (MonoidHom.ker.{u2, u1} G _inst_1 H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) f)) -> (Monoid.IsTorsion.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) -> (Monoid.IsTorsion.{u2} (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x N)) (Submonoid.toMonoid.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Subgroup.toSubmonoid.{u2} G _inst_1 N))) -> (Monoid.IsTorsion.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align is_torsion.extension_closed IsTorsion.extension_closedₓ'. -/
/-- Torsion groups are closed under extensions. -/
@[to_additive AddIsTorsion.extension_closed "Additive torsion groups are closed under extensions."]
theorem IsTorsion.extension_closed {f : G →* H} (hN : N = f.ker) (tH : IsTorsion H)
    (tN : IsTorsion N) : IsTorsion G := fun g =>
  (isOfFinOrder_iff_pow_eq_one _).mpr <|
    by
    obtain ⟨ngn, ngnpos, hngn⟩ := (isOfFinOrder_iff_pow_eq_one _).mp (tH <| f g)
    have hmem := f.mem_ker.mpr ((f.map_pow g ngn).trans hngn)
    lift g ^ ngn to N using hN.symm ▸ hmem with gn
    obtain ⟨nn, nnpos, hnn⟩ := (isOfFinOrder_iff_pow_eq_one _).mp (tN gn)
    exact
      ⟨ngn * nn, mul_pos ngnpos nnpos, by
        rw [pow_mul, ← h, ← Subgroup.coe_pow, hnn, Subgroup.coe_one]⟩
#align is_torsion.extension_closed IsTorsion.extension_closed
#align add_is_torsion.extension_closed AddIsTorsion.extension_closed

/- warning: is_torsion.quotient_iff -> IsTorsion.quotient_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {H : Type.{u2}} [_inst_1 : Group.{u1} G] {N : Subgroup.{u1} G _inst_1} [_inst_2 : Group.{u2} H] {f : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))}, (Function.Surjective.{succ u1, succ u2} G H (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) (fun (_x : MonoidHom.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) => G -> H) (MonoidHom.hasCoeToFun.{u1, u2} G H (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2)))) f)) -> (Eq.{succ u1} (Subgroup.{u1} G _inst_1) N (MonoidHom.ker.{u1, u2} G _inst_1 H (Monoid.toMulOneClass.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) f)) -> (Monoid.IsTorsion.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) N) (Subgroup.toGroup.{u1} G _inst_1 N)))) -> (Iff (Monoid.IsTorsion.{u2} H (DivInvMonoid.toMonoid.{u2} H (Group.toDivInvMonoid.{u2} H _inst_2))) (Monoid.IsTorsion.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u2}} {H : Type.{u1}} [_inst_1 : Group.{u2} G] {N : Subgroup.{u2} G _inst_1} [_inst_2 : Group.{u1} H] {f : MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))}, (Function.Surjective.{succ u2, succ u1} G H (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : G) => H) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G H (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)))) (MulOneClass.toMul.{u1} H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))) G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) (MonoidHom.monoidHomClass.{u2, u1} G H (Monoid.toMulOneClass.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))) (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2)))))) f)) -> (Eq.{succ u2} (Subgroup.{u2} G _inst_1) N (MonoidHom.ker.{u2, u1} G _inst_1 H (Monoid.toMulOneClass.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) f)) -> (Monoid.IsTorsion.{u2} (Subtype.{succ u2} G (fun (x : G) => Membership.mem.{u2, u2} G (Subgroup.{u2} G _inst_1) (SetLike.instMembership.{u2, u2} (Subgroup.{u2} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u2} G _inst_1)) x N)) (Submonoid.toMonoid.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1)) (Subgroup.toSubmonoid.{u2} G _inst_1 N))) -> (Iff (Monoid.IsTorsion.{u1} H (DivInvMonoid.toMonoid.{u1} H (Group.toDivInvMonoid.{u1} H _inst_2))) (Monoid.IsTorsion.{u2} G (DivInvMonoid.toMonoid.{u2} G (Group.toDivInvMonoid.{u2} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align is_torsion.quotient_iff IsTorsion.quotient_iffₓ'. -/
/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive AddIsTorsion.quotient_iff
      "The image of a quotient is additively torsion iff the group is torsion."]
theorem IsTorsion.quotient_iff {f : G →* H} (hf : Function.Surjective f) (hN : N = f.ker)
    (tN : IsTorsion N) : IsTorsion H ↔ IsTorsion G :=
  ⟨fun tH => IsTorsion.extension_closed hN tH tN, fun tG => IsTorsion.of_surjective hf tG⟩
#align is_torsion.quotient_iff IsTorsion.quotient_iff
#align add_is_torsion.quotient_iff AddIsTorsion.quotient_iff

#print ExponentExists.isTorsion /-
/-- If a group exponent exists, the group is torsion. -/
@[to_additive ExponentExists.is_add_torsion
      "If a group exponent exists, the group is additively torsion."]
theorem ExponentExists.isTorsion (h : ExponentExists G) : IsTorsion G := fun g =>
  by
  obtain ⟨n, npos, hn⟩ := h
  exact (isOfFinOrder_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩
#align exponent_exists.is_torsion ExponentExists.isTorsion
#align exponent_exists.is_add_torsion ExponentExists.is_add_torsion
-/

#print IsTorsion.exponentExists /-
/-- The group exponent exists for any bounded torsion group. -/
@[to_additive IsAddTorsion.exponentExists
      "The group exponent exists for any bounded additive torsion group."]
theorem IsTorsion.exponentExists (tG : IsTorsion G)
    (bounded : (Set.range fun g : G => orderOf g).Finite) : ExponentExists G :=
  exponentExists_iff_ne_zero.mpr <|
    (exponent_ne_zero_iff_range_orderOf_finite fun g => orderOf_pos' (tG g)).mpr bounded
#align is_torsion.exponent_exists IsTorsion.exponentExists
#align is_add_torsion.exponent_exists IsAddTorsion.exponentExists
-/

#print isTorsion_of_finite /-
/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_finite "Finite additive groups are additive torsion groups."]
theorem isTorsion_of_finite [Finite G] : IsTorsion G :=
  ExponentExists.isTorsion <| exponentExists_iff_ne_zero.mpr exponent_ne_zero_of_finite
#align is_torsion_of_finite isTorsion_of_finite
#align is_add_torsion_of_finite is_add_torsion_of_finite
-/

end Group

section Module

-- A (semi/)ring of scalars and a commutative monoid of elements
variable (R M : Type _) [AddCommMonoid M]

namespace AddMonoid

/- warning: add_monoid.is_torsion.module_of_torsion -> AddMonoid.IsTorsion.module_of_torsion is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : Semiring.{u1} R] [_inst_3 : Module.{u1, u2} R M _inst_2 _inst_1], (AddMonoid.IsTorsion.{u1} R (AddMonoidWithOne.toAddMonoid.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_2))))) -> (AddMonoid.IsTorsion.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1))
but is expected to have type
  forall (R : Type.{u2}) (M : Type.{u1}) [_inst_1 : AddCommMonoid.{u1} M] [_inst_2 : Semiring.{u2} R] [_inst_3 : Module.{u2, u1} R M _inst_2 _inst_1], (AddMonoid.IsTorsion.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u2} R (NonAssocSemiring.toAddCommMonoidWithOne.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))))) -> (AddMonoid.IsTorsion.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1))
Case conversion may be inaccurate. Consider using '#align add_monoid.is_torsion.module_of_torsion AddMonoid.IsTorsion.module_of_torsionₓ'. -/
/-- A module whose scalars are additively torsion is additively torsion. -/
theorem IsTorsion.module_of_torsion [Semiring R] [Module R M] (tR : IsTorsion R) : IsTorsion M :=
  fun f =>
  (isOfFinAddOrder_iff_nsmul_eq_zero _).mpr <|
    by
    obtain ⟨n, npos, hn⟩ := (isOfFinAddOrder_iff_nsmul_eq_zero _).mp (tR 1)
    exact ⟨n, npos, by simp only [nsmul_eq_smul_cast R _ f, ← nsmul_one, hn, zero_smul]⟩
#align add_monoid.is_torsion.module_of_torsion AddMonoid.IsTorsion.module_of_torsion

/- warning: add_monoid.is_torsion.module_of_finite -> AddMonoid.IsTorsion.module_of_finite is a dubious translation:
lean 3 declaration is
  forall (R : Type.{u1}) (M : Type.{u2}) [_inst_1 : AddCommMonoid.{u2} M] [_inst_2 : Ring.{u1} R] [_inst_3 : Finite.{succ u1} R] [_inst_4 : Module.{u1, u2} R M (Ring.toSemiring.{u1} R _inst_2) _inst_1], AddMonoid.IsTorsion.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)
but is expected to have type
  forall (R : Type.{u2}) (M : Type.{u1}) [_inst_1 : AddCommMonoid.{u1} M] [_inst_2 : Ring.{u2} R] [_inst_3 : Finite.{succ u2} R] [_inst_4 : Module.{u2, u1} R M (Ring.toSemiring.{u2} R _inst_2) _inst_1], AddMonoid.IsTorsion.{u1} M (AddCommMonoid.toAddMonoid.{u1} M _inst_1)
Case conversion may be inaccurate. Consider using '#align add_monoid.is_torsion.module_of_finite AddMonoid.IsTorsion.module_of_finiteₓ'. -/
/-- A module with a finite ring of scalars is additively torsion. -/
theorem IsTorsion.module_of_finite [Ring R] [Finite R] [Module R M] : IsTorsion M :=
  (is_add_torsion_of_finite : IsTorsion R).module_of_torsion _ _
#align add_monoid.is_torsion.module_of_finite AddMonoid.IsTorsion.module_of_finite

end AddMonoid

end Module

section CommMonoid

variable (G) [CommMonoid G]

namespace CommMonoid

#print CommMonoid.torsion /-
/-- The torsion submonoid of a commutative monoid.

(Note that by `monoid.is_torsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive add_torsion "The torsion submonoid of an additive commutative monoid."]
def torsion : Submonoid G where
  carrier := { x | IsOfFinOrder x }
  one_mem' := isOfFinOrder_one
  mul_mem' _ _ hx hy := hx.mul hy
#align comm_monoid.torsion CommMonoid.torsion
#align add_comm_monoid.add_torsion AddCommMonoid.addTorsion
-/

variable {G}

/- warning: comm_monoid.torsion.is_torsion -> CommMonoid.torsion.isTorsion is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], Monoid.IsTorsion.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) (CommMonoid.torsion.{u1} G _inst_1)) (Submonoid.toMonoid.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1) (CommMonoid.torsion.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], Monoid.IsTorsion.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.instSetLikeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) x (CommMonoid.torsion.{u1} G _inst_1))) (Submonoid.toMonoid.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1) (CommMonoid.torsion.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align comm_monoid.torsion.is_torsion CommMonoid.torsion.isTorsionₓ'. -/
/-- Torsion submonoids are torsion. -/
@[to_additive "Additive torsion submonoids are additively torsion."]
theorem torsion.isTorsion : IsTorsion <| torsion G := fun ⟨_, n, npos, hn⟩ =>
  ⟨n, npos,
    Subtype.ext <| by
      rw [mul_left_iterate, _root_.mul_one, [anonymous], Subtype.coe_mk, Submonoid.coe_one,
        (isPeriodicPt_mul_iff_pow_eq_one _).mp hn]⟩
#align comm_monoid.torsion.is_torsion CommMonoid.torsion.isTorsion
#align add_comm_monoid.add_torsion.is_torsion AddCommMonoid.addTorsion.isTorsion

variable (G) (p : ℕ) [hp : Fact p.Prime]

include hp

#print CommMonoid.primaryComponent /-
/-- The `p`-primary component is the submonoid of elements with order prime-power of `p`. -/
@[to_additive
      "The `p`-primary component is the submonoid of elements with additive order prime-power of `p`.",
  simps]
def primaryComponent : Submonoid G
    where
  carrier := { g | ∃ n : ℕ, orderOf g = p ^ n }
  one_mem' := ⟨0, by rw [pow_zero, orderOf_one]⟩
  mul_mem' g₁ g₂ hg₁ hg₂ :=
    exists_orderOf_eq_prime_pow_iff.mpr <|
      by
      obtain ⟨m, hm⟩ := exists_order_of_eq_prime_pow_iff.mp hg₁
      obtain ⟨n, hn⟩ := exists_order_of_eq_prime_pow_iff.mp hg₂
      exact
        ⟨m + n, by
          rw [mul_pow, pow_add, pow_mul, hm, one_pow, Monoid.one_mul, mul_comm, pow_mul, hn,
            one_pow]⟩
#align comm_monoid.primary_component CommMonoid.primaryComponent
#align add_comm_monoid.primary_component AddCommMonoid.primaryComponent
-/

variable {G} {p}

/- warning: comm_monoid.primary_component.exists_order_of_eq_prime_pow -> CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)] (g : coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp)), Exists.{1} Nat (fun (n : Nat) => Eq.{1} Nat (orderOf.{u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp)) (Submonoid.toMonoid.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp)) g) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat (Monoid.Pow.{0} Nat Nat.monoid)) p n))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)] (g : Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.instSetLikeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) x (CommMonoid.primaryComponent.{u1} G _inst_1 p hp))), Exists.{1} Nat (fun (n : Nat) => Eq.{1} Nat (orderOf.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.instSetLikeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) x (CommMonoid.primaryComponent.{u1} G _inst_1 p hp))) (Submonoid.toMonoid.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp)) g) (HPow.hPow.{0, 0, 0} Nat Nat Nat (instHPow.{0, 0} Nat Nat instPowNat) p n))
Case conversion may be inaccurate. Consider using '#align comm_monoid.primary_component.exists_order_of_eq_prime_pow CommMonoid.primaryComponent.exists_orderOf_eq_prime_powₓ'. -/
/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive "Elements of the `p`-primary component have additive order `p^n` for some `n`"]
theorem primaryComponent.exists_orderOf_eq_prime_pow (g : CommMonoid.primaryComponent G p) :
    ∃ n : ℕ, orderOf g = p ^ n := by simpa [primary_component] using g.property
#align comm_monoid.primary_component.exists_order_of_eq_prime_pow CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow
#align add_comm_monoid.primary_component.exists_order_of_eq_prime_nsmul AddCommMonoid.primaryComponent.exists_orderOf_eq_prime_nsmul

/- warning: comm_monoid.primary_component.disjoint -> CommMonoid.primaryComponent.disjoint is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)] {p' : Nat} [hp' : Fact (Nat.Prime p')], (Ne.{1} Nat p p') -> (Disjoint.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Preorder.toHasLe.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.partialOrder.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.completeLattice.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp) (CommMonoid.primaryComponent.{u1} G _inst_1 p' hp'))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)] {p' : Nat} [hp' : Fact (Nat.Prime p')], (Ne.{1} Nat p p') -> (Disjoint.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.instCompleteLatticeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))) (BoundedOrder.toOrderBot.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Preorder.toLE.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (PartialOrder.toPreorder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (OmegaCompletePartialOrder.toPartialOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (CompleteLattice.instOmegaCompletePartialOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.instCompleteLatticeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))))) (CompleteLattice.toBoundedOrder.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.instCompleteLatticeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))) (CommMonoid.primaryComponent.{u1} G _inst_1 p hp) (CommMonoid.primaryComponent.{u1} G _inst_1 p' hp'))
Case conversion may be inaccurate. Consider using '#align comm_monoid.primary_component.disjoint CommMonoid.primaryComponent.disjointₓ'. -/
/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive "The `p`- and `q`-primary components are disjoint for `p ≠ q`."]
theorem primaryComponent.disjoint {p' : ℕ} [hp' : Fact p'.Prime] (hne : p ≠ p') :
    Disjoint (CommMonoid.primaryComponent G p) (CommMonoid.primaryComponent G p') :=
  Submonoid.disjoint_def.mpr <| by
    rintro g ⟨_ | n, hn⟩ ⟨n', hn'⟩
    · rwa [pow_zero, orderOf_eq_one_iff] at hn
    ·
      exact
        absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos (hn.symm.trans hn')) hne
#align comm_monoid.primary_component.disjoint CommMonoid.primaryComponent.disjoint
#align add_comm_monoid.primary_component.disjoint AddCommMonoid.primaryComponent.disjoint

end CommMonoid

open CommMonoid (torsion)

namespace Monoid.IsTorsion

variable {G}

/- warning: monoid.is_torsion.torsion_eq_top -> Monoid.IsTorsion.torsion_eq_top is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], (Monoid.IsTorsion.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) -> (Eq.{succ u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (CommMonoid.torsion.{u1} G _inst_1) (Top.top.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.hasTop.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], (Monoid.IsTorsion.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) -> (Eq.{succ u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (CommMonoid.torsion.{u1} G _inst_1) (Top.top.{u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (Submonoid.instTopSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align monoid.is_torsion.torsion_eq_top Monoid.IsTorsion.torsion_eq_topₓ'. -/
/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[simp, to_additive "The additive torsion submonoid of an additive torsion monoid is `⊤`."]
theorem torsion_eq_top (tG : IsTorsion G) : torsion G = ⊤ := by ext <;> tauto
#align monoid.is_torsion.torsion_eq_top Monoid.IsTorsion.torsion_eq_top
#align add_monoid.is_torsion.torsion_eq_top AddMonoid.IsTorsion.torsion_eq_top

/- warning: monoid.is_torsion.torsion_mul_equiv -> Monoid.IsTorsion.torsionMulEquiv is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], (Monoid.IsTorsion.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) -> (MulEquiv.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.setLike.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) (CommMonoid.torsion.{u1} G _inst_1)) G (Submonoid.mul.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) (CommMonoid.torsion.{u1} G _inst_1)) (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommMonoid.{u1} G], (Monoid.IsTorsion.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) -> (MulEquiv.{u1, u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))) G (Submonoid.instSetLikeSubmonoid.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)))) x (CommMonoid.torsion.{u1} G _inst_1))) G (Submonoid.mul.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1)) (CommMonoid.torsion.{u1} G _inst_1)) (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (CommMonoid.toMonoid.{u1} G _inst_1))))
Case conversion may be inaccurate. Consider using '#align monoid.is_torsion.torsion_mul_equiv Monoid.IsTorsion.torsionMulEquivₓ'. -/
/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive "An additive torsion monoid is isomorphic to its torsion submonoid."]
def torsionMulEquiv (tG : IsTorsion G) : torsion G ≃* G :=
  (MulEquiv.submonoidCongr tG.torsion_eq_top).trans Submonoid.topEquiv
#align monoid.is_torsion.torsion_mul_equiv Monoid.IsTorsion.torsionMulEquiv
#align add_monoid.is_torsion.torsion_add_equiv AddMonoid.IsTorsion.torsionAddEquiv

/- warning: monoid.is_torsion.torsion_mul_equiv_apply -> Monoid.IsTorsion.torsionMulEquiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monoid.is_torsion.torsion_mul_equiv_apply Monoid.IsTorsion.torsionMulEquiv_applyₓ'. -/
@[to_additive]
theorem torsionMulEquiv_apply (tG : IsTorsion G) (a : torsion G) :
    tG.torsionMulEquiv a = MulEquiv.submonoidCongr tG.torsion_eq_top a :=
  rfl
#align monoid.is_torsion.torsion_mul_equiv_apply Monoid.IsTorsion.torsionMulEquiv_apply
#align add_monoid.is_torsion.torsion_add_equiv_apply AddMonoid.IsTorsion.torsionAddEquiv_apply

/- warning: monoid.is_torsion.torsion_mul_equiv_symm_apply_coe -> Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align monoid.is_torsion.torsion_mul_equiv_symm_apply_coe Monoid.IsTorsion.torsionMulEquiv_symm_apply_coeₓ'. -/
@[to_additive]
theorem torsionMulEquiv_symm_apply_coe (tG : IsTorsion G) (a : G) :
    tG.torsionMulEquiv.symm a = ⟨Submonoid.topEquiv.symm a, tG _⟩ :=
  rfl
#align monoid.is_torsion.torsion_mul_equiv_symm_apply_coe Monoid.IsTorsion.torsionMulEquiv_symm_apply_coe
#align add_monoid.is_torsion.torsion_add_equiv_symm_apply_coe AddMonoid.IsTorsion.torsionAddEquiv_symm_apply_coe

end Monoid.IsTorsion

/- warning: torsion.of_torsion -> Torsion.ofTorsion is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align torsion.of_torsion Torsion.ofTorsionₓ'. -/
/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[simp,
  to_additive AddCommMonoid.Torsion.ofTorsion
      "Additive torsion submonoids of an additive torsion submonoid are isomorphic to the submonoid."]
def Torsion.ofTorsion : torsion (torsion G) ≃* torsion G :=
  Monoid.IsTorsion.torsionMulEquiv CommMonoid.torsion.isTorsion
#align torsion.of_torsion Torsion.ofTorsion
#align add_comm_monoid.torsion.of_torsion AddCommMonoid.Torsion.ofTorsion

end CommMonoid

section CommGroup

variable (G) [CommGroup G]

namespace CommGroup

#print CommGroup.torsion /-
/-- The torsion subgroup of an abelian group. -/
@[to_additive "The torsion subgroup of an additive abelian group."]
def torsion : Subgroup G :=
  { CommMonoid.torsion G with inv_mem' := fun x => IsOfFinOrder.inv }
#align comm_group.torsion CommGroup.torsion
#align add_comm_group.torsion AddCommGroup.torsion
-/

#print CommGroup.torsion_eq_torsion_submonoid /-
/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
      "The additive torsion submonoid of an abelian group equals the torsion subgroup as a submonoid."]
theorem torsion_eq_torsion_submonoid : CommMonoid.torsion G = (torsion G).toSubmonoid :=
  rfl
#align comm_group.torsion_eq_torsion_submonoid CommGroup.torsion_eq_torsion_submonoid
#align add_comm_group.add_torsion_eq_add_torsion_submonoid AddCommGroup.add_torsion_eq_add_torsion_submonoid
-/

variable (p : ℕ) [hp : Fact p.Prime]

include hp

#print CommGroup.primaryComponent /-
/-- The `p`-primary component is the subgroup of elements with order prime-power of `p`. -/
@[to_additive
      "The `p`-primary component is the subgroup of elements with additive order prime-power of `p`.",
  simps]
def primaryComponent : Subgroup G :=
  { CommMonoid.primaryComponent G p with
    inv_mem' := fun g ⟨n, hn⟩ => ⟨n, (orderOf_inv g).trans hn⟩ }
#align comm_group.primary_component CommGroup.primaryComponent
#align add_comm_group.primary_component AddCommGroup.primaryComponent
-/

variable {G} {p}

/- warning: comm_group.primary_component.is_p_group -> CommGroup.primaryComponent.isPGroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)], IsPGroup.{u1} p (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1)) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1)) G (Subgroup.setLike.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) (CommGroup.primaryComponent.{u1} G _inst_1 p hp)) (Subgroup.toGroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1) (CommGroup.primaryComponent.{u1} G _inst_1 p hp))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : CommGroup.{u1} G] {p : Nat} [hp : Fact (Nat.Prime p)], IsPGroup.{u1} p (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1)) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1)) G (Subgroup.instSetLikeSubgroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1))) x (CommGroup.primaryComponent.{u1} G _inst_1 p hp))) (Subgroup.toGroup.{u1} G (CommGroup.toGroup.{u1} G _inst_1) (CommGroup.primaryComponent.{u1} G _inst_1 p hp))
Case conversion may be inaccurate. Consider using '#align comm_group.primary_component.is_p_group CommGroup.primaryComponent.isPGroupₓ'. -/
/-- The `p`-primary component is a `p` group. -/
theorem primaryComponent.isPGroup : IsPGroup p <| primaryComponent G p := fun g =>
  (propext exists_orderOf_eq_prime_pow_iff.symm).mpr
    (CommMonoid.primaryComponent.exists_orderOf_eq_prime_pow g)
#align comm_group.primary_component.is_p_group CommGroup.primaryComponent.isPGroup

end CommGroup

end CommGroup

namespace Monoid

variable (G) [Monoid G]

#print Monoid.IsTorsionFree /-
/-- A predicate on a monoid saying that only 1 is of finite order. -/
@[to_additive "A predicate on an additive monoid saying that only 0 is of finite order."]
def IsTorsionFree :=
  ∀ g : G, g ≠ 1 → ¬IsOfFinOrder g
#align monoid.is_torsion_free Monoid.IsTorsionFree
#align add_monoid.is_torsion_free AddMonoid.IsTorsionFree
-/

/- warning: monoid.not_is_torsion_free_iff -> Monoid.not_isTorsionFree_iff is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) [_inst_1 : Monoid.{u1} G], Iff (Not (Monoid.IsTorsionFree.{u1} G _inst_1)) (Exists.{succ u1} G (fun (g : G) => And (Ne.{succ u1} G g (OfNat.ofNat.{u1} G 1 (OfNat.mk.{u1} G 1 (One.one.{u1} G (MulOneClass.toHasOne.{u1} G (Monoid.toMulOneClass.{u1} G _inst_1)))))) (IsOfFinOrder.{u1} G _inst_1 g)))
but is expected to have type
  forall (G : Type.{u1}) [_inst_1 : Monoid.{u1} G], Iff (Not (Monoid.IsTorsionFree.{u1} G _inst_1)) (Exists.{succ u1} G (fun (g : G) => And (Ne.{succ u1} G g (OfNat.ofNat.{u1} G 1 (One.toOfNat1.{u1} G (Monoid.toOne.{u1} G _inst_1)))) (IsOfFinOrder.{u1} G _inst_1 g)))
Case conversion may be inaccurate. Consider using '#align monoid.not_is_torsion_free_iff Monoid.not_isTorsionFree_iffₓ'. -/
/-- A nontrivial monoid is not torsion-free if any nontrivial element has finite order. -/
@[simp,
  to_additive "An additive monoid is not torsion free if any nontrivial element has finite order."]
theorem not_isTorsionFree_iff : ¬IsTorsionFree G ↔ ∃ g : G, g ≠ 1 ∧ IsOfFinOrder g := by
  simp_rw [is_torsion_free, Ne.def, not_forall, Classical.not_not, exists_prop]
#align monoid.not_is_torsion_free_iff Monoid.not_isTorsionFree_iff
#align add_monoid.not_is_torsion_free_iff AddMonoid.not_isTorsionFree_iff

end Monoid

section Group

open Monoid

variable [Group G]

#print IsTorsion.not_torsion_free /-
/-- A nontrivial torsion group is not torsion-free. -/
@[to_additive AddMonoid.IsTorsion.not_torsion_free
      "A nontrivial additive torsion group is not torsion-free."]
theorem IsTorsion.not_torsion_free [hN : Nontrivial G] : IsTorsion G → ¬IsTorsionFree G := fun tG =>
  (not_isTorsionFree_iff _).mpr <|
    by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, hx, tG x⟩
#align is_torsion.not_torsion_free IsTorsion.not_torsion_free
#align add_monoid.is_torsion.not_torsion_free AddMonoid.IsTorsion.not_torsion_free
-/

#print IsTorsionFree.not_torsion /-
/-- A nontrivial torsion-free group is not torsion. -/
@[to_additive AddMonoid.IsTorsionFree.not_torsion
      "A nontrivial torsion-free additive group is not torsion."]
theorem IsTorsionFree.not_torsion [hN : Nontrivial G] : IsTorsionFree G → ¬IsTorsion G := fun tfG =>
  (not_isTorsion_iff _).mpr <|
    by
    obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN
    exact ⟨x, (tfG x) hx⟩
#align is_torsion_free.not_torsion IsTorsionFree.not_torsion
#align add_monoid.is_torsion_free.not_torsion AddMonoid.IsTorsionFree.not_torsion
-/

/- warning: is_torsion_free.subgroup -> IsTorsionFree.subgroup is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], (Monoid.IsTorsionFree.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) -> (forall (H : Subgroup.{u1} G _inst_1), Monoid.IsTorsionFree.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (DivInvMonoid.toMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Group.toDivInvMonoid.{u1} (coeSort.{succ u1, succ (succ u1)} (Subgroup.{u1} G _inst_1) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.setLike.{u1} G _inst_1)) H) (Subgroup.toGroup.{u1} G _inst_1 H))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], (Monoid.IsTorsionFree.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))) -> (forall (H : Subgroup.{u1} G _inst_1), Monoid.IsTorsionFree.{u1} (Subtype.{succ u1} G (fun (x : G) => Membership.mem.{u1, u1} G (Subgroup.{u1} G _inst_1) (SetLike.instMembership.{u1, u1} (Subgroup.{u1} G _inst_1) G (Subgroup.instSetLikeSubgroup.{u1} G _inst_1)) x H)) (Submonoid.toMonoid.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) (Subgroup.toSubmonoid.{u1} G _inst_1 H)))
Case conversion may be inaccurate. Consider using '#align is_torsion_free.subgroup IsTorsionFree.subgroupₓ'. -/
/-- Subgroups of torsion-free groups are torsion-free. -/
@[to_additive "Subgroups of additive torsion-free groups are additively torsion-free."]
theorem IsTorsionFree.subgroup (tG : IsTorsionFree G) (H : Subgroup G) : IsTorsionFree H :=
  fun h hne =>
  (isOfFinOrder_iff_coe H.toSubmonoid h).Not.mpr <|
    tG h <| by norm_cast <;> simp [hne, not_false_iff]
#align is_torsion_free.subgroup IsTorsionFree.subgroup
#align is_torsion_free.add_subgroup IsTorsionFree.addSubgroup

/- warning: is_torsion_free.prod -> IsTorsionFree.prod is a dubious translation:
lean 3 declaration is
  forall {η : Type.{u1}} {Gs : η -> Type.{u2}} [_inst_2 : forall (i : η), Group.{u2} (Gs i)], (forall (i : η), Monoid.IsTorsionFree.{u2} (Gs i) (DivInvMonoid.toMonoid.{u2} (Gs i) (Group.toDivInvMonoid.{u2} (Gs i) (_inst_2 i)))) -> (Monoid.IsTorsionFree.{max u1 u2} (forall (i : η), Gs i) (Pi.monoid.{u1, u2} η (fun (i : η) => Gs i) (fun (i : η) => DivInvMonoid.toMonoid.{u2} (Gs i) (Group.toDivInvMonoid.{u2} (Gs i) (_inst_2 i)))))
but is expected to have type
  forall {η : Type.{u2}} {Gs : η -> Type.{u1}} [_inst_2 : forall (i : η), Group.{u1} (Gs i)], (forall (i : η), Monoid.IsTorsionFree.{u1} (Gs i) (DivInvMonoid.toMonoid.{u1} (Gs i) (Group.toDivInvMonoid.{u1} (Gs i) (_inst_2 i)))) -> (Monoid.IsTorsionFree.{max u2 u1} (forall (i : η), Gs i) (Pi.monoid.{u2, u1} η (fun (i : η) => Gs i) (fun (i : η) => DivInvMonoid.toMonoid.{u1} (Gs i) (Group.toDivInvMonoid.{u1} (Gs i) (_inst_2 i)))))
Case conversion may be inaccurate. Consider using '#align is_torsion_free.prod IsTorsionFree.prodₓ'. -/
/-- Direct products of torsion free groups are torsion free. -/
@[to_additive AddMonoid.IsTorsionFree.prod
      "Direct products of additive torsion free groups are torsion free."]
theorem IsTorsionFree.prod {η : Type _} {Gs : η → Type _} [∀ i, Group (Gs i)]
    (tfGs : ∀ i, IsTorsionFree (Gs i)) : IsTorsionFree <| ∀ i, Gs i := fun w hne h =>
  hne <|
    funext fun i => Classical.not_not.mp <| mt (tfGs i (w i)) <| Classical.not_not.mpr <| h.apply i
#align is_torsion_free.prod IsTorsionFree.prod
#align add_monoid.is_torsion_free.prod AddMonoid.IsTorsionFree.prod

end Group

section CommGroup

open Monoid (IsTorsionFree)

open CommGroup (torsion)

variable (G) [CommGroup G]

#print IsTorsionFree.quotient_torsion /-
/-- Quotienting a group by its torsion subgroup yields a torsion free group. -/
@[to_additive AddIsTorsionFree.quotient_torsion
      "Quotienting a group by its additive torsion subgroup yields an additive torsion free group."]
theorem IsTorsionFree.quotient_torsion : IsTorsionFree <| G ⧸ torsion G := fun g hne hfin =>
  hne <| by
    induction g using QuotientGroup.induction_on'
    obtain ⟨m, mpos, hm⟩ := (isOfFinOrder_iff_pow_eq_one _).mp hfin
    obtain ⟨n, npos, hn⟩ := (isOfFinOrder_iff_pow_eq_one _).mp ((QuotientGroup.eq_one_iff _).mp hm)
    exact
      (QuotientGroup.eq_one_iff g).mpr
        ((isOfFinOrder_iff_pow_eq_one _).mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩)
#align is_torsion_free.quotient_torsion IsTorsionFree.quotient_torsion
#align add_is_torsion_free.quotient_torsion AddIsTorsionFree.quotient_torsion
-/

end CommGroup

