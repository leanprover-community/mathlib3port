/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang

! This file was ported from Lean 3 source module algebra.direct_sum.internal
! leanprover-community/mathlib commit 33c67ae661dd8988516ff7f247b0be3018cdd952
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Algebra.Operations
import Mathbin.Algebra.Algebra.Subalgebra.Basic
import Mathbin.Algebra.DirectSum.Algebra

/-!
# Internally graded rings and algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:

* `set_like.gnon_unital_non_assoc_semiring`
* `set_like.gsemiring`
* `set_like.gcomm_semiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `direct_sum.coe_ring_hom` (a `ring_hom` version of `direct_sum.coe_add_monoid_hom`)
* `direct_sum.coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.is_internal` for providing an explicit decomposition function.

When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/


open DirectSum BigOperators

variable {ι : Type _} {σ S R : Type _}

#print AddCommMonoid.ofSubmonoidOnSemiring /-
instance AddCommMonoid.ofSubmonoidOnSemiring [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) : ∀ i, AddCommMonoid (A i) := fun i => by infer_instance
#align add_comm_monoid.of_submonoid_on_semiring AddCommMonoid.ofSubmonoidOnSemiring
-/

/- warning: add_comm_group.of_subgroup_on_ring -> AddCommGroup.ofSubgroupOnRing is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : Ring.{u3} R] [_inst_2 : SetLike.{u2, u3} σ R] [_inst_3 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (AddCommGroupWithOne.toAddGroupWithOne.{u3} R (Ring.toAddCommGroupWithOne.{u3} R _inst_1)))) _inst_2] (A : ι -> σ) (i : ι), AddCommGroup.{u3} (coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_2) (A i))
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : Ring.{u3} R] [_inst_2 : SetLike.{u2, u3} σ R] [_inst_3 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R _inst_1))) _inst_2] (A : ι -> σ) (i : ι), AddCommGroup.{u3} (Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_2) x (A i)))
Case conversion may be inaccurate. Consider using '#align add_comm_group.of_subgroup_on_ring AddCommGroup.ofSubgroupOnRingₓ'. -/
instance AddCommGroup.ofSubgroupOnRing [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ) :
    ∀ i, AddCommGroup (A i) := fun i => by infer_instance
#align add_comm_group.of_subgroup_on_ring AddCommGroup.ofSubgroupOnRing

/- warning: set_like.algebra_map_mem_graded -> SetLike.algebraMap_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {S : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u1} ι] [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Semiring.{u3} R] [_inst_4 : Algebra.{u2, u3} S R _inst_2 _inst_3] (A : ι -> (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4))) [_inst_5 : SetLike.GradedOne.{u1, u3, u3} ι R (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4)) (Submodule.setLike.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4)) (AddMonoidWithOne.toOne.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3)))) _inst_1 A] (s : S), Membership.Mem.{u3, u3} R (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4)) (SetLike.hasMem.{u3, u3} (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4)) R (Submodule.setLike.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))) (Algebra.toModule.{u2, u3} S R _inst_2 _inst_3 _inst_4))) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (RingHom.{u2, u3} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} R _inst_3)) (fun (_x : RingHom.{u2, u3} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} R _inst_3)) => S -> R) (RingHom.hasCoeToFun.{u2, u3} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u3} R _inst_3)) (algebraMap.{u2, u3} S R _inst_2 _inst_3 _inst_4) s) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι _inst_1))))
but is expected to have type
  forall {ι : Type.{u3}} {S : Type.{u2}} {R : Type.{u1}} [_inst_1 : Zero.{u3} ι] [_inst_2 : CommSemiring.{u2} S] [_inst_3 : Semiring.{u1} R] [_inst_4 : Algebra.{u2, u1} S R _inst_2 _inst_3] (A : ι -> (Submodule.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4))) [_inst_5 : SetLike.GradedOne.{u3, u1, u1} ι R (Submodule.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4)) (Submodule.setLike.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4)) (Semiring.toOne.{u1} R _inst_3) _inst_1 A] (s : S), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : S) => R) s) (Submodule.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4)) (SetLike.instMembership.{u1, u1} (Submodule.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4)) R (Submodule.setLike.{u2, u1} S R (CommSemiring.toSemiring.{u2} S _inst_2) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (Algebra.toModule.{u2, u1} S R _inst_2 _inst_3 _inst_4))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (RingHom.{u2, u1} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3)) S (fun (_x : S) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : S) => R) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (RingHom.{u2, u1} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3)) S R (NonUnitalNonAssocSemiring.toMul.{u2} S (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)))) (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3))) (NonUnitalRingHomClass.toMulHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3)) S R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} S (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_3)) (RingHomClass.toNonUnitalRingHomClass.{max u2 u1, u2, u1} (RingHom.{u2, u1} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3)) S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3) (RingHom.instRingHomClassRingHom.{u2, u1} S R (Semiring.toNonAssocSemiring.{u2} S (CommSemiring.toSemiring.{u2} S _inst_2)) (Semiring.toNonAssocSemiring.{u1} R _inst_3))))) (algebraMap.{u2, u1} S R _inst_2 _inst_3 _inst_4) s) (A (OfNat.ofNat.{u3} ι 0 (Zero.toOfNat0.{u3} ι _inst_1)))
Case conversion may be inaccurate. Consider using '#align set_like.algebra_map_mem_graded SetLike.algebraMap_mem_gradedₓ'. -/
theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 :=
  by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _
#align set_like.algebra_map_mem_graded SetLike.algebraMap_mem_graded

/- warning: set_like.nat_cast_mem_graded -> SetLike.nat_cast_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u1} ι] [_inst_2 : AddMonoidWithOne.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R _inst_2)) _inst_3] (A : ι -> σ) [_inst_5 : SetLike.GradedOne.{u1, u3, u2} ι R σ _inst_3 (AddMonoidWithOne.toOne.{u3} R _inst_2) _inst_1 A] (n : Nat), Membership.Mem.{u3, u2} R σ (SetLike.hasMem.{u2, u3} σ R _inst_3) ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Nat R (HasLiftT.mk.{1, succ u3} Nat R (CoeTCₓ.coe.{1, succ u3} Nat R (Nat.castCoe.{u3} R (AddMonoidWithOne.toNatCast.{u3} R _inst_2)))) n) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι _inst_1))))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u1}} {R : Type.{u2}} [_inst_1 : Zero.{u3} ι] [_inst_2 : AddMonoidWithOne.{u2} R] [_inst_3 : SetLike.{u1, u2} σ R] [_inst_4 : AddSubmonoidClass.{u1, u2} σ R (AddMonoid.toAddZeroClass.{u2} R (AddMonoidWithOne.toAddMonoid.{u2} R _inst_2)) _inst_3] (A : ι -> σ) [_inst_5 : SetLike.GradedOne.{u3, u2, u1} ι R σ _inst_3 (AddMonoidWithOne.toOne.{u2} R _inst_2) _inst_1 A] (n : Nat), Membership.mem.{u2, u1} R σ (SetLike.instMembership.{u1, u2} σ R _inst_3) (Nat.cast.{u2} R (AddMonoidWithOne.toNatCast.{u2} R _inst_2) n) (A (OfNat.ofNat.{u3} ι 0 (Zero.toOfNat0.{u3} ι _inst_1)))
Case conversion may be inaccurate. Consider using '#align set_like.nat_cast_mem_graded SetLike.nat_cast_mem_gradedₓ'. -/
theorem SetLike.nat_cast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 :=
  by
  induction n
  · rw [Nat.cast_zero]
    exact zero_mem (A 0)
  · rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)
#align set_like.nat_cast_mem_graded SetLike.nat_cast_mem_graded

/- warning: set_like.int_cast_mem_graded -> SetLike.int_cast_mem_graded is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u1} ι] [_inst_2 : AddGroupWithOne.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R _inst_2)) _inst_3] (A : ι -> σ) [_inst_5 : SetLike.GradedOne.{u1, u3, u2} ι R σ _inst_3 (AddMonoidWithOne.toOne.{u3} R (AddGroupWithOne.toAddMonoidWithOne.{u3} R _inst_2)) _inst_1 A] (z : Int), Membership.Mem.{u3, u2} R σ (SetLike.hasMem.{u2, u3} σ R _inst_3) ((fun (a : Type) (b : Type.{u3}) [self : HasLiftT.{1, succ u3} a b] => self.0) Int R (HasLiftT.mk.{1, succ u3} Int R (CoeTCₓ.coe.{1, succ u3} Int R (Int.castCoe.{u3} R (AddGroupWithOne.toHasIntCast.{u3} R _inst_2)))) z) (A (OfNat.ofNat.{u1} ι 0 (OfNat.mk.{u1} ι 0 (Zero.zero.{u1} ι _inst_1))))
but is expected to have type
  forall {ι : Type.{u3}} {σ : Type.{u1}} {R : Type.{u2}} [_inst_1 : Zero.{u3} ι] [_inst_2 : AddGroupWithOne.{u2} R] [_inst_3 : SetLike.{u1, u2} σ R] [_inst_4 : AddSubgroupClass.{u1, u2} σ R (AddGroup.toSubNegMonoid.{u2} R (AddGroupWithOne.toAddGroup.{u2} R _inst_2)) _inst_3] (A : ι -> σ) [_inst_5 : SetLike.GradedOne.{u3, u2, u1} ι R σ _inst_3 (AddMonoidWithOne.toOne.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R _inst_2)) _inst_1 A] (z : Int), Membership.mem.{u2, u1} R σ (SetLike.instMembership.{u1, u2} σ R _inst_3) (Int.cast.{u2} R (AddGroupWithOne.toIntCast.{u2} R _inst_2) z) (A (OfNat.ofNat.{u3} ι 0 (Zero.toOfNat0.{u3} ι _inst_1)))
Case conversion may be inaccurate. Consider using '#align set_like.int_cast_mem_graded SetLike.int_cast_mem_gradedₓ'. -/
theorem SetLike.int_cast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 :=
  by
  induction z
  · rw [Int.cast_ofNat]
    exact SetLike.nat_cast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.nat_cast_mem_graded _ _)
#align set_like.int_cast_mem_graded SetLike.int_cast_mem_graded

section DirectSum

variable [DecidableEq ι]

/-! #### From `add_submonoid`s and `add_subgroup`s -/


namespace SetLike

/- warning: set_like.gnon_unital_non_assoc_semiring -> SetLike.gnonUnitalNonAssocSemiring is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : Add.{u1} ι] [_inst_3 : NonUnitalNonAssocSemiring.{u3} R] [_inst_4 : SetLike.{u2, u3} σ R] [_inst_5 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R _inst_3))) _inst_4] (A : ι -> σ) [_inst_6 : SetLike.GradedMul.{u1, u3, u2} ι R σ _inst_4 (Distrib.toHasMul.{u3} R (NonUnitalNonAssocSemiring.toDistrib.{u3} R _inst_3)) _inst_2 A], DirectSum.GNonUnitalNonAssocSemiring.{u1, u3} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_4) (A i)) _inst_2 (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R _inst_3) σ _inst_4 _inst_5 (A i))
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : Add.{u1} ι] [_inst_2 : NonUnitalNonAssocSemiring.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R _inst_2))) _inst_3] (_inst_5 : ι -> σ) [A : SetLike.GradedMul.{u1, u3, u2} ι R σ _inst_3 (NonUnitalNonAssocSemiring.toMul.{u3} R _inst_2) _inst_1 _inst_5], DirectSum.GNonUnitalNonAssocSemiring.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_3) x (_inst_5 i))) _inst_1 (fun (i : ι) => AddSubmonoidClass.toAddCommMonoid.{u3, u2} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R _inst_2) σ _inst_3 _inst_4 (_inst_5 i))
Case conversion may be inaccurate. Consider using '#align set_like.gnon_unital_non_assoc_semiring SetLike.gnonUnitalNonAssocSemiringₓ'. -/
/-- Build a `gnon_unital_non_assoc_semiring` instance for a collection of additive submonoids. -/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedMul A] :
    DirectSum.GNonUnitalNonAssocSemiring fun i => A i :=
  {
    SetLike.gMul
      A with
    mul_zero := fun i j _ => Subtype.ext (MulZeroClass.mul_zero _)
    zero_mul := fun i j _ => Subtype.ext (MulZeroClass.zero_mul _)
    mul_add := fun i j _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun i j _ _ _ => Subtype.ext (add_mul _ _ _) }
#align set_like.gnon_unital_non_assoc_semiring SetLike.gnonUnitalNonAssocSemiring

/- warning: set_like.gsemiring -> SetLike.gsemiring is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u1} ι] [_inst_3 : Semiring.{u3} R] [_inst_4 : SetLike.{u2, u3} σ R] [_inst_5 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_3))))) _inst_4] (A : ι -> σ) [_inst_6 : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_4 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_3)) _inst_2 A], DirectSum.GSemiring.{u1, u3} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_4) (A i)) _inst_2 (fun (i : ι) => AddCommMonoid.ofSubmonoidOnSemiring.{u1, u2, u3} ι σ R _inst_3 _inst_4 _inst_5 A i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : Semiring.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))))) _inst_3] (_inst_5 : ι -> σ) [A : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_3 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R _inst_2)) _inst_1 _inst_5], DirectSum.GSemiring.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_3) x (_inst_5 i))) _inst_1 (fun (i : ι) => AddCommMonoid.ofSubmonoidOnSemiring.{u1, u2, u3} ι σ R _inst_2 _inst_3 _inst_4 _inst_5 i)
Case conversion may be inaccurate. Consider using '#align set_like.gsemiring SetLike.gsemiringₓ'. -/
/-- Build a `gsemiring` instance for a collection of additive submonoids. -/
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i :=
  {
    SetLike.gMonoid
      A with
    mul_zero := fun i j _ => Subtype.ext (MulZeroClass.mul_zero _)
    zero_mul := fun i j _ => Subtype.ext (MulZeroClass.zero_mul _)
    mul_add := fun i j _ _ _ => Subtype.ext (mul_add _ _ _)
    add_mul := fun i j _ _ _ => Subtype.ext (add_mul _ _ _)
    natCast := fun n => ⟨n, SetLike.nat_cast_mem_graded _ _⟩
    natCast_zero := Subtype.ext Nat.cast_zero
    natCast_succ := fun n => Subtype.ext (Nat.cast_succ n) }
#align set_like.gsemiring SetLike.gsemiring

/- warning: set_like.gcomm_semiring -> SetLike.gcommSemiring is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u1} ι] [_inst_3 : CommSemiring.{u3} R] [_inst_4 : SetLike.{u2, u3} σ R] [_inst_5 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3)))))) _inst_4] (A : ι -> σ) [_inst_6 : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_4 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R _inst_3))) (AddCommMonoid.toAddMonoid.{u1} ι _inst_2) A], DirectSum.GCommSemiring.{u1, u3} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_4) (A i)) _inst_2 (fun (i : ι) => AddCommMonoid.ofSubmonoidOnSemiring.{u1, u2, u3} ι σ R (CommSemiring.toSemiring.{u3} R _inst_3) _inst_4 _inst_5 A i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : CommSemiring.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubmonoidClass.{u2, u3} σ R (AddMonoid.toAddZeroClass.{u3} R (AddMonoidWithOne.toAddMonoid.{u3} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u3} R (NonAssocSemiring.toAddCommMonoidWithOne.{u3} R (Semiring.toNonAssocSemiring.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2)))))) _inst_3] (_inst_5 : ι -> σ) [A : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_3 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R _inst_2))) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) _inst_5], DirectSum.GCommSemiring.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_3) x (_inst_5 i))) _inst_1 (fun (i : ι) => AddCommMonoid.ofSubmonoidOnSemiring.{u1, u2, u3} ι σ R (CommSemiring.toSemiring.{u3} R _inst_2) _inst_3 _inst_4 _inst_5 i)
Case conversion may be inaccurate. Consider using '#align set_like.gcomm_semiring SetLike.gcommSemiringₓ'. -/
/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gsemiring A with }
#align set_like.gcomm_semiring SetLike.gcommSemiring

/- warning: set_like.gring -> SetLike.gring is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddMonoid.{u1} ι] [_inst_3 : Ring.{u3} R] [_inst_4 : SetLike.{u2, u3} σ R] [_inst_5 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (AddCommGroupWithOne.toAddGroupWithOne.{u3} R (Ring.toAddCommGroupWithOne.{u3} R _inst_3)))) _inst_4] (A : ι -> σ) [_inst_6 : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_4 (Ring.toMonoid.{u3} R _inst_3) _inst_2 A], DirectSum.GRing.{u1, u3} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_4) (A i)) _inst_2 (fun (i : ι) => AddCommGroup.ofSubgroupOnRing.{u1, u2, u3} ι σ R _inst_3 _inst_4 _inst_5 A i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : AddMonoid.{u1} ι] [_inst_2 : Ring.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R _inst_2))) _inst_3] (_inst_5 : ι -> σ) [A : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_3 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (Ring.toSemiring.{u3} R _inst_2))) _inst_1 _inst_5], DirectSum.GRing.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_3) x (_inst_5 i))) _inst_1 (fun (i : ι) => AddCommGroup.ofSubgroupOnRing.{u1, u2, u3} ι σ R _inst_2 _inst_3 _inst_4 _inst_5 i)
Case conversion may be inaccurate. Consider using '#align set_like.gring SetLike.gringₓ'. -/
/-- Build a `gring` instance for a collection of additive subgroups. -/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i :=
  {
    SetLike.gsemiring
      A with
    intCast := fun z => ⟨z, SetLike.int_cast_mem_graded _ _⟩
    intCast_ofNat := fun n => Subtype.ext <| Int.cast_ofNat _
    intCast_negSucc := fun n => Subtype.ext <| Int.cast_negSucc n }
#align set_like.gring SetLike.gring

/- warning: set_like.gcomm_ring -> SetLike.gcommRing is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} ι] [_inst_2 : AddCommMonoid.{u1} ι] [_inst_3 : CommRing.{u3} R] [_inst_4 : SetLike.{u2, u3} σ R] [_inst_5 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (AddCommGroupWithOne.toAddGroupWithOne.{u3} R (Ring.toAddCommGroupWithOne.{u3} R (CommRing.toRing.{u3} R _inst_3))))) _inst_4] (A : ι -> σ) [_inst_6 : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_4 (Ring.toMonoid.{u3} R (CommRing.toRing.{u3} R _inst_3)) (AddCommMonoid.toAddMonoid.{u1} ι _inst_2) A], DirectSum.GCommRing.{u1, u3} ι (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => coeSort.{succ u2, succ (succ u3)} σ Type.{u3} (SetLike.hasCoeToSort.{u2, u3} σ R _inst_4) (A i)) _inst_2 (fun (i : ι) => AddCommGroup.ofSubgroupOnRing.{u1, u2, u3} ι σ R (CommRing.toRing.{u3} R _inst_3) _inst_4 _inst_5 A i)
but is expected to have type
  forall {ι : Type.{u1}} {σ : Type.{u2}} {R : Type.{u3}} [_inst_1 : AddCommMonoid.{u1} ι] [_inst_2 : CommRing.{u3} R] [_inst_3 : SetLike.{u2, u3} σ R] [_inst_4 : AddSubgroupClass.{u2, u3} σ R (AddGroup.toSubNegMonoid.{u3} R (AddGroupWithOne.toAddGroup.{u3} R (Ring.toAddGroupWithOne.{u3} R (CommRing.toRing.{u3} R _inst_2)))) _inst_3] (_inst_5 : ι -> σ) [A : SetLike.GradedMonoid.{u1, u3, u2} ι R σ _inst_3 (MonoidWithZero.toMonoid.{u3} R (Semiring.toMonoidWithZero.{u3} R (CommSemiring.toSemiring.{u3} R (CommRing.toCommSemiring.{u3} R _inst_2)))) (AddCommMonoid.toAddMonoid.{u1} ι _inst_1) _inst_5], DirectSum.GCommRing.{u1, u3} ι (fun (i : ι) => Subtype.{succ u3} R (fun (x : R) => Membership.mem.{u3, u2} R σ (SetLike.instMembership.{u2, u3} σ R _inst_3) x (_inst_5 i))) _inst_1 (fun (i : ι) => AddCommGroup.ofSubgroupOnRing.{u1, u2, u3} ι σ R (CommRing.toRing.{u3} R _inst_2) _inst_3 _inst_4 _inst_5 i)
Case conversion may be inaccurate. Consider using '#align set_like.gcomm_ring SetLike.gcommRingₓ'. -/
/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GCommRing fun i => A i :=
  { SetLike.gCommMonoid A, SetLike.gring A with }
#align set_like.gcomm_ring SetLike.gcommRing

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

#print DirectSum.coeRingHom /-
/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.Subtype (A i)) rfl fun _ _ _ _ => rfl
#align direct_sum.coe_ring_hom DirectSum.coeRingHom
-/

/- warning: direct_sum.coe_ring_hom_of -> DirectSum.coeRingHom_of is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_ring_hom_of DirectSum.coeRingHom_ofₓ'. -/
/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp]
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _
#align direct_sum.coe_ring_hom_of DirectSum.coeRingHom_of

/- warning: direct_sum.coe_mul_apply -> DirectSum.coe_mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_apply DirectSum.coe_mul_applyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij in (r.support ×ˢ r'.support).filterₓ fun ij : ι × ι => ij.1 + ij.2 = n,
        r ij.1 * r' ij.2 :=
  by
  rw [mul_eq_sum_support_ghas_mul, Dfinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  simp_rw [coe_of_apply, ← Finset.sum_filter, SetLike.coe_gMul]
#align direct_sum.coe_mul_apply DirectSum.coe_mul_apply

/- warning: direct_sum.coe_mul_apply_eq_dfinsupp_sum -> DirectSum.coe_mul_apply_eq_dfinsupp_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_apply_eq_dfinsupp_sum DirectSum.coe_mul_apply_eq_dfinsupp_sumₓ'. -/
theorem coe_mul_apply_eq_dfinsupp_sum [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) = r.Sum fun i ri => r'.Sum fun j rj => if i + j = n then ri * rj else 0 :=
  by
  simp only [mul_eq_dfinsupp_sum, Dfinsupp.sum_apply]
  iterate 2 rw [Dfinsupp.sum, AddSubmonoidClass.coe_finset_sum]; congr ; ext
  dsimp only; split_ifs
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ _ h]
    rfl
#align direct_sum.coe_mul_apply_eq_dfinsupp_sum DirectSum.coe_mul_apply_eq_dfinsupp_sum

/- warning: direct_sum.coe_of_mul_apply_aux -> DirectSum.coe_of_mul_apply_aux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_of_mul_apply_aux DirectSum.coe_of_mul_apply_auxₓ'. -/
theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : ∀ x : ι, i + x = n ↔ x = j) :
    ((of _ i r * r') n : R) = r * r' j := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.zero_mul, if_t_t]
      exact Dfinsupp.sum_zero
    simp_rw [Dfinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs
    rfl
    rw [dfinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, MulZeroClass.mul_zero]
#align direct_sum.coe_of_mul_apply_aux DirectSum.coe_of_mul_apply_aux

/- warning: direct_sum.coe_mul_of_apply_aux -> DirectSum.coe_mul_of_apply_aux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_of_apply_aux DirectSum.coe_mul_of_apply_auxₓ'. -/
theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
    (r' : A i) {j n : ι} (H : ∀ x : ι, x + i = n ↔ x = j) : ((r * of _ i r') n : R) = r j * r' := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, Dfinsupp.sum_comm]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.mul_zero, if_t_t]
      exact Dfinsupp.sum_zero
    simp_rw [Dfinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs
    rfl
    rw [dfinsupp.not_mem_support_iff.mp h, ZeroMemClass.coe_zero, MulZeroClass.zero_mul]
#align direct_sum.coe_mul_of_apply_aux DirectSum.coe_mul_of_apply_aux

/- warning: direct_sum.coe_of_mul_apply_add -> DirectSum.coe_of_mul_apply_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_of_mul_apply_add DirectSum.coe_of_mul_apply_addₓ'. -/
theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of _ i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_of_mul_apply_add DirectSum.coe_of_mul_apply_add

/- warning: direct_sum.coe_mul_of_apply_add -> DirectSum.coe_mul_of_apply_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_of_apply_add DirectSum.coe_mul_of_apply_addₓ'. -/
theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of _ i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩
#align direct_sum.coe_mul_of_apply_add DirectSum.coe_mul_of_apply_add

end coe

section CanonicallyOrderedAddMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

variable [CanonicallyOrderedAddMonoid ι] [SetLike.GradedMonoid A]

/- warning: direct_sum.coe_of_mul_apply_of_not_le -> DirectSum.coe_of_mul_apply_of_not_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_of_mul_apply_of_not_le DirectSum.coe_of_mul_apply_of_not_leₓ'. -/
theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i ≤ n) :
    ((of _ i r * r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.zero_mul, if_t_t]
      exact Dfinsupp.sum_zero
    · rw [Dfinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact h ((self_le_add_right i x).trans_eq H)
#align direct_sum.coe_of_mul_apply_of_not_le DirectSum.coe_of_mul_apply_of_not_le

/- warning: direct_sum.coe_mul_of_apply_of_not_le -> DirectSum.coe_mul_of_apply_of_not_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_of_apply_of_not_le DirectSum.coe_mul_of_apply_of_not_leₓ'. -/
theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i ≤ n) :
    ((r * of _ i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsupp_sum, Dfinsupp.sum_comm]
    apply (Dfinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, MulZeroClass.mul_zero, if_t_t]
      exact Dfinsupp.sum_zero
    · rw [Dfinsupp.sum, Finset.sum_ite_of_false _ _ fun x _ H => _, Finset.sum_const_zero]
      exact h ((self_le_add_left i x).trans_eq H)
#align direct_sum.coe_mul_of_apply_of_not_le DirectSum.coe_mul_of_apply_of_not_le

variable [Sub ι] [OrderedSub ι] [ContravariantClass ι ι (· + ·) (· ≤ ·)]

/- warning: direct_sum.coe_mul_of_apply_of_le -> DirectSum.coe_mul_of_apply_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_of_apply_of_le DirectSum.coe_mul_of_apply_of_leₓ'. -/
/- The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
  state them for `canonically_ordered_add_monoid` + the above three typeclasses for convenience. -/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of _ i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun x => (eq_tsub_iff_add_eq_of_le h).symm
#align direct_sum.coe_mul_of_apply_of_le DirectSum.coe_mul_of_apply_of_le

/- warning: direct_sum.coe_of_mul_apply_of_le -> DirectSum.coe_of_mul_apply_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_of_mul_apply_of_le DirectSum.coe_of_mul_apply_of_leₓ'. -/
theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of _ i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]
#align direct_sum.coe_of_mul_apply_of_le DirectSum.coe_of_mul_apply_of_le

/- warning: direct_sum.coe_mul_of_apply -> DirectSum.coe_mul_of_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_mul_of_apply DirectSum.coe_mul_of_applyₓ'. -/
theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of _ i r') n : R) = if i ≤ n then r (n - i) * r' else 0 :=
  by
  split_ifs
  exacts[coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_mul_of_apply DirectSum.coe_mul_of_apply

/- warning: direct_sum.coe_of_mul_apply -> DirectSum.coe_of_mul_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_of_mul_apply DirectSum.coe_of_mul_applyₓ'. -/
theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of _ i r * r') n : R) = if i ≤ n then r * r' (n - i) else 0 :=
  by
  split_ifs
  exacts[coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]
#align direct_sum.coe_of_mul_apply DirectSum.coe_of_mul_apply

end CanonicallyOrderedAddMonoid

end DirectSum

/-! #### From `submodule`s -/


namespace Submodule

#print Submodule.galgebra /-
/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i
    where
  toFun :=
    ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
  map_one := Subtype.ext <| (algebraMap S R).map_one
  map_mul x y := Sigma.subtype_ext (add_zero 0).symm <| (algebraMap S R).map_mul _ _
  commutes := fun r ⟨i, xi⟩ =>
    Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) <| Algebra.commutes _ _
  smul_def := fun r ⟨i, xi⟩ => Sigma.subtype_ext (zero_add i).symm <| Algebra.smul_def _ _
#align submodule.galgebra Submodule.galgebra
-/

/- warning: submodule.set_like.coe_galgebra_to_fun -> Submodule.setLike.coe_galgebra_toFun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.set_like.coe_galgebra_to_fun Submodule.setLike.coe_galgebra_toFunₓ'. -/
@[simp]
theorem setLike.coe_galgebra_toFun [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    ↑(@DirectSum.GAlgebra.toFun _ S (fun i => A i) _ _ _ _ _ _ _ s) = (algebraMap S R s : R) :=
  rfl
#align submodule.set_like.coe_galgebra_to_fun Submodule.setLike.coe_galgebra_toFun

#print Submodule.nat_power_gradedMonoid /-
/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i
    where
  one_mem := by
    rw [← one_le, pow_zero]
    exact le_rfl
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq
#align submodule.nat_power_graded_monoid Submodule.nat_power_gradedMonoid
-/

end Submodule

#print DirectSum.coeAlgHom /-
/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).Subtype) rfl (fun _ _ _ _ => rfl) fun _ => rfl
#align direct_sum.coe_alg_hom DirectSum.coeAlgHom
-/

/- warning: submodule.supr_eq_to_submodule_range -> Submodule.iSup_eq_toSubmodule_range is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.supr_eq_to_submodule_range Submodule.iSup_eq_toSubmodule_rangeₓ'. -/
/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`direct_sum.coe_alg_hom`. -/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    (⨆ i, A i) = (DirectSum.coeAlgHom A).range.toSubmodule :=
  (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl
#align submodule.supr_eq_to_submodule_range Submodule.iSup_eq_toSubmodule_range

/- warning: direct_sum.coe_alg_hom_of -> DirectSum.coeAlgHom_of is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.coe_alg_hom_of DirectSum.coeAlgHom_ofₓ'. -/
@[simp]
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ rfl (fun _ _ _ _ => rfl) _ _
#align direct_sum.coe_alg_hom_of DirectSum.coeAlgHom_of

end DirectSum

section HomogeneousElement

/- warning: set_like.is_homogeneous_zero_submodule -> SetLike.homogeneous_zero_submodule is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {S : Type.{u2}} {R : Type.{u3}} [_inst_1 : Zero.{u1} ι] [_inst_2 : Semiring.{u2} S] [_inst_3 : AddCommMonoid.{u3} R] [_inst_4 : Module.{u2, u3} S R _inst_2 _inst_3] (A : ι -> (Submodule.{u2, u3} S R _inst_2 _inst_3 _inst_4)), SetLike.Homogeneous.{u1, u3, u3} ι R (Submodule.{u2, u3} S R _inst_2 _inst_3 _inst_4) (Submodule.setLike.{u2, u3} S R _inst_2 _inst_3 _inst_4) A (OfNat.ofNat.{u3} R 0 (OfNat.mk.{u3} R 0 (Zero.zero.{u3} R (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R _inst_3))))))
but is expected to have type
  forall {ι : Type.{u3}} {S : Type.{u2}} {R : Type.{u1}} [_inst_1 : Zero.{u3} ι] [_inst_2 : Semiring.{u2} S] [_inst_3 : AddCommMonoid.{u1} R] [_inst_4 : Module.{u2, u1} S R _inst_2 _inst_3] (A : ι -> (Submodule.{u2, u1} S R _inst_2 _inst_3 _inst_4)), SetLike.Homogeneous.{u3, u1, u1} ι R (Submodule.{u2, u1} S R _inst_2 _inst_3 _inst_4) (Submodule.setLike.{u2, u1} S R _inst_2 _inst_3 _inst_4) A (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (AddMonoid.toZero.{u1} R (AddCommMonoid.toAddMonoid.{u1} R _inst_3))))
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous_zero_submodule SetLike.homogeneous_zero_submoduleₓ'. -/
theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι → Submodule S R) : SetLike.Homogeneous A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩
#align set_like.is_homogeneous_zero_submodule SetLike.homogeneous_zero_submodule

/- warning: set_like.is_homogeneous.smul -> SetLike.Homogeneous.smul is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {S : Type.{u2}} {R : Type.{u3}} [_inst_1 : CommSemiring.{u2} S] [_inst_2 : Semiring.{u3} R] [_inst_3 : Algebra.{u2, u3} S R _inst_1 _inst_2] {A : ι -> (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3))} {s : S} {r : R}, (SetLike.Homogeneous.{u1, u3, u3} ι R (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3)) (Submodule.setLike.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3)) A r) -> (SetLike.Homogeneous.{u1, u3, u3} ι R (Submodule.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3)) (Submodule.setLike.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3)) A (SMul.smul.{u2, u3} S R (SMulZeroClass.toHasSmul.{u2, u3} S R (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u2, u3} S R (MulZeroClass.toHasZero.{u2} S (MulZeroOneClass.toMulZeroClass.{u2} S (MonoidWithZero.toMulZeroOneClass.{u2} S (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_1))))) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u3} S R (Semiring.toMonoidWithZero.{u2} S (CommSemiring.toSemiring.{u2} S _inst_1)) (AddZeroClass.toHasZero.{u3} R (AddMonoid.toAddZeroClass.{u3} R (AddCommMonoid.toAddMonoid.{u3} R (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2)))))) (Module.toMulActionWithZero.{u2, u3} S R (CommSemiring.toSemiring.{u2} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} R (Semiring.toNonAssocSemiring.{u3} R _inst_2))) (Algebra.toModule.{u2, u3} S R _inst_1 _inst_2 _inst_3))))) s r))
but is expected to have type
  forall {ι : Type.{u1}} {S : Type.{u3}} {R : Type.{u2}} [_inst_1 : CommSemiring.{u3} S] [_inst_2 : Semiring.{u2} R] [_inst_3 : Algebra.{u3, u2} S R _inst_1 _inst_2] {A : ι -> (Submodule.{u3, u2} S R (CommSemiring.toSemiring.{u3} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Algebra.toModule.{u3, u2} S R _inst_1 _inst_2 _inst_3))} {s : S} {r : R}, (SetLike.Homogeneous.{u1, u2, u2} ι R (Submodule.{u3, u2} S R (CommSemiring.toSemiring.{u3} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Algebra.toModule.{u3, u2} S R _inst_1 _inst_2 _inst_3)) (Submodule.setLike.{u3, u2} S R (CommSemiring.toSemiring.{u3} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Algebra.toModule.{u3, u2} S R _inst_1 _inst_2 _inst_3)) A r) -> (SetLike.Homogeneous.{u1, u2, u2} ι R (Submodule.{u3, u2} S R (CommSemiring.toSemiring.{u3} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Algebra.toModule.{u3, u2} S R _inst_1 _inst_2 _inst_3)) (Submodule.setLike.{u3, u2} S R (CommSemiring.toSemiring.{u3} S _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} R (Semiring.toNonAssocSemiring.{u2} R _inst_2))) (Algebra.toModule.{u3, u2} S R _inst_1 _inst_2 _inst_3)) A (HSMul.hSMul.{u3, u2, u2} S R R (instHSMul.{u3, u2} S R (Algebra.toSMul.{u3, u2} S R _inst_1 _inst_2 _inst_3)) s r))
Case conversion may be inaccurate. Consider using '#align set_like.is_homogeneous.smul SetLike.Homogeneous.smulₓ'. -/
theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
    {s : S} {r : R} (hr : SetLike.Homogeneous A r) : SetLike.Homogeneous A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩
#align set_like.is_homogeneous.smul SetLike.Homogeneous.smul

end HomogeneousElement

