/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.monoid_algebra.ideal
! leanprover-community/mathlib commit 4f81bc21e32048db7344b7867946e992cf5f68cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.MonoidAlgebra.Division
import Mathbin.RingTheory.Ideal.Basic

/-!
# Lemmas about ideals of `monoid_algebra` and `add_monoid_algebra`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {k A G : Type _}

/- warning: monoid_algebra.mem_ideal_span_of_image -> MonoidAlgebra.mem_ideal_span_of_image is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} {G : Type.{u2}} [_inst_1 : Monoid.{u2} G] [_inst_2 : Semiring.{u1} k] {s : Set.{u2} G} {x : MonoidAlgebra.{u1, u2} k G _inst_2}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (Ideal.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)) (SetLike.hasMem.{max u1 u2, max u1 u2} (Ideal.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)) (MonoidAlgebra.{u1, u2} k G _inst_2) (Submodule.setLike.{max u1 u2, max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (Semiring.toNonAssocSemiring.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)))) (Semiring.toModule.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)))) x (Ideal.span.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1) (Set.image.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (coeFn.{max (succ (max u1 u2)) (succ u2), max (succ u2) (succ (max u1 u2))} (MonoidHom.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) (fun (_x : MonoidHom.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) => G -> (MonoidAlgebra.{u1, u2} k G _inst_2)) (MonoidHom.hasCoeToFun.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) (MonoidAlgebra.of.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))) s))) (forall (m : G), (Membership.Mem.{u2, u2} G (Finset.{u2} G) (Finset.hasMem.{u2} G) m (Finsupp.support.{u2, u1} G k (MulZeroClass.toHasZero.{u1} k (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} k (Semiring.toNonAssocSemiring.{u1} k _inst_2)))) x)) -> (Exists.{succ u2} G (fun (m' : G) => Exists.{0} (Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) m' s) (fun (H : Membership.Mem.{u2, u2} G (Set.{u2} G) (Set.hasMem.{u2} G) m' s) => Exists.{succ u2} G (fun (d : G) => Eq.{succ u2} G m (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toHasMul.{u2} G (Monoid.toMulOneClass.{u2} G _inst_1))) d m'))))))
but is expected to have type
  forall {k : Type.{u1}} {G : Type.{u2}} [_inst_1 : Monoid.{u2} G] [_inst_2 : Semiring.{u1} k] {s : Set.{u2} G} {x : MonoidAlgebra.{u1, u2} k G _inst_2}, Iff (Membership.mem.{max u1 u2, max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (Ideal.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)) (SetLike.instMembership.{max u1 u2, max u1 u2} (Ideal.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)) (MonoidAlgebra.{u1, u2} k G _inst_2) (Submodule.setLike.{max u1 u2, max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (Semiring.toNonAssocSemiring.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)))) (Semiring.toModule.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1)))) x (Ideal.span.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.semiring.{u1, u2} k G _inst_2 _inst_1) (Set.image.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (FunLike.coe.{max (succ u1) (succ u2), succ u2, max (succ u1) (succ u2)} (MonoidHom.{u2, max u2 u1} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) G (fun (_x : G) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : G) => MonoidAlgebra.{u1, u2} k G _inst_2) _x) (MulHomClass.toFunLike.{max u1 u2, u2, max u1 u2} (MonoidHom.{u2, max u2 u1} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) G (MonoidAlgebra.{u1, u2} k G _inst_2) (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G _inst_1)) (MulOneClass.toMul.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) (MonoidHomClass.toMulHomClass.{max u1 u2, u2, max u1 u2} (MonoidHom.{u2, max u2 u1} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))) G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1)))) (MonoidHom.monoidHomClass.{u2, max u1 u2} G (MonoidAlgebra.{u1, u2} k G _inst_2) (Monoid.toMulOneClass.{u2} G _inst_1) (MulZeroOneClass.toMulOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (NonAssocSemiring.toMulZeroOneClass.{max u1 u2} (MonoidAlgebra.{u1, u2} k G _inst_2) (MonoidAlgebra.nonAssocSemiring.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))))))) (MonoidAlgebra.of.{u1, u2} k G _inst_2 (Monoid.toMulOneClass.{u2} G _inst_1))) s))) (forall (m : G), (Membership.mem.{u2, u2} G (Finset.{u2} G) (Finset.instMembershipFinset.{u2} G) m (Finsupp.support.{u2, u1} G k (MonoidWithZero.toZero.{u1} k (Semiring.toMonoidWithZero.{u1} k _inst_2)) x)) -> (Exists.{succ u2} G (fun (m' : G) => And (Membership.mem.{u2, u2} G (Set.{u2} G) (Set.instMembershipSet.{u2} G) m' s) (Exists.{succ u2} G (fun (d : G) => Eq.{succ u2} G m (HMul.hMul.{u2, u2, u2} G G G (instHMul.{u2} G (MulOneClass.toMul.{u2} G (Monoid.toMulOneClass.{u2} G _inst_1))) d m'))))))
Case conversion may be inaccurate. Consider using '#align monoid_algebra.mem_ideal_span_of_image MonoidAlgebra.mem_ideal_span_of_imageₓ'. -/
/-- If `x` belongs to the ideal generated by generators in `s`, then every element of the support of
`x` factors through an element of `s`.

We could spell `∃ d, m = d * m` as `mul_opposite.op m' ∣ mul_opposite.op m` but this would be worse.
-/
theorem MonoidAlgebra.mem_ideal_span_of_image [Monoid G] [Semiring k] {s : Set G}
    {x : MonoidAlgebra k G} :
    x ∈ Ideal.span (MonoidAlgebra.of k G '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d * m' :=
  by
  let RHS : Ideal (MonoidAlgebra k G) :=
    { carrier := { p | ∀ m : G, m ∈ p.support → ∃ m' ∈ s, ∃ d, m = d * m' }
      add_mem' := fun x y hx hy m hm => by
        classical exact (Finset.mem_union.1 <| Finsupp.support_add hm).elim (hx m) (hy m)
      zero_mem' := fun m hm => by cases hm
      smul_mem' := fun x y hy m hm =>
        by
        replace hm := finset.mem_bUnion.mp (Finsupp.support_sum hm)
        obtain ⟨xm, hxm, hm⟩ := hm
        replace hm := finset.mem_bUnion.mp (Finsupp.support_sum hm)
        obtain ⟨ym, hym, hm⟩ := hm
        replace hm := finset.mem_singleton.mp (Finsupp.support_single_subset hm)
        obtain rfl := hm
        refine' (hy _ hym).imp fun sm => Exists.imp fun hsm => _
        rintro ⟨d, rfl⟩
        exact ⟨xm * d, (mul_assoc _ _ _).symm⟩ }
  change _ ↔ x ∈ RHS
  constructor
  · revert x
    refine' Ideal.span_le.2 _
    rintro _ ⟨i, hi, rfl⟩ m hm
    refine' ⟨_, hi, 1, _⟩
    obtain rfl := finset.mem_singleton.mp (Finsupp.support_single_subset hm)
    exact (one_mul _).symm
  · intro hx
    rw [← Finsupp.sum_single x]
    apply Ideal.sum_mem _ fun i hi => _
    obtain ⟨d, hd, d2, rfl⟩ := hx _ hi
    convert Ideal.mul_mem_left _ (id <| Finsupp.single d2 <| x (d2 * d) : MonoidAlgebra k G) _
    pick_goal 3
    refine' Ideal.subset_span ⟨_, hd, rfl⟩
    rw [id.def, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
#align monoid_algebra.mem_ideal_span_of_image MonoidAlgebra.mem_ideal_span_of_image

/- warning: add_monoid_algebra.mem_ideal_span_of'_image -> AddMonoidAlgebra.mem_ideal_span_of'_image is a dubious translation:
lean 3 declaration is
  forall {k : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Semiring.{u1} k] {s : Set.{u2} A} {x : AddMonoidAlgebra.{u1, u2} k A _inst_2}, Iff (Membership.Mem.{max u2 u1, max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Ideal.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)) (SetLike.hasMem.{max u2 u1, max u2 u1} (Ideal.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)) (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Submodule.setLike.{max u2 u1, max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Semiring.toNonAssocSemiring.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)))) (Semiring.toModule.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)))) x (Ideal.span.{max u2 u1} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1) (Set.image.{u2, max u2 u1} A (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.of'.{u1, u2} k A _inst_2) s))) (forall (m : A), (Membership.Mem.{u2, u2} A (Finset.{u2} A) (Finset.hasMem.{u2} A) m (Finsupp.support.{u2, u1} A k (MulZeroClass.toHasZero.{u1} k (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} k (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} k (Semiring.toNonAssocSemiring.{u1} k _inst_2)))) x)) -> (Exists.{succ u2} A (fun (m' : A) => Exists.{0} (Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) m' s) (fun (H : Membership.Mem.{u2, u2} A (Set.{u2} A) (Set.hasMem.{u2} A) m' s) => Exists.{succ u2} A (fun (d : A) => Eq.{succ u2} A m (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toHasAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_1))) d m'))))))
but is expected to have type
  forall {k : Type.{u1}} {A : Type.{u2}} [_inst_1 : AddMonoid.{u2} A] [_inst_2 : Semiring.{u1} k] {s : Set.{u2} A} {x : AddMonoidAlgebra.{u1, u2} k A _inst_2}, Iff (Membership.mem.{max u1 u2, max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Ideal.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)) (SetLike.instMembership.{max u1 u2, max u1 u2} (Ideal.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)) (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Submodule.setLike.{max u1 u2, max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1) (NonUnitalNonAssocSemiring.toAddCommMonoid.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (Semiring.toNonAssocSemiring.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)))) (Semiring.toModule.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1)))) x (Ideal.span.{max u1 u2} (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.semiring.{u1, u2} k A _inst_2 _inst_1) (Set.image.{u2, max u1 u2} A (AddMonoidAlgebra.{u1, u2} k A _inst_2) (AddMonoidAlgebra.of'.{u1, u2} k A _inst_2) s))) (forall (m : A), (Membership.mem.{u2, u2} A (Finset.{u2} A) (Finset.instMembershipFinset.{u2} A) m (Finsupp.support.{u2, u1} A k (MonoidWithZero.toZero.{u1} k (Semiring.toMonoidWithZero.{u1} k _inst_2)) x)) -> (Exists.{succ u2} A (fun (m' : A) => And (Membership.mem.{u2, u2} A (Set.{u2} A) (Set.instMembershipSet.{u2} A) m' s) (Exists.{succ u2} A (fun (d : A) => Eq.{succ u2} A m (HAdd.hAdd.{u2, u2, u2} A A A (instHAdd.{u2} A (AddZeroClass.toAdd.{u2} A (AddMonoid.toAddZeroClass.{u2} A _inst_1))) d m'))))))
Case conversion may be inaccurate. Consider using '#align add_monoid_algebra.mem_ideal_span_of'_image AddMonoidAlgebra.mem_ideal_span_of'_imageₓ'. -/
/-- If `x` belongs to the ideal generated by generators in `s`, then every element of the support of
`x` factors additively through an element of `s`.
-/
theorem AddMonoidAlgebra.mem_ideal_span_of'_image [AddMonoid A] [Semiring k] {s : Set A}
    {x : AddMonoidAlgebra k A} :
    x ∈ Ideal.span (AddMonoidAlgebra.of' k A '' s) ↔ ∀ m ∈ x.support, ∃ m' ∈ s, ∃ d, m = d + m' :=
  @MonoidAlgebra.mem_ideal_span_of_image k (Multiplicative A) _ _ _ _
#align add_monoid_algebra.mem_ideal_span_of'_image AddMonoidAlgebra.mem_ideal_span_of'_image

