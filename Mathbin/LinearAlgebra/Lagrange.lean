/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson

! This file was ported from Lean 3 source module linear_algebra.lagrange
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.LinearAlgebra.Vandermonde
import Mathbin.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions
* In everything that follows, `s : finset ι` is a finite set of indexes, with `v : ι → F` an
indexing of the field over some type. We call the image of v on s the interpolation nodes,
though strictly unique nodes are only defined when v is injective on s.
* `lagrange.basis_divisor x y`, with `x y : F`. These are the normalised irreducible factors of
the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
are distinct.
* `lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
and `0` at `v j` for `i ≠ j`.
* `lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
associated with the _nodes_`x i`.
* `lagrange.interpolate_at v f`, where `v : ι ↪ F` and `ι` is a fintype, and `f : F → F` is a
function from the field to itself: this is the Lagrange interpolant that evaluates to `f (x i)`
at `x i`, and so approximates the function `f`. This is just a special case of the general
interpolation, where the values are given by a known function `f`.
-/


open Polynomial BigOperators

section PolynomialDetermination

namespace Polynomial

variable {R : Type _} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype

variable (s : Finset R)

/- warning: polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero -> Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.Mem.{u1, u1} R (Finset.{u1} R) (Finset.hasMem.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f (OfNat.ofNat.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 0 (OfNat.mk.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 0 (Zero.zero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.zero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.mem.{u1, u1} R (Finset.{u1} R) (Finset.instMembershipFinset.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x f) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_2))))))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f (OfNat.ofNat.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.zero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zeroₓ'. -/
theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < s.card)
    (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 :=
  by
  rw [← mem_degree_lt] at degree_f_lt
  simp_rw [eval_eq_sum_degree_lt_equiv degree_f_lt] at eval_f
  rw [← degree_lt_equiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (injective.comp (embedding.subtype _).inj' (equiv_fin_of_card_eq (card_coe _)).symm.Injective)
      fun _ => eval_f _ (Finset.coe_mem _)
#align polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero

/- warning: polynomial.eq_of_degree_sub_lt_of_eval_finset_eq -> Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {g : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.Mem.{u1, u1} R (Finset.{u1} R) (Finset.hasMem.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x g))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {g : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.mem.{u1, u1} R (Finset.{u1} R) (Finset.instMembershipFinset.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x g))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f g)
Case conversion may be inaccurate. Consider using '#align polynomial.eq_of_degree_sub_lt_of_eval_finset_eq Polynomial.eq_of_degree_sub_lt_of_eval_finset_eqₓ'. -/
theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < s.card)
    (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g :=
  by
  rw [← sub_eq_zero]
  refine' eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt _
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg
#align polynomial.eq_of_degree_sub_lt_of_eval_finset_eq Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq

/- warning: polynomial.eq_of_degrees_lt_of_eval_finset_eq -> Polynomial.eq_of_degrees_lt_of_eval_finset_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {g : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u1} R s))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) g) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.Mem.{u1, u1} R (Finset.{u1} R) (Finset.hasMem.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) x g))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {g : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} (s : Finset.{u1} R), (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u1} R s))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) g) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u1} R s))) -> (forall (x : R), (Membership.mem.{u1, u1} R (Finset.{u1} R) (Finset.instMembershipFinset.{u1} R) x s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x f) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) x g))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f g)
Case conversion may be inaccurate. Consider using '#align polynomial.eq_of_degrees_lt_of_eval_finset_eq Polynomial.eq_of_degrees_lt_of_eval_finset_eqₓ'. -/
theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < s.card)
    (degree_g_lt : g.degree < s.card) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g :=
  by
  rw [← mem_degree_lt] at degree_f_lt degree_g_lt
  refine' eq_of_degree_sub_lt_of_eval_finset_eq _ _ eval_fg
  rw [← mem_degree_lt]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt
#align polynomial.eq_of_degrees_lt_of_eval_finset_eq Polynomial.eq_of_degrees_lt_of_eval_finset_eq

end Finset

section Indexed

open Finset

variable {ι : Type _} {v : ι → R} (s : Finset ι)

/- warning: polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero -> Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (v i) f) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f (OfNat.ofNat.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 0 (OfNat.mk.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) 0 (Zero.zero.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.zero.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v (Finset.toSet.{u2} ι s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (v i) f) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1) _inst_2))))))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f (OfNat.ofNat.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) 0 (Zero.toOfNat0.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.zero.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zeroₓ'. -/
theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < s.card) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_inj_on hvs] at degree_f_lt
    refine' eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt _
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj
#align polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero

/- warning: polynomial.eq_of_degree_sub_lt_of_eval_index_eq -> Polynomial.eq_of_degree_sub_lt_of_eval_index_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {g : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (v i) f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (v i) g))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {g : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v (Finset.toSet.{u2} ι s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (HSub.hSub.{u1, u1, u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (instHSub.{u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Polynomial.sub.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (v i) f) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (v i) g))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f g)
Case conversion may be inaccurate. Consider using '#align polynomial.eq_of_degree_sub_lt_of_eval_index_eq Polynomial.eq_of_degree_sub_lt_of_eval_index_eqₓ'. -/
theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < s.card) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine' eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt _
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg
#align polynomial.eq_of_degree_sub_lt_of_eval_index_eq Polynomial.eq_of_degree_sub_lt_of_eval_index_eq

/- warning: polynomial.eq_of_degrees_lt_of_eval_index_eq -> Polynomial.eq_of_degrees_lt_of_eval_index_eq is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))] {f : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {g : Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) f) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u2} ι s))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toHasLt.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) g) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (v i) f) (Polynomial.eval.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1)) (v i) g))) -> (Eq.{succ u1} (Polynomial.{u1} R (Ring.toSemiring.{u1} R (CommRing.toRing.{u1} R _inst_1))) f g)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] [_inst_2 : IsDomain.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))] {f : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {g : Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))} {ι : Type.{u2}} {v : ι -> R} (s : Finset.{u2} ι), (Set.InjOn.{u2, u1} ι R v (Finset.toSet.{u2} ι s)) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) f) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u2} ι s))) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) g) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u2} ι s))) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} R (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (v i) f) (Polynomial.eval.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (v i) g))) -> (Eq.{succ u1} (Polynomial.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) f g)
Case conversion may be inaccurate. Consider using '#align polynomial.eq_of_degrees_lt_of_eval_index_eq Polynomial.eq_of_degrees_lt_of_eval_index_eqₓ'. -/
theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card)
    (degree_g_lt : g.degree < s.card) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g :=
  by
  refine' eq_of_degree_sub_lt_of_eval_index_eq _ hvs _ eval_fg
  rw [← mem_degree_lt] at degree_f_lt degree_g_lt⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt
#align polynomial.eq_of_degrees_lt_of_eval_index_eq Polynomial.eq_of_degrees_lt_of_eval_index_eq

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

variable {F : Type _} [Field F]

section BasisDivisor

variable {x y : F}

#print Lagrange.basisDivisor /-
/-- `basis_divisor x y` is the unique linear or constant polynomial such that
when evaluated at `x` it gives `1` and `y` it gives `0` (where when `x = y` it is identically `0`).
Such polynomials are the building blocks for the Lagrange interpolants. -/
def basisDivisor (x y : F) : F[X] :=
  C (x - y)⁻¹ * (X - C y)
#align lagrange.basis_divisor Lagrange.basisDivisor
-/

#print Lagrange.basisDivisor_self /-
theorem basisDivisor_self : basisDivisor x x = 0 := by
  simp only [basis_divisor, sub_self, inv_zero, map_zero, MulZeroClass.zero_mul]
#align lagrange.basis_divisor_self Lagrange.basisDivisor_self
-/

#print Lagrange.basisDivisor_inj /-
theorem basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y :=
  by
  simp_rw [basis_divisor, mul_eq_zero, X_sub_C_ne_zero, or_false_iff, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy
#align lagrange.basis_divisor_inj Lagrange.basisDivisor_inj
-/

#print Lagrange.basisDivisor_eq_zero_iff /-
@[simp]
theorem basisDivisor_eq_zero_iff : basisDivisor x y = 0 ↔ x = y :=
  ⟨basisDivisor_inj, fun H => H ▸ basisDivisor_self⟩
#align lagrange.basis_divisor_eq_zero_iff Lagrange.basisDivisor_eq_zero_iff
-/

#print Lagrange.basisDivisor_ne_zero_iff /-
theorem basisDivisor_ne_zero_iff : basisDivisor x y ≠ 0 ↔ x ≠ y := by
  rw [Ne.def, basis_divisor_eq_zero_iff]
#align lagrange.basis_divisor_ne_zero_iff Lagrange.basisDivisor_ne_zero_iff
-/

#print Lagrange.degree_basisDivisor_of_ne /-
theorem degree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).degree = 1 :=
  by
  rw [basis_divisor, degree_mul, degree_X_sub_C, degree_C, zero_add]
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)
#align lagrange.degree_basis_divisor_of_ne Lagrange.degree_basisDivisor_of_ne
-/

#print Lagrange.degree_basisDivisor_self /-
@[simp]
theorem degree_basisDivisor_self : (basisDivisor x x).degree = ⊥ := by
  rw [basis_divisor_self, degree_zero]
#align lagrange.degree_basis_divisor_self Lagrange.degree_basisDivisor_self
-/

#print Lagrange.natDegree_basisDivisor_self /-
theorem natDegree_basisDivisor_self : (basisDivisor x x).natDegree = 0 := by
  rw [basis_divisor_self, nat_degree_zero]
#align lagrange.nat_degree_basis_divisor_self Lagrange.natDegree_basisDivisor_self
-/

#print Lagrange.natDegree_basisDivisor_of_ne /-
theorem natDegree_basisDivisor_of_ne (hxy : x ≠ y) : (basisDivisor x y).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some (degree_basisDivisor_of_ne hxy)
#align lagrange.nat_degree_basis_divisor_of_ne Lagrange.natDegree_basisDivisor_of_ne
-/

/- warning: lagrange.eval_basis_divisor_right -> Lagrange.eval_basisDivisor_right is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {x : F} {y : F}, Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) y (Lagrange.basisDivisor.{u1} F _inst_1 x y)) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {x : F} {y : F}, Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) y (Lagrange.basisDivisor.{u1} F _inst_1 x y)) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_basis_divisor_right Lagrange.eval_basisDivisor_rightₓ'. -/
@[simp]
theorem eval_basisDivisor_right : eval y (basisDivisor x y) = 0 := by
  simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, MulZeroClass.mul_zero]
#align lagrange.eval_basis_divisor_right Lagrange.eval_basisDivisor_right

/- warning: lagrange.eval_basis_divisor_left_of_ne -> Lagrange.eval_basisDivisor_left_of_ne is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {x : F} {y : F}, (Ne.{succ u1} F x y) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) x (Lagrange.basisDivisor.{u1} F _inst_1 x y)) (OfNat.ofNat.{u1} F 1 (OfNat.mk.{u1} F 1 (One.one.{u1} F (AddMonoidWithOne.toOne.{u1} F (AddGroupWithOne.toAddMonoidWithOne.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {x : F} {y : F}, (Ne.{succ u1} F x y) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) x (Lagrange.basisDivisor.{u1} F _inst_1 x y)) (OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F (Semiring.toOne.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_basis_divisor_left_of_ne Lagrange.eval_basisDivisor_left_of_neₓ'. -/
theorem eval_basisDivisor_left_of_ne (hxy : x ≠ y) : eval x (basisDivisor x y) = 1 :=
  by
  simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel (sub_ne_zero_of_ne hxy)
#align lagrange.eval_basis_divisor_left_of_ne Lagrange.eval_basisDivisor_left_of_ne

end BasisDivisor

section Basis

open Finset

variable {ι : Type _} [DecidableEq ι] {s : Finset ι} {v : ι → F} {i j : ι}

#print Lagrange.basis /-
/-- Lagrange basis polynomials indexed by `s : finset ι`, defined at nodes `v i` for a
map `v : ι → F`. For `i, j ∈ s`, `basis s v i` evaluates to 0 at `v j` for `i ≠ j`. When
`v` is injective on `s`, `basis s v i` evaluates to 1 at `v i`. -/
protected def basis (s : Finset ι) (v : ι → F) (i : ι) : F[X] :=
  ∏ j in s.eraseₓ i, basisDivisor (v i) (v j)
#align lagrange.basis Lagrange.basis
-/

/- warning: lagrange.basis_empty -> Lagrange.basis_empty is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {v : ι -> F} {i : ι}, Eq.{succ u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.hasEmptyc.{u2} ι)) v i) (OfNat.ofNat.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (OfNat.mk.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (One.one.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Polynomial.hasOne.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} ι] {v : ι -> F} {i : ι}, Eq.{succ u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Lagrange.basis.{u2, u1} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) v i) (OfNat.ofNat.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) 1 (One.toOfNat1.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Polynomial.one.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))))))
Case conversion may be inaccurate. Consider using '#align lagrange.basis_empty Lagrange.basis_emptyₓ'. -/
@[simp]
theorem basis_empty : Lagrange.basis ∅ v i = 1 :=
  rfl
#align lagrange.basis_empty Lagrange.basis_empty

/- warning: lagrange.basis_singleton -> Lagrange.basis_singleton is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {v : ι -> F} (i : ι), Eq.{succ u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) (Singleton.singleton.{u2, u2} ι (Finset.{u2} ι) (Finset.hasSingleton.{u2} ι) i) v i) (OfNat.ofNat.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (OfNat.mk.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (One.one.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Polynomial.hasOne.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} ι] {v : ι -> F} (i : ι), Eq.{succ u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Lagrange.basis.{u2, u1} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) (Singleton.singleton.{u1, u1} ι (Finset.{u1} ι) (Finset.instSingletonFinset.{u1} ι) i) v i) (OfNat.ofNat.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) 1 (One.toOfNat1.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Polynomial.one.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))))))
Case conversion may be inaccurate. Consider using '#align lagrange.basis_singleton Lagrange.basis_singletonₓ'. -/
@[simp]
theorem basis_singleton (i : ι) : Lagrange.basis {i} v i = 1 := by
  rw [Lagrange.basis, erase_singleton, prod_empty]
#align lagrange.basis_singleton Lagrange.basis_singleton

#print Lagrange.basis_pair_left /-
@[simp]
theorem basis_pair_left (hij : i ≠ j) : Lagrange.basis {i, j} v i = basisDivisor (v i) (v j) := by
  simp only [Lagrange.basis, hij, erase_insert_eq_erase, erase_eq_of_not_mem, mem_singleton,
    not_false_iff, prod_singleton]
#align lagrange.basis_pair_left Lagrange.basis_pair_left
-/

#print Lagrange.basis_pair_right /-
@[simp]
theorem basis_pair_right (hij : i ≠ j) : Lagrange.basis {i, j} v j = basisDivisor (v j) (v i) := by
  rw [pair_comm]; exact basis_pair_left hij.symm
#align lagrange.basis_pair_right Lagrange.basis_pair_right
-/

#print Lagrange.basis_ne_zero /-
theorem basis_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : Lagrange.basis s v i ≠ 0 :=
  by
  simp_rw [Lagrange.basis, prod_ne_zero_iff, Ne.def, mem_erase]
  rintro j ⟨hij, hj⟩
  rw [basis_divisor_eq_zero_iff, hvs.eq_iff hi hj]
  exact hij.symm
#align lagrange.basis_ne_zero Lagrange.basis_ne_zero
-/

/- warning: lagrange.eval_basis_self -> Lagrange.eval_basis_self is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {s : Finset.{u2} ι} {v : ι -> F} {i : ι}, (Set.InjOn.{u2, u1} ι F v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (v i) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (OfNat.ofNat.{u1} F 1 (OfNat.mk.{u1} F 1 (One.one.{u1} F (AddMonoidWithOne.toOne.{u1} F (AddGroupWithOne.toAddMonoidWithOne.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {s : Finset.{u2} ι} {v : ι -> F} {i : ι}, (Set.InjOn.{u2, u1} ι F v (Finset.toSet.{u2} ι s)) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) (v i) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (OfNat.ofNat.{u1} F 1 (One.toOfNat1.{u1} F (Semiring.toOne.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_basis_self Lagrange.eval_basis_selfₓ'. -/
@[simp]
theorem eval_basis_self (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).eval (v i) = 1 :=
  by
  rw [Lagrange.basis, eval_prod]
  refine' prod_eq_one fun j H => _
  rw [eval_basis_divisor_left_of_ne]
  rcases mem_erase.mp H with ⟨hij, hj⟩
  exact mt (hvs hi hj) hij.symm
#align lagrange.eval_basis_self Lagrange.eval_basis_self

/- warning: lagrange.eval_basis_of_ne -> Lagrange.eval_basis_of_ne is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {s : Finset.{u2} ι} {v : ι -> F} {i : ι} {j : ι}, (Ne.{succ u2} ι i j) -> (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) j s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (v j) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} [_inst_2 : DecidableEq.{succ u2} ι] {s : Finset.{u2} ι} {v : ι -> F} {i : ι} {j : ι}, (Ne.{succ u2} ι i j) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) j s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) (v j) (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_basis_of_ne Lagrange.eval_basis_of_neₓ'. -/
@[simp]
theorem eval_basis_of_ne (hij : i ≠ j) (hj : j ∈ s) : (Lagrange.basis s v i).eval (v j) = 0 :=
  by
  simp_rw [Lagrange.basis, eval_prod, prod_eq_zero_iff]
  exact ⟨j, ⟨mem_erase.mpr ⟨hij.symm, hj⟩, eval_basis_divisor_right⟩⟩
#align lagrange.eval_basis_of_ne Lagrange.eval_basis_of_ne

#print Lagrange.natDegree_basis /-
@[simp]
theorem natDegree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree = s.card - 1 :=
  by
  have H : ∀ j, j ∈ s.erase i → basis_divisor (v i) (v j) ≠ 0 :=
    by
    simp_rw [Ne.def, mem_erase, basis_divisor_eq_zero_iff]
    exact fun j ⟨hij₁, hj⟩ hij₂ => hij₁ (hvs hj hi hij₂.symm)
  rw [← card_erase_of_mem hi, card_eq_sum_ones]
  convert nat_degree_prod _ _ H using 1
  refine' sum_congr rfl fun j hj => (nat_degree_basis_divisor_of_ne _).symm
  rw [Ne.def, ← basis_divisor_eq_zero_iff]
  exact H _ hj
#align lagrange.nat_degree_basis Lagrange.natDegree_basis
-/

#print Lagrange.degree_basis /-
theorem degree_basis (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (Lagrange.basis s v i).degree = ↑(s.card - 1) := by
  rw [degree_eq_nat_degree (basis_ne_zero hvs hi), nat_degree_basis hvs hi]
#align lagrange.degree_basis Lagrange.degree_basis
-/

#print Lagrange.sum_basis /-
theorem sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) : (∑ j in s, Lagrange.basis s v j) = 1 :=
  by
  refine' eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) _) _ _
  · rw [Finset.sup_lt_iff (WithBot.bot_lt_coe s.card)]
    intro i hi
    rw [degree_basis hvs hi, WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem hi)
  · rw [degree_one, ← WithBot.coe_zero, WithBot.coe_lt_coe]
    exact nonempty.card_pos hs
  · intro i hi
    rw [eval_finset_sum, eval_one, ← add_sum_erase _ _ hi, eval_basis_self hvs hi,
      add_right_eq_self]
    refine' sum_eq_zero fun j hj => _
    rcases mem_erase.mp hj with ⟨hij, hj⟩
    rw [eval_basis_of_ne hij hi]
#align lagrange.sum_basis Lagrange.sum_basis
-/

#print Lagrange.basisDivisor_add_symm /-
theorem basisDivisor_add_symm {x y : F} (hxy : x ≠ y) : basisDivisor x y + basisDivisor y x = 1 :=
  by
  classical rw [←
      sum_basis (Set.injOn_of_injective Function.injective_id _) ⟨x, mem_insert_self _ {y}⟩,
      sum_insert (not_mem_singleton.mpr hxy), sum_singleton, basis_pair_left hxy,
      basis_pair_right hxy, id, id]
#align lagrange.basis_divisor_add_symm Lagrange.basisDivisor_add_symm
-/

end Basis

section Interpolate

open Finset

variable {ι : Type _} [DecidableEq ι] {s t : Finset ι} {i j : ι} {v : ι → F} (r r' : ι → F)

#print Lagrange.interpolate /-
/-- Lagrange interpolation: given a finset `s : finset ι`, a nodal map  `v : ι → F` injective on
`s` and a value function `r : ι → F`,  `interpolate s v r` is the unique
polynomial of degree `< s.card` that takes value `r i` on `v i` for all `i` in `s`. -/
@[simps]
def interpolate (s : Finset ι) (v : ι → F) : (ι → F) →ₗ[F] F[X]
    where
  toFun r := ∑ i in s, C (r i) * Lagrange.basis s v i
  map_add' f g := by simp_rw [← Finset.sum_add_distrib, ← add_mul, ← C_add, Pi.add_apply]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
#align lagrange.interpolate Lagrange.interpolate
-/

/- warning: lagrange.interpolate_empty -> Lagrange.interpolate_empty is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_empty Lagrange.interpolate_emptyₓ'. -/
@[simp]
theorem interpolate_empty : interpolate ∅ v r = 0 := by rw [interpolate_apply, sum_empty]
#align lagrange.interpolate_empty Lagrange.interpolate_empty

/- warning: lagrange.interpolate_singleton -> Lagrange.interpolate_singleton is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_singleton Lagrange.interpolate_singletonₓ'. -/
@[simp]
theorem interpolate_singleton : interpolate {i} v r = C (r i) := by
  rw [interpolate_apply, sum_singleton, basis_singleton, mul_one]
#align lagrange.interpolate_singleton Lagrange.interpolate_singleton

/- warning: lagrange.interpolate_one -> Lagrange.interpolate_one is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_one Lagrange.interpolate_oneₓ'. -/
theorem interpolate_one (hvs : Set.InjOn v s) (hs : s.Nonempty) : interpolate s v 1 = 1 := by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]; exact sum_basis hvs hs
#align lagrange.interpolate_one Lagrange.interpolate_one

/- warning: lagrange.eval_interpolate_at_node -> Lagrange.eval_interpolate_at_node is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eval_interpolate_at_node Lagrange.eval_interpolate_at_nodeₓ'. -/
theorem eval_interpolate_at_node (hvs : Set.InjOn v s) (hi : i ∈ s) :
    eval (v i) (interpolate s v r) = r i :=
  by
  rw [interpolate_apply, eval_finset_sum, ← add_sum_erase _ _ hi]
  simp_rw [eval_mul, eval_C, eval_basis_self hvs hi, mul_one, add_right_eq_self]
  refine' sum_eq_zero fun j H => _
  rw [eval_basis_of_ne (mem_erase.mp H).1 hi, MulZeroClass.mul_zero]
#align lagrange.eval_interpolate_at_node Lagrange.eval_interpolate_at_node

/- warning: lagrange.degree_interpolate_le -> Lagrange.degree_interpolate_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.degree_interpolate_le Lagrange.degree_interpolate_leₓ'. -/
theorem degree_interpolate_le (hvs : Set.InjOn v s) : (interpolate s v r).degree ≤ ↑(s.card - 1) :=
  by
  refine' (degree_sum_le _ _).trans _
  rw [Finset.sup_le_iff]
  intro i hi
  rw [degree_mul, degree_basis hvs hi]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add, WithBot.coe_le_coe]
#align lagrange.degree_interpolate_le Lagrange.degree_interpolate_le

/- warning: lagrange.degree_interpolate_lt -> Lagrange.degree_interpolate_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.degree_interpolate_lt Lagrange.degree_interpolate_ltₓ'. -/
theorem degree_interpolate_lt (hvs : Set.InjOn v s) : (interpolate s v r).degree < s.card :=
  by
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine' lt_of_le_of_lt (degree_interpolate_le _ hvs) _
    rw [WithBot.coe_lt_coe]
    exact Nat.sub_lt (nonempty.card_pos h) zero_lt_one
#align lagrange.degree_interpolate_lt Lagrange.degree_interpolate_lt

/- warning: lagrange.degree_interpolate_erase_lt -> Lagrange.degree_interpolate_erase_lt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.degree_interpolate_erase_lt Lagrange.degree_interpolate_erase_ltₓ'. -/
theorem degree_interpolate_erase_lt (hvs : Set.InjOn v s) (hi : i ∈ s) :
    (interpolate (s.eraseₓ i) v r).degree < ↑(s.card - 1) :=
  by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _ (Set.InjOn.mono (coe_subset.mpr (erase_subset _ _)) hvs)
#align lagrange.degree_interpolate_erase_lt Lagrange.degree_interpolate_erase_lt

/- warning: lagrange.values_eq_on_of_interpolate_eq -> Lagrange.values_eq_on_of_interpolate_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.values_eq_on_of_interpolate_eq Lagrange.values_eq_on_of_interpolate_eqₓ'. -/
theorem values_eq_on_of_interpolate_eq (hvs : Set.InjOn v s)
    (hrr' : interpolate s v r = interpolate s v r') : ∀ i ∈ s, r i = r' i := fun _ hi => by
  rw [← eval_interpolate_at_node r hvs hi, hrr', eval_interpolate_at_node r' hvs hi]
#align lagrange.values_eq_on_of_interpolate_eq Lagrange.values_eq_on_of_interpolate_eq

/- warning: lagrange.interpolate_eq_of_values_eq_on -> Lagrange.interpolate_eq_of_values_eq_on is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_eq_of_values_eq_on Lagrange.interpolate_eq_of_values_eq_onₓ'. -/
theorem interpolate_eq_of_values_eq_on (hrr' : ∀ i ∈ s, r i = r' i) :
    interpolate s v r = interpolate s v r' :=
  sum_congr rfl fun i hi => by rw [hrr' _ hi]
#align lagrange.interpolate_eq_of_values_eq_on Lagrange.interpolate_eq_of_values_eq_on

/- warning: lagrange.interpolate_eq_iff_values_eq_on -> Lagrange.interpolate_eq_iff_values_eq_on is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_eq_iff_values_eq_on Lagrange.interpolate_eq_iff_values_eq_onₓ'. -/
theorem interpolate_eq_iff_values_eq_on (hvs : Set.InjOn v s) :
    interpolate s v r = interpolate s v r' ↔ ∀ i ∈ s, r i = r' i :=
  ⟨values_eq_on_of_interpolate_eq _ _ hvs, interpolate_eq_of_values_eq_on _ _⟩
#align lagrange.interpolate_eq_iff_values_eq_on Lagrange.interpolate_eq_iff_values_eq_on

/- warning: lagrange.eq_interpolate -> Lagrange.eq_interpolate is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eq_interpolate Lagrange.eq_interpolateₓ'. -/
theorem eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card) :
    f = interpolate s v fun i => f.eval (v i) :=
  eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _ hvs) fun i hi =>
    (eval_interpolate_at_node _ hvs hi).symm
#align lagrange.eq_interpolate Lagrange.eq_interpolate

/- warning: lagrange.eq_interpolate_of_eval_eq -> Lagrange.eq_interpolate_of_eval_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eq_interpolate_of_eval_eq Lagrange.eq_interpolate_of_eval_eqₓ'. -/
theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < s.card)
    (eval_f : ∀ i ∈ s, f.eval (v i) = r i) : f = interpolate s v r := by
  rw [eq_interpolate hvs degree_f_lt]; exact interpolate_eq_of_values_eq_on _ _ eval_f
#align lagrange.eq_interpolate_of_eval_eq Lagrange.eq_interpolate_of_eval_eq

/- warning: lagrange.eq_interpolate_iff -> Lagrange.eq_interpolate_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eq_interpolate_iff Lagrange.eq_interpolate_iffₓ'. -/
/-- This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) :
    (f.degree < s.card ∧ ∀ i ∈ s, eval (v i) f = r i) ↔ f = interpolate s v r :=
  by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]; exact ⟨degree_interpolate_lt _ hvs, fun _ hi => eval_interpolate_at_node _ hvs hi⟩
#align lagrange.eq_interpolate_iff Lagrange.eq_interpolate_iff

#print Lagrange.funEquivDegreeLT /-
/-- Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `fintype.card ι`.-/
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F s.card ≃ₗ[F] s → F
    where
  toFun f i := f.1.eval (v i)
  map_add' f g := funext fun v => eval_add
  map_smul' c f := funext <| by simp
  invFun r :=
    ⟨interpolate s v fun x => if hx : x ∈ s then r ⟨x, hx⟩ else 0,
      mem_degreeLT.2 <| degree_interpolate_lt _ hvs⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, Subtype.coe_mk, dite_eq_ite]
    rw [mem_degree_lt] at hf
    nth_rw_rhs 1 [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => if_pos hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [Subtype.coe_mk, eval_interpolate_at_node _ hvs hi]
    exact dif_pos hi
#align lagrange.fun_equiv_degree_lt Lagrange.funEquivDegreeLT
-/

/- warning: lagrange.interpolate_eq_sum_interpolate_insert_sdiff -> Lagrange.interpolate_eq_sum_interpolate_insert_sdiff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_eq_sum_interpolate_insert_sdiff Lagrange.interpolate_eq_sum_interpolate_insert_sdiffₓ'. -/
theorem interpolate_eq_sum_interpolate_insert_sdiff (hvt : Set.InjOn v t) (hs : s.Nonempty)
    (hst : s ⊆ t) :
    interpolate t v r = ∑ i in s, interpolate (insert i (t \ s)) v r * Lagrange.basis s v i :=
  by
  symm
  refine' eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) _) fun i hi => _
  · simp_rw [Finset.sup_lt_iff (WithBot.bot_lt_coe t.card), degree_mul]
    intro i hi
    have hs : 1 ≤ s.card := nonempty.card_pos ⟨_, hi⟩
    have hst' : s.card ≤ t.card := card_le_of_subset hst
    have H : t.card = 1 + (t.card - s.card) + (s.card - 1) := by
      rw [add_assoc, tsub_add_tsub_cancel hst' hs, ← add_tsub_assoc_of_le (hs.trans hst'),
        Nat.succ_add_sub_one, zero_add]
    rw [degree_basis (Set.InjOn.mono hst hvt) hi, H, WithBot.coe_add,
      WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (s.card - 1))]
    convert degree_interpolate_lt _
        (hvt.mono (coe_subset.mpr (insert_subset.mpr ⟨hst hi, sdiff_subset _ _⟩)))
    rw [card_insert_of_not_mem (not_mem_sdiff_of_mem_right hi), card_sdiff hst, add_comm]
  · simp_rw [eval_finset_sum, eval_mul]
    by_cases hi' : i ∈ s
    · rw [← add_sum_erase _ _ hi', eval_basis_self (hvt.mono hst) hi',
        eval_interpolate_at_node _
          (hvt.mono (coe_subset.mpr (insert_subset.mpr ⟨hi, sdiff_subset _ _⟩)))
          (mem_insert_self _ _),
        mul_one, add_right_eq_self]
      refine' sum_eq_zero fun j hj => _
      rcases mem_erase.mp hj with ⟨hij, hj⟩
      rw [eval_basis_of_ne hij hi', MulZeroClass.mul_zero]
    · have H : (∑ j in s, eval (v i) (Lagrange.basis s v j)) = 1 := by
        rw [← eval_finset_sum, sum_basis (hvt.mono hst) hs, eval_one]
      rw [← mul_one (r i), ← H, mul_sum]
      refine' sum_congr rfl fun j hj => _
      congr
      exact
        eval_interpolate_at_node _ (hvt.mono (insert_subset.mpr ⟨hst hj, sdiff_subset _ _⟩))
          (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))
#align lagrange.interpolate_eq_sum_interpolate_insert_sdiff Lagrange.interpolate_eq_sum_interpolate_insert_sdiff

/- warning: lagrange.interpolate_eq_add_interpolate_erase -> Lagrange.interpolate_eq_add_interpolate_erase is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_eq_add_interpolate_erase Lagrange.interpolate_eq_add_interpolate_eraseₓ'. -/
theorem interpolate_eq_add_interpolate_erase (hvs : Set.InjOn v s) (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    interpolate s v r =
      interpolate (s.eraseₓ j) v r * basisDivisor (v i) (v j) +
        interpolate (s.eraseₓ i) v r * basisDivisor (v j) (v i) :=
  by
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ hvs ⟨i, mem_insert_self i {j}⟩ _,
    sum_insert (not_mem_singleton.mpr hij), sum_singleton, basis_pair_left hij,
    basis_pair_right hij, sdiff_insert_insert_of_mem_of_not_mem hi (not_mem_singleton.mpr hij),
    sdiff_singleton_eq_erase, pair_comm,
    sdiff_insert_insert_of_mem_of_not_mem hj (not_mem_singleton.mpr hij.symm),
    sdiff_singleton_eq_erase]
  · exact insert_subset.mpr ⟨hi, singleton_subset_iff.mpr hj⟩
#align lagrange.interpolate_eq_add_interpolate_erase Lagrange.interpolate_eq_add_interpolate_erase

end Interpolate

section Nodal

open Finset Polynomial

variable {ι : Type _} {s : Finset ι} {v : ι → F} {i : ι} (r : ι → F) {x : F}

#print Lagrange.nodal /-
/-- `nodal s v` is the unique monic polynomial whose roots are the nodes defined by `v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
def nodal (s : Finset ι) (v : ι → F) : F[X] :=
  ∏ i in s, X - C (v i)
#align lagrange.nodal Lagrange.nodal
-/

/- warning: lagrange.nodal_eq -> Lagrange.nodal_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_eq Lagrange.nodal_eqₓ'. -/
theorem nodal_eq (s : Finset ι) (v : ι → F) : nodal s v = ∏ i in s, X - C (v i) :=
  rfl
#align lagrange.nodal_eq Lagrange.nodal_eq

/- warning: lagrange.nodal_empty -> Lagrange.nodal_empty is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {v : ι -> F}, Eq.{succ u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Lagrange.nodal.{u1, u2} F _inst_1 ι (EmptyCollection.emptyCollection.{u2} (Finset.{u2} ι) (Finset.hasEmptyc.{u2} ι)) v) (OfNat.ofNat.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (OfNat.mk.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) 1 (One.one.{u1} (Polynomial.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) (Polynomial.hasOne.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} {v : ι -> F}, Eq.{succ u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Lagrange.nodal.{u2, u1} F _inst_1 ι (EmptyCollection.emptyCollection.{u1} (Finset.{u1} ι) (Finset.instEmptyCollectionFinset.{u1} ι)) v) (OfNat.ofNat.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) 1 (One.toOfNat1.{u2} (Polynomial.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1)))) (Polynomial.one.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))))))
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_empty Lagrange.nodal_emptyₓ'. -/
@[simp]
theorem nodal_empty : nodal ∅ v = 1 :=
  rfl
#align lagrange.nodal_empty Lagrange.nodal_empty

/- warning: lagrange.degree_nodal -> Lagrange.degree_nodal is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F}, Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (WithBot.{0} Nat) (HasLiftT.mk.{1, 1} Nat (WithBot.{0} Nat) (CoeTCₓ.coe.{1, 1} Nat (WithBot.{0} Nat) (WithBot.hasCoeT.{0} Nat))) (Finset.card.{u2} ι s))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} {s : Finset.{u1} ι} {v : ι -> F}, Eq.{1} (WithBot.{0} Nat) (Polynomial.degree.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))) (Lagrange.nodal.{u2, u1} F _inst_1 ι s v)) (Nat.cast.{0} (WithBot.{0} Nat) (Semiring.toNatCast.{0} (WithBot.{0} Nat) (OrderedSemiring.toSemiring.{0} (WithBot.{0} Nat) (OrderedCommSemiring.toOrderedSemiring.{0} (WithBot.{0} Nat) (WithBot.orderedCommSemiring.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.canonicallyOrderedCommSemiring Nat.nontrivial)))) (Finset.card.{u1} ι s))
Case conversion may be inaccurate. Consider using '#align lagrange.degree_nodal Lagrange.degree_nodalₓ'. -/
theorem degree_nodal : (nodal s v).degree = s.card := by
  simp_rw [nodal, degree_prod, degree_X_sub_C, sum_const, Nat.smul_one_eq_coe]
#align lagrange.degree_nodal Lagrange.degree_nodal

/- warning: lagrange.eval_nodal -> Lagrange.eval_nodal is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {x : F}, Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) x (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (Finset.prod.{u1, u2} F ι (CommRing.toCommMonoid.{u1} F (EuclideanDomain.toCommRing.{u1} F (Field.toEuclideanDomain.{u1} F _inst_1))) s (fun (i : ι) => HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddGroupWithOne.toAddGroup.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))) x (v i)))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} {s : Finset.{u1} ι} {v : ι -> F} {x : F}, Eq.{succ u2} F (Polynomial.eval.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))) x (Lagrange.nodal.{u2, u1} F _inst_1 ι s v)) (Finset.prod.{u2, u1} F ι (CommRing.toCommMonoid.{u2} F (EuclideanDomain.toCommRing.{u2} F (Field.toEuclideanDomain.{u2} F _inst_1))) s (fun (i : ι) => HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (Ring.toSub.{u2} F (DivisionRing.toRing.{u2} F (Field.toDivisionRing.{u2} F _inst_1)))) x (v i)))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_nodal Lagrange.eval_nodalₓ'. -/
theorem eval_nodal {x : F} : (nodal s v).eval x = ∏ i in s, x - v i := by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]
#align lagrange.eval_nodal Lagrange.eval_nodal

/- warning: lagrange.eval_nodal_at_node -> Lagrange.eval_nodal_at_node is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι}, (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (v i) (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι}, (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) (v i) (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_nodal_at_node Lagrange.eval_nodal_at_nodeₓ'. -/
theorem eval_nodal_at_node (hi : i ∈ s) : eval (v i) (nodal s v) = 0 := by
  rw [eval_nodal, prod_eq_zero_iff]; exact ⟨i, hi, sub_eq_zero_of_eq rfl⟩
#align lagrange.eval_nodal_at_node Lagrange.eval_nodal_at_node

/- warning: lagrange.eval_nodal_not_at_node -> Lagrange.eval_nodal_not_at_node is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {x : F}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Ne.{succ u1} F x (v i))) -> (Ne.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) x (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {x : F}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Ne.{succ u1} F x (v i))) -> (Ne.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) x (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_nodal_not_at_node Lagrange.eval_nodal_not_at_nodeₓ'. -/
theorem eval_nodal_not_at_node (hx : ∀ i ∈ s, x ≠ v i) : eval x (nodal s v) ≠ 0 := by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]; exact hx
#align lagrange.eval_nodal_not_at_node Lagrange.eval_nodal_not_at_node

/- warning: lagrange.nodal_eq_mul_nodal_erase -> Lagrange.nodal_eq_mul_nodal_erase is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_eq_mul_nodal_erase Lagrange.nodal_eq_mul_nodal_eraseₓ'. -/
theorem nodal_eq_mul_nodal_erase [DecidableEq ι] (hi : i ∈ s) :
    nodal s v = (X - C (v i)) * nodal (s.eraseₓ i) v := by simp_rw [nodal, mul_prod_erase _ _ hi]
#align lagrange.nodal_eq_mul_nodal_erase Lagrange.nodal_eq_mul_nodal_erase

/- warning: lagrange.X_sub_C_dvd_nodal -> Lagrange.X_sub_C_dvd_nodal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.X_sub_C_dvd_nodal Lagrange.X_sub_C_dvd_nodalₓ'. -/
theorem X_sub_C_dvd_nodal (v : ι → F) (hi : i ∈ s) : X - C (v i) ∣ nodal s v :=
  ⟨_, by classical exact nodal_eq_mul_nodal_erase hi⟩
#align lagrange.X_sub_C_dvd_nodal Lagrange.X_sub_C_dvd_nodal

variable [DecidableEq ι]

/- warning: lagrange.nodal_erase_eq_nodal_div -> Lagrange.nodal_erase_eq_nodal_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_erase_eq_nodal_div Lagrange.nodal_erase_eq_nodal_divₓ'. -/
theorem nodal_erase_eq_nodal_div (hi : i ∈ s) : nodal (s.eraseₓ i) v = nodal s v / (X - C (v i)) :=
  by
  rw [nodal_eq_mul_nodal_erase hi, EuclideanDomain.mul_div_cancel_left]
  exact X_sub_C_ne_zero _
#align lagrange.nodal_erase_eq_nodal_div Lagrange.nodal_erase_eq_nodal_div

/- warning: lagrange.nodal_insert_eq_nodal -> Lagrange.nodal_insert_eq_nodal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_insert_eq_nodal Lagrange.nodal_insert_eq_nodalₓ'. -/
theorem nodal_insert_eq_nodal (hi : i ∉ s) : nodal (insert i s) v = (X - C (v i)) * nodal s v := by
  simp_rw [nodal, prod_insert hi]
#align lagrange.nodal_insert_eq_nodal Lagrange.nodal_insert_eq_nodal

/- warning: lagrange.derivative_nodal -> Lagrange.derivative_nodal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.derivative_nodal Lagrange.derivative_nodalₓ'. -/
theorem derivative_nodal : (nodal s v).derivative = ∑ i in s, nodal (s.eraseₓ i) v :=
  by
  refine' Finset.induction_on s _ fun _ _ hit IH => _
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine' sum_congr rfl fun j hjt => _
    rw [nodal_erase_eq_nodal_div (mem_insert_of_mem hjt), nodal_insert_eq_nodal hit,
      EuclideanDomain.mul_div_assoc _ (X_sub_C_dvd_nodal v hjt), nodal_erase_eq_nodal_div hjt]
#align lagrange.derivative_nodal Lagrange.derivative_nodal

/- warning: lagrange.eval_nodal_derivative_eval_node_eq -> Lagrange.eval_nodal_derivative_eval_node_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eval_nodal_derivative_eval_node_eq Lagrange.eval_nodal_derivative_eval_node_eqₓ'. -/
theorem eval_nodal_derivative_eval_node_eq (hi : i ∈ s) :
    eval (v i) (nodal s v).derivative = eval (v i) (nodal (s.eraseₓ i) v) :=
  by
  rw [derivative_nodal, eval_finset_sum, ← add_sum_erase _ _ hi, add_right_eq_self]
  refine' sum_eq_zero fun j hj => _
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C, prod_eq_zero_iff, mem_erase]
  exact ⟨i, ⟨(mem_erase.mp hj).1.symm, hi⟩, sub_eq_zero_of_eq rfl⟩
#align lagrange.eval_nodal_derivative_eval_node_eq Lagrange.eval_nodal_derivative_eval_node_eq

#print Lagrange.nodalWeight /-
/-- This defines the nodal weight for a given set of node indexes and node mapping function `v`. -/
def nodalWeight (s : Finset ι) (v : ι → F) (i : ι) :=
  ∏ j in s.eraseₓ i, (v i - v j)⁻¹
#align lagrange.nodal_weight Lagrange.nodalWeight
-/

/- warning: lagrange.nodal_weight_eq_eval_nodal_erase_inv -> Lagrange.nodalWeight_eq_eval_nodal_erase_inv is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι} [_inst_2 : DecidableEq.{succ u2} ι], Eq.{succ u1} F (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u1} F (DivInvMonoid.toHasInv.{u1} F (DivisionRing.toDivInvMonoid.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (v i) (Lagrange.nodal.{u1, u2} F _inst_1 ι (Finset.erase.{u2} ι (fun (a : ι) (b : ι) => _inst_2 a b) s i) v)))
but is expected to have type
  forall {F : Type.{u2}} [_inst_1 : Field.{u2} F] {ι : Type.{u1}} {s : Finset.{u1} ι} {v : ι -> F} {i : ι} [_inst_2 : DecidableEq.{succ u1} ι], Eq.{succ u2} F (Lagrange.nodalWeight.{u2, u1} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u2} F (Field.toInv.{u2} F _inst_1) (Polynomial.eval.{u2} F (DivisionSemiring.toSemiring.{u2} F (Semifield.toDivisionSemiring.{u2} F (Field.toSemifield.{u2} F _inst_1))) (v i) (Lagrange.nodal.{u2, u1} F _inst_1 ι (Finset.erase.{u1} ι (fun (a : ι) (b : ι) => _inst_2 a b) s i) v)))
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_weight_eq_eval_nodal_erase_inv Lagrange.nodalWeight_eq_eval_nodal_erase_invₓ'. -/
theorem nodalWeight_eq_eval_nodal_erase_inv :
    nodalWeight s v i = (eval (v i) (nodal (s.eraseₓ i) v))⁻¹ := by
  rw [eval_nodal, nodal_weight, prod_inv_distrib]
#align lagrange.nodal_weight_eq_eval_nodal_erase_inv Lagrange.nodalWeight_eq_eval_nodal_erase_inv

/- warning: lagrange.nodal_weight_eq_eval_nodal_derative -> Lagrange.nodalWeight_eq_eval_nodal_derative is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_weight_eq_eval_nodal_derative Lagrange.nodalWeight_eq_eval_nodal_derativeₓ'. -/
theorem nodalWeight_eq_eval_nodal_derative (hi : i ∈ s) :
    nodalWeight s v i = (eval (v i) (nodal s v).derivative)⁻¹ := by
  rw [eval_nodal_derivative_eval_node_eq hi, nodal_weight_eq_eval_nodal_erase_inv]
#align lagrange.nodal_weight_eq_eval_nodal_derative Lagrange.nodalWeight_eq_eval_nodal_derative

/- warning: lagrange.nodal_weight_ne_zero -> Lagrange.nodalWeight_ne_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι} [_inst_2 : DecidableEq.{succ u2} ι], (Set.InjOn.{u2, u1} ι F v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Ne.{succ u1} F (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι} [_inst_2 : DecidableEq.{succ u2} ι], (Set.InjOn.{u2, u1} ι F v (Finset.toSet.{u2} ι s)) -> (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Ne.{succ u1} F (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.nodal_weight_ne_zero Lagrange.nodalWeight_ne_zeroₓ'. -/
theorem nodalWeight_ne_zero (hvs : Set.InjOn v s) (hi : i ∈ s) : nodalWeight s v i ≠ 0 :=
  by
  rw [nodal_weight, prod_ne_zero_iff]
  intro j hj
  rcases mem_erase.mp hj with ⟨hij, hj⟩
  refine' inv_ne_zero (sub_ne_zero_of_ne (mt (hvs.eq_iff hi hj).mp hij.symm))
#align lagrange.nodal_weight_ne_zero Lagrange.nodalWeight_ne_zero

/- warning: lagrange.basis_eq_prod_sub_inv_mul_nodal_div -> Lagrange.basis_eq_prod_sub_inv_mul_nodal_div is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.basis_eq_prod_sub_inv_mul_nodal_div Lagrange.basis_eq_prod_sub_inv_mul_nodal_divₓ'. -/
theorem basis_eq_prod_sub_inv_mul_nodal_div (hi : i ∈ s) :
    Lagrange.basis s v i = C (nodalWeight s v i) * (nodal s v / (X - C (v i))) := by
  simp_rw [Lagrange.basis, basis_divisor, nodal_weight, prod_mul_distrib, map_prod, ←
    nodal_erase_eq_nodal_div hi, nodal]
#align lagrange.basis_eq_prod_sub_inv_mul_nodal_div Lagrange.basis_eq_prod_sub_inv_mul_nodal_div

/- warning: lagrange.eval_basis_not_at_node -> Lagrange.eval_basis_not_at_node is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι} {x : F} [_inst_2 : DecidableEq.{succ u2} ι], (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Ne.{succ u1} F x (v i)) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) x (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (Distrib.toHasMul.{u1} F (Ring.toDistrib.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))) (Polynomial.eval.{u1} F (Ring.toSemiring.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) x (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (Distrib.toHasMul.{u1} F (Ring.toDistrib.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))) (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u1} F (DivInvMonoid.toHasInv.{u1} F (DivisionRing.toDivInvMonoid.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddGroupWithOne.toAddGroup.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))) x (v i))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {i : ι} {x : F} [_inst_2 : DecidableEq.{succ u2} ι], (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Ne.{succ u1} F x (v i)) -> (Eq.{succ u1} F (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) x (Lagrange.basis.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i)) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (NonUnitalNonAssocRing.toMul.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))) (Polynomial.eval.{u1} F (DivisionSemiring.toSemiring.{u1} F (Semifield.toDivisionSemiring.{u1} F (Field.toSemifield.{u1} F _inst_1))) x (Lagrange.nodal.{u1, u2} F _inst_1 ι s v)) (HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (NonUnitalNonAssocRing.toMul.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))) (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u1} F (Field.toInv.{u1} F _inst_1) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (Ring.toSub.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) x (v i))))))
Case conversion may be inaccurate. Consider using '#align lagrange.eval_basis_not_at_node Lagrange.eval_basis_not_at_nodeₓ'. -/
theorem eval_basis_not_at_node (hi : i ∈ s) (hxi : x ≠ v i) :
    eval x (Lagrange.basis s v i) = eval x (nodal s v) * (nodalWeight s v i * (x - v i)⁻¹) := by
  rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hi, eval_mul, eval_C, ←
    nodal_erase_eq_nodal_div hi, eval_nodal, eval_nodal, mul_assoc, ← mul_prod_erase _ _ hi, ←
    mul_assoc (x - v i)⁻¹, inv_mul_cancel (sub_ne_zero_of_ne hxi), one_mul]
#align lagrange.eval_basis_not_at_node Lagrange.eval_basis_not_at_node

/- warning: lagrange.interpolate_eq_nodal_weight_mul_nodal_div_X_sub_C -> Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.interpolate_eq_nodal_weight_mul_nodal_div_X_sub_C Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_Cₓ'. -/
theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C :
    interpolate s v r = ∑ i in s, C (nodalWeight s v i) * (nodal s v / (X - C (v i))) * C (r i) :=
  sum_congr rfl fun j hj => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hj]
#align lagrange.interpolate_eq_nodal_weight_mul_nodal_div_X_sub_C Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C

/- warning: lagrange.eval_interpolate_not_at_node -> Lagrange.eval_interpolate_not_at_node is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eval_interpolate_not_at_node Lagrange.eval_interpolate_not_at_nodeₓ'. -/
/-- This is the first barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      eval x (nodal s v) * ∑ i in s, nodalWeight s v i * (x - v i)⁻¹ * r i :=
  by
  simp_rw [interpolate_apply, mul_sum, eval_finset_sum, eval_mul, eval_C]
  refine' sum_congr rfl fun i hi => _
  rw [← mul_assoc, mul_comm, eval_basis_not_at_node hi (hx _ hi)]
#align lagrange.eval_interpolate_not_at_node Lagrange.eval_interpolate_not_at_node

/- warning: lagrange.sum_nodal_weight_mul_inv_sub_ne_zero -> Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {x : F} [_inst_2 : DecidableEq.{succ u2} ι], (Set.InjOn.{u2, u1} ι F v ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} ι) (Set.{u2} ι) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} ι) (Set.{u2} ι) (Finset.Set.hasCoeT.{u2} ι))) s)) -> (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i s) -> (Ne.{succ u1} F x (v i))) -> (Finset.Nonempty.{u2} ι s) -> (Ne.{succ u1} F (Finset.sum.{u1, u2} F ι (AddCommGroup.toAddCommMonoid.{u1} F (NonUnitalNonAssocRing.toAddCommGroup.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (Distrib.toHasMul.{u1} F (Ring.toDistrib.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1))))) (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u1} F (DivInvMonoid.toHasInv.{u1} F (DivisionRing.toDivInvMonoid.{u1} F (Field.toDivisionRing.{u1} F _inst_1))) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddGroupWithOne.toAddGroup.{u1} F (AddCommGroupWithOne.toAddGroupWithOne.{u1} F (Ring.toAddCommGroupWithOne.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))) x (v i))))) (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (MulZeroClass.toHasZero.{u1} F (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_1 : Field.{u1} F] {ι : Type.{u2}} {s : Finset.{u2} ι} {v : ι -> F} {x : F} [_inst_2 : DecidableEq.{succ u2} ι], (Set.InjOn.{u2, u1} ι F v (Finset.toSet.{u2} ι s)) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Finset.{u2} ι) (Finset.instMembershipFinset.{u2} ι) i s) -> (Ne.{succ u1} F x (v i))) -> (Finset.Nonempty.{u2} ι s) -> (Ne.{succ u1} F (Finset.sum.{u1, u2} F ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} F (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))) s (fun (i : ι) => HMul.hMul.{u1, u1, u1} F F F (instHMul.{u1} F (NonUnitalNonAssocRing.toMul.{u1} F (NonAssocRing.toNonUnitalNonAssocRing.{u1} F (Ring.toNonAssocRing.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))))) (Lagrange.nodalWeight.{u1, u2} F _inst_1 ι (fun (a : ι) (b : ι) => _inst_2 a b) s v i) (Inv.inv.{u1} F (Field.toInv.{u1} F _inst_1) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (Ring.toSub.{u1} F (DivisionRing.toRing.{u1} F (Field.toDivisionRing.{u1} F _inst_1)))) x (v i))))) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (CommMonoidWithZero.toZero.{u1} F (CommGroupWithZero.toCommMonoidWithZero.{u1} F (Semifield.toCommGroupWithZero.{u1} F (Field.toSemifield.{u1} F _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align lagrange.sum_nodal_weight_mul_inv_sub_ne_zero Lagrange.sum_nodalWeight_mul_inv_sub_ne_zeroₓ'. -/
theorem sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : ∀ i ∈ s, x ≠ v i)
    (hs : s.Nonempty) : (∑ i in s, nodalWeight s v i * (x - v i)⁻¹) ≠ 0 :=
  @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ <| by
    simpa only [Pi.one_apply, interpolate_one hvs hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node 1 hx).symm
#align lagrange.sum_nodal_weight_mul_inv_sub_ne_zero Lagrange.sum_nodalWeight_mul_inv_sub_ne_zero

/- warning: lagrange.eval_interpolate_not_at_node' -> Lagrange.eval_interpolate_not_at_node' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align lagrange.eval_interpolate_not_at_node' Lagrange.eval_interpolate_not_at_node'ₓ'. -/
/-- This is the second barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node' (hvs : Set.InjOn v s) (hs : s.Nonempty)
    (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v r) =
      (∑ i in s, nodalWeight s v i * (x - v i)⁻¹ * r i) /
        ∑ i in s, nodalWeight s v i * (x - v i)⁻¹ :=
  by
  rw [← div_one (eval x (interpolate s v r)), ← @eval_one _ _ x, ← interpolate_one hvs hs,
    eval_interpolate_not_at_node r hx, eval_interpolate_not_at_node 1 hx]
  simp only [mul_div_mul_left _ _ (eval_nodal_not_at_node hx), Pi.one_apply, mul_one]
#align lagrange.eval_interpolate_not_at_node' Lagrange.eval_interpolate_not_at_node'

end Nodal

end Lagrange

