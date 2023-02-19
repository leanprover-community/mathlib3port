/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module algebra.big_operators.nat_antidiagonal
! leanprover-community/mathlib commit e97cf15cd1aec9bd5c193b2ffac5a6dc9118912b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.NatAntidiagonal
import Mathbin.Algebra.BigOperators.Basic

/-!
# Big operators for `nat_antidiagonal`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains theorems relevant to big operators over `finset.nat.antidiagonal`.
-/


open BigOperators

variable {M N : Type _} [CommMonoid M] [AddCommMonoid N]

namespace Finset

namespace Nat

/- warning: finset.nat.prod_antidiagonal_succ -> Finset.Nat.prod_antidiagonal_succ is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f (Prod.mk.{0, 0} Nat Nat (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Prod.fst.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Prod.snd.{0, 0} Nat Nat p)))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f (Prod.mk.{0, 0} Nat Nat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Prod.fst.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Prod.snd.{0, 0} Nat Nat p)))))
Case conversion may be inaccurate. Consider using '#align finset.nat.prod_antidiagonal_succ Finset.Nat.prod_antidiagonal_succₓ'. -/
theorem prod_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal (n + 1), f p) = f (0, n + 1) * ∏ p in antidiagonal n, f (p.1 + 1, p.2) :=
  by rw [antidiagonal_succ, prod_cons, Prod_map]; rfl
#align finset.nat.prod_antidiagonal_succ Finset.Nat.prod_antidiagonal_succ

/- warning: finset.nat.sum_antidiagonal_succ -> Finset.Nat.sum_antidiagonal_succ is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} N] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> N}, Eq.{succ u1} N (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HAdd.hAdd.{u1, u1, u1} N N N (instHAdd.{u1} N (AddZeroClass.toHasAdd.{u1} N (AddMonoid.toAddZeroClass.{u1} N (AddCommMonoid.toAddMonoid.{u1} N _inst_2)))) (f (Prod.mk.{0, 0} Nat Nat (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Prod.fst.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Prod.snd.{0, 0} Nat Nat p)))))
but is expected to have type
  forall {N : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} N] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> N}, Eq.{succ u1} N (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HAdd.hAdd.{u1, u1, u1} N N N (instHAdd.{u1} N (AddZeroClass.toAdd.{u1} N (AddMonoid.toAddZeroClass.{u1} N (AddCommMonoid.toAddMonoid.{u1} N _inst_2)))) (f (Prod.mk.{0, 0} Nat Nat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Prod.fst.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Prod.snd.{0, 0} Nat Nat p)))))
Case conversion may be inaccurate. Consider using '#align finset.nat.sum_antidiagonal_succ Finset.Nat.sum_antidiagonal_succₓ'. -/
theorem sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p in antidiagonal n, f (p.1 + 1, p.2) :=
  @prod_antidiagonal_succ (Multiplicative N) _ _ _
#align finset.nat.sum_antidiagonal_succ Finset.Nat.sum_antidiagonal_succ

#print Finset.Nat.prod_antidiagonal_swap /-
@[to_additive]
theorem prod_antidiagonal_swap {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal n, f p.symm) = ∏ p in antidiagonal n, f p :=
  by
  nth_rw 2 [← map_swap_antidiagonal]
  rw [Prod_map]
  rfl
#align finset.nat.prod_antidiagonal_swap Finset.Nat.prod_antidiagonal_swap
#align finset.nat.sum_antidiagonal_swap Finset.Nat.sum_antidiagonal_swap
-/

/- warning: finset.nat.prod_antidiagonal_succ' -> Finset.Nat.prod_antidiagonal_succ' is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (Prod.fst.{0, 0} Nat Nat p) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Prod.snd.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> M}, Eq.{succ u1} M (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)))) (f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Finset.prod.{u1, 0} M (Prod.{0, 0} Nat Nat) _inst_1 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (Prod.fst.{0, 0} Nat Nat p) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Prod.snd.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align finset.nat.prod_antidiagonal_succ' Finset.Nat.prod_antidiagonal_succ'ₓ'. -/
theorem prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} :
    (∏ p in antidiagonal (n + 1), f p) = f (n + 1, 0) * ∏ p in antidiagonal n, f (p.1, p.2 + 1) :=
  by
  rw [← prod_antidiagonal_swap, prod_antidiagonal_succ, ← prod_antidiagonal_swap]
  rfl
#align finset.nat.prod_antidiagonal_succ' Finset.Nat.prod_antidiagonal_succ'

/- warning: finset.nat.sum_antidiagonal_succ' -> Finset.Nat.sum_antidiagonal_succ' is a dubious translation:
lean 3 declaration is
  forall {N : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} N] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> N}, Eq.{succ u1} N (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HAdd.hAdd.{u1, u1, u1} N N N (instHAdd.{u1} N (AddZeroClass.toHasAdd.{u1} N (AddMonoid.toAddZeroClass.{u1} N (AddCommMonoid.toAddMonoid.{u1} N _inst_2)))) (f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (Prod.fst.{0, 0} Nat Nat p) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Prod.snd.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {N : Type.{u1}} [_inst_2 : AddCommMonoid.{u1} N] {n : Nat} {f : (Prod.{0, 0} Nat Nat) -> N}, Eq.{succ u1} N (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (p : Prod.{0, 0} Nat Nat) => f p)) (HAdd.hAdd.{u1, u1, u1} N N N (instHAdd.{u1} N (AddZeroClass.toAdd.{u1} N (AddMonoid.toAddZeroClass.{u1} N (AddCommMonoid.toAddMonoid.{u1} N _inst_2)))) (f (Prod.mk.{0, 0} Nat Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Finset.sum.{u1, 0} N (Prod.{0, 0} Nat Nat) _inst_2 (Finset.Nat.antidiagonal n) (fun (p : Prod.{0, 0} Nat Nat) => f (Prod.mk.{0, 0} Nat Nat (Prod.fst.{0, 0} Nat Nat p) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Prod.snd.{0, 0} Nat Nat p) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align finset.nat.sum_antidiagonal_succ' Finset.Nat.sum_antidiagonal_succ'ₓ'. -/
theorem sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p in antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p in antidiagonal n, f (p.1, p.2 + 1) :=
  @prod_antidiagonal_succ' (Multiplicative N) _ _ _
#align finset.nat.sum_antidiagonal_succ' Finset.Nat.sum_antidiagonal_succ'

#print Finset.Nat.prod_antidiagonal_subst /-
@[to_additive]
theorem prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
    (∏ p in antidiagonal n, f p n) = ∏ p in antidiagonal n, f p (p.1 + p.2) :=
  prod_congr rfl fun p hp => by rw [nat.mem_antidiagonal.1 hp]
#align finset.nat.prod_antidiagonal_subst Finset.Nat.prod_antidiagonal_subst
#align finset.nat.sum_antidiagonal_subst Finset.Nat.sum_antidiagonal_subst
-/

#print Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk /-
@[to_additive]
theorem prod_antidiagonal_eq_prod_range_succ_mk {M : Type _} [CommMonoid M] (f : ℕ × ℕ → M)
    (n : ℕ) : (∏ ij in Finset.Nat.antidiagonal n, f ij) = ∏ k in range n.succ, f (k, n - k) :=
  by
  convert Prod_map _ ⟨fun i => (i, n - i), fun x y h => (Prod.mk.inj h).1⟩ _
  rfl
#align finset.nat.prod_antidiagonal_eq_prod_range_succ_mk Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk
#align finset.nat.sum_antidiagonal_eq_sum_range_succ_mk Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
-/

#print Finset.Nat.prod_antidiagonal_eq_prod_range_succ /-
/-- This lemma matches more generally than `finset.nat.prod_antidiagonal_eq_prod_range_succ_mk` when
using `rw ←`. -/
@[to_additive
      "This lemma matches more generally than\n`finset.nat.sum_antidiagonal_eq_sum_range_succ_mk` when using `rw ←`."]
theorem prod_antidiagonal_eq_prod_range_succ {M : Type _} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ ij in Finset.Nat.antidiagonal n, f ij.1 ij.2) = ∏ k in range n.succ, f k (n - k) :=
  prod_antidiagonal_eq_prod_range_succ_mk _ _
#align finset.nat.prod_antidiagonal_eq_prod_range_succ Finset.Nat.prod_antidiagonal_eq_prod_range_succ
#align finset.nat.sum_antidiagonal_eq_sum_range_succ Finset.Nat.sum_antidiagonal_eq_sum_range_succ
-/

end Nat

end Finset

