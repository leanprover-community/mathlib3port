/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.coprime.lemmas
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Ring
import Mathbin.Data.Fintype.Basic
import Mathbin.Data.Int.Gcd
import Mathbin.RingTheory.Coprime.Basic

/-!
# Additional lemmas about elements of a ring satisfying `is_coprime`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are in a separate file to the definition of `is_coprime` as they require more imports.

Notably, this includes lemmas about `finset.prod` as this requires importing big_operators, and
lemmas about `has_pow` since these are easiest to prove via `finset.prod`.

-/


universe u v

variable {R : Type u} {I : Type v} [CommSemiring R] {x y z : R} {s : I → R} {t : Finset I}

open BigOperators

section

open Classical

/- warning: nat.is_coprime_iff_coprime -> Nat.isCoprime_iff_coprime is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, Iff (IsCoprime.{0} Int Int.commSemiring ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) (Nat.coprime m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, Iff (IsCoprime.{0} Int Int.instCommSemiringInt (Nat.cast.{0} Int Int.instNatCastInt m) (Nat.cast.{0} Int Int.instNatCastInt n)) (Nat.coprime m n)
Case conversion may be inaccurate. Consider using '#align nat.is_coprime_iff_coprime Nat.isCoprime_iff_coprimeₓ'. -/
theorem Nat.isCoprime_iff_coprime {m n : ℕ} : IsCoprime (m : ℤ) n ↔ Nat.coprime m n :=
  ⟨fun ⟨a, b, H⟩ =>
    Nat.eq_one_of_dvd_one <|
      Int.coe_nat_dvd.1 <| by
        rw [Int.ofNat_one, ← H]
        exact
          dvd_add (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_left m n) _)
            (dvd_mul_of_dvd_right (Int.coe_nat_dvd.2 <| Nat.gcd_dvd_right m n) _),
    fun H =>
    ⟨Nat.gcdA m n, Nat.gcdB m n, by
      rw [mul_comm _ (m : ℤ), mul_comm _ (n : ℤ), ← Nat.gcd_eq_gcd_ab, show _ = _ from H,
        Int.ofNat_one]⟩⟩
#align nat.is_coprime_iff_coprime Nat.isCoprime_iff_coprime

/- warning: is_coprime.nat_coprime -> IsCoprime.nat_coprime is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, (IsCoprime.{0} Int Int.commSemiring ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n)) -> (Nat.coprime m n)
but is expected to have type
  forall {m : Nat} {n : Nat}, (IsCoprime.{0} Int Int.instCommSemiringInt (Nat.cast.{0} Int Int.instNatCastInt m) (Nat.cast.{0} Int Int.instNatCastInt n)) -> (Nat.coprime m n)
Case conversion may be inaccurate. Consider using '#align is_coprime.nat_coprime IsCoprime.nat_coprimeₓ'. -/
/- warning: nat.coprime.is_coprime -> Nat.coprime.isCoprime is a dubious translation:
lean 3 declaration is
  forall {m : Nat} {n : Nat}, (Nat.coprime m n) -> (IsCoprime.{0} Int Int.commSemiring ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) m) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Int (HasLiftT.mk.{1, 1} Nat Int (CoeTCₓ.coe.{1, 1} Nat Int (coeBase.{1, 1} Nat Int Int.hasCoe))) n))
but is expected to have type
  forall {m : Nat} {n : Nat}, (Nat.coprime m n) -> (IsCoprime.{0} Int Int.instCommSemiringInt (Nat.cast.{0} Int Int.instNatCastInt m) (Nat.cast.{0} Int Int.instNatCastInt n))
Case conversion may be inaccurate. Consider using '#align nat.coprime.is_coprime Nat.coprime.isCoprimeₓ'. -/
alias Nat.isCoprime_iff_coprime ↔ IsCoprime.nat_coprime Nat.coprime.isCoprime
#align is_coprime.nat_coprime IsCoprime.nat_coprime
#align nat.coprime.is_coprime Nat.coprime.isCoprime

#print IsCoprime.prod_left /-
theorem IsCoprime.prod_left : (∀ i ∈ t, IsCoprime (s i) x) → IsCoprime (∏ i in t, s i) x :=
  Finset.induction_on t (fun _ => isCoprime_one_left) fun b t hbt ih H =>
    by
    rw [Finset.prod_insert hbt]
    rw [Finset.forall_mem_insert] at H
    exact H.1.mul_left (ih H.2)
#align is_coprime.prod_left IsCoprime.prod_left
-/

#print IsCoprime.prod_right /-
theorem IsCoprime.prod_right : (∀ i ∈ t, IsCoprime x (s i)) → IsCoprime x (∏ i in t, s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left
#align is_coprime.prod_right IsCoprime.prod_right
-/

#print IsCoprime.prod_left_iff /-
theorem IsCoprime.prod_left_iff : IsCoprime (∏ i in t, s i) x ↔ ∀ i ∈ t, IsCoprime (s i) x :=
  Finset.induction_on t (iff_of_true isCoprime_one_left fun _ => False.elim) fun b t hbt ih => by
    rw [Finset.prod_insert hbt, IsCoprime.mul_left_iff, ih, Finset.forall_mem_insert]
#align is_coprime.prod_left_iff IsCoprime.prod_left_iff
-/

#print IsCoprime.prod_right_iff /-
theorem IsCoprime.prod_right_iff : IsCoprime x (∏ i in t, s i) ↔ ∀ i ∈ t, IsCoprime x (s i) := by
  simpa only [isCoprime_comm] using IsCoprime.prod_left_iff
#align is_coprime.prod_right_iff IsCoprime.prod_right_iff
-/

#print IsCoprime.of_prod_left /-
theorem IsCoprime.of_prod_left (H1 : IsCoprime (∏ i in t, s i) x) (i : I) (hit : i ∈ t) :
    IsCoprime (s i) x :=
  IsCoprime.prod_left_iff.1 H1 i hit
#align is_coprime.of_prod_left IsCoprime.of_prod_left
-/

#print IsCoprime.of_prod_right /-
theorem IsCoprime.of_prod_right (H1 : IsCoprime x (∏ i in t, s i)) (i : I) (hit : i ∈ t) :
    IsCoprime x (s i) :=
  IsCoprime.prod_right_iff.1 H1 i hit
#align is_coprime.of_prod_right IsCoprime.of_prod_right
-/

#print Finset.prod_dvd_of_coprime /-
theorem Finset.prod_dvd_of_coprime :
    ∀ (Hs : (t : Set I).Pairwise (IsCoprime on s)) (Hs1 : ∀ i ∈ t, s i ∣ z), (∏ x in t, s x) ∣ z :=
  Finset.induction_on t (fun _ _ => one_dvd z)
    (by
      intro a r har ih Hs Hs1
      rw [Finset.prod_insert har]
      have aux1 : a ∈ (↑(insert a r) : Set I) := Finset.mem_insert_self a r
      refine'
        (IsCoprime.prod_right fun i hir =>
              Hs aux1 (Finset.mem_insert_of_mem hir) <|
                by
                rintro rfl
                exact har hir).mul_dvd
          (Hs1 a aux1) (ih (Hs.mono _) fun i hi => Hs1 i <| Finset.mem_insert_of_mem hi)
      simp only [Finset.coe_insert, Set.subset_insert])
#align finset.prod_dvd_of_coprime Finset.prod_dvd_of_coprime
-/

#print Fintype.prod_dvd_of_coprime /-
theorem Fintype.prod_dvd_of_coprime [Fintype I] (Hs : Pairwise (IsCoprime on s))
    (Hs1 : ∀ i, s i ∣ z) : (∏ x, s x) ∣ z :=
  Finset.prod_dvd_of_coprime (Hs.set_pairwise _) fun i _ => Hs1 i
#align fintype.prod_dvd_of_coprime Fintype.prod_dvd_of_coprime
-/

end

open Finset

/- warning: exists_sum_eq_one_iff_pairwise_coprime -> exists_sum_eq_one_iff_pairwise_coprime is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {I : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {s : I -> R} {t : Finset.{u2} I} [_inst_2 : DecidableEq.{succ u2} I], (Finset.Nonempty.{u2} I t) -> (Iff (Exists.{max (succ u2) (succ u1)} (I -> R) (fun (μ : I -> R) => Eq.{succ u1} R (Finset.sum.{u1, u2} R I (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) t (fun (i : I) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (μ i) (Finset.prod.{u1, u2} R I (CommSemiring.toCommMonoid.{u1} R _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} I) (Finset.hasSdiff.{u2} I (fun (a : I) (b : I) => _inst_2 a b)) t (Singleton.singleton.{u2, u2} I (Finset.{u2} I) (Finset.hasSingleton.{u2} I) i)) (fun (j : I) => s j)))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) (Pairwise.{u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) (Function.onFun.{succ u2, succ u1, 1} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) R Prop (IsCoprime.{u1} R _inst_1) (fun (i : coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) => s ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) I (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) I (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) I (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} I) Type.{u2} (Finset.hasCoeToSort.{u2} I) t) I (coeSubtype.{succ u2} I (fun (x : I) => Membership.Mem.{u2, u2} I (Finset.{u2} I) (Finset.hasMem.{u2} I) x t))))) i)))))
but is expected to have type
  forall {R : Type.{u1}} {I : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {s : I -> R} {t : Finset.{u2} I} [_inst_2 : DecidableEq.{succ u2} I], (Finset.Nonempty.{u2} I t) -> (Iff (Exists.{max (succ u1) (succ u2)} (I -> R) (fun (μ : I -> R) => Eq.{succ u1} R (Finset.sum.{u1, u2} R I (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) t (fun (i : I) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (μ i) (Finset.prod.{u1, u2} R I (CommSemiring.toCommMonoid.{u1} R _inst_1) (SDiff.sdiff.{u2} (Finset.{u2} I) (Finset.instSDiffFinset.{u2} I (fun (a : I) (b : I) => _inst_2 a b)) t (Singleton.singleton.{u2, u2} I (Finset.{u2} I) (Finset.instSingletonFinset.{u2} I) i)) (fun (j : I) => s j)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (Pairwise.{u2} (Subtype.{succ u2} I (fun (x : I) => Membership.mem.{u2, u2} I (Finset.{u2} I) (Finset.instMembershipFinset.{u2} I) x t)) (Function.onFun.{succ u2, succ u1, 1} (Subtype.{succ u2} I (fun (x : I) => Membership.mem.{u2, u2} I (Finset.{u2} I) (Finset.instMembershipFinset.{u2} I) x t)) R Prop (IsCoprime.{u1} R _inst_1) (fun (i : Subtype.{succ u2} I (fun (x : I) => Membership.mem.{u2, u2} I (Finset.{u2} I) (Finset.instMembershipFinset.{u2} I) x t)) => s (Subtype.val.{succ u2} I (fun (x : I) => Membership.mem.{u2, u2} I (Finset.{u2} I) (Finset.instMembershipFinset.{u2} I) x t) i)))))
Case conversion may be inaccurate. Consider using '#align exists_sum_eq_one_iff_pairwise_coprime exists_sum_eq_one_iff_pairwise_coprimeₓ'. -/
theorem exists_sum_eq_one_iff_pairwise_coprime [DecidableEq I] (h : t.Nonempty) :
    (∃ μ : I → R, (∑ i in t, μ i * ∏ j in t \ {i}, s j) = 1) ↔
      Pairwise (IsCoprime on fun i : t => s i) :=
  by
  refine' h.cons_induction _ _ <;> clear t h
  · simp only [Pairwise, sum_singleton, Finset.sdiff_self, prod_empty, mul_one,
      exists_apply_eq_apply, Ne.def, true_iff_iff]
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h
    rw [Finset.mem_singleton] at hi hj
    simpa [hi, hj] using h
  intro a t hat h ih
  rw [pairwise_cons']
  have mem : ∀ x ∈ t, a ∈ insert a t \ {x} := fun x hx =>
    by
    rw [mem_sdiff, mem_singleton]
    exact ⟨mem_insert_self _ _, fun ha => hat (ha.symm.cases_on hx)⟩
  constructor
  · rintro ⟨μ, hμ⟩
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat] at hμ
    refine' ⟨ih.mp ⟨Pi.single h.some (μ a * s h.some) + μ * fun _ => s a, _⟩, fun b hb => _⟩
    · rw [prod_eq_mul_prod_diff_singleton h.some_spec, ← mul_assoc, ←
        @if_pos _ _ h.some_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ
      rw [← hμ, sum_congr rfl]
      intro x hx
      convert @add_mul R _ _ _ _ _ _ using 2
      · by_cases hx : x = h.some
        · rw [hx, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hx, zero_mul]
      · convert (mul_assoc _ _ _).symm
        convert prod_eq_mul_prod_diff_singleton (mem x hx) _ using 3
        convert sdiff_sdiff_comm
        rw [sdiff_singleton_eq_erase, erase_insert hat]
    · have : IsCoprime (s b) (s a) :=
        ⟨μ a * ∏ i in t \ {b}, s i, ∑ i in t, μ i * ∏ j in t \ {i}, s j, _⟩
      · exact ⟨this.symm, this⟩
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl]
      intro x hx
      convert mul_assoc _ _ _
      convert prod_eq_prod_diff_singleton_mul (mem x hx) _ using 3
      convert sdiff_sdiff_comm
      rw [sdiff_singleton_eq_erase, erase_insert hat]
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    obtain ⟨u, v, huv⟩ := IsCoprime.prod_left fun b hb => (Hb b hb).right
    use fun i => if i = a then u else v * μ i
    have hμ' : (∑ i in t, v * ((μ i * ∏ j in t \ {i}, s j) * s a)) = v * s a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul]
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert hat, if_pos rfl, ← huv, ←
      hμ', sum_congr rfl]
    intro x hx
    rw [mul_assoc, if_neg fun ha : x = a => hat (ha.casesOn hx)]
    convert mul_assoc _ _ _
    convert (prod_eq_prod_diff_singleton_mul (mem x hx) _).symm using 3
    convert sdiff_sdiff_comm
    rw [sdiff_singleton_eq_erase, erase_insert hat]
#align exists_sum_eq_one_iff_pairwise_coprime exists_sum_eq_one_iff_pairwise_coprime

/- warning: exists_sum_eq_one_iff_pairwise_coprime' -> exists_sum_eq_one_iff_pairwise_coprime' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {I : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {s : I -> R} [_inst_2 : Fintype.{u2} I] [_inst_3 : Nonempty.{succ u2} I] [_inst_4 : DecidableEq.{succ u2} I], Iff (Exists.{max (succ u2) (succ u1)} (I -> R) (fun (μ : I -> R) => Eq.{succ u1} R (Finset.sum.{u1, u2} R I (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.univ.{u2} I _inst_2) (fun (i : I) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (μ i) (Finset.prod.{u1, u2} R I (CommSemiring.toCommMonoid.{u1} R _inst_1) (HasCompl.compl.{u2} (Finset.{u2} I) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} I) (Finset.booleanAlgebra.{u2} I _inst_2 (fun (a : I) (b : I) => _inst_4 a b))) (Singleton.singleton.{u2, u2} I (Finset.{u2} I) (Finset.hasSingleton.{u2} I) i)) (fun (j : I) => s j)))) (OfNat.ofNat.{u1} R 1 (OfNat.mk.{u1} R 1 (One.one.{u1} R (AddMonoidWithOne.toOne.{u1} R (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} R (NonAssocSemiring.toAddCommMonoidWithOne.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))))))) (Pairwise.{u2} I (Function.onFun.{succ u2, succ u1, 1} I R Prop (IsCoprime.{u1} R _inst_1) s))
but is expected to have type
  forall {R : Type.{u1}} {I : Type.{u2}} [_inst_1 : CommSemiring.{u1} R] {s : I -> R} [_inst_2 : Fintype.{u2} I] [_inst_3 : Nonempty.{succ u2} I] [_inst_4 : DecidableEq.{succ u2} I], Iff (Exists.{max (succ u1) (succ u2)} (I -> R) (fun (μ : I -> R) => Eq.{succ u1} R (Finset.sum.{u1, u2} R I (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))) (Finset.univ.{u2} I _inst_2) (fun (i : I) => HMul.hMul.{u1, u1, u1} R R R (instHMul.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1))))) (μ i) (Finset.prod.{u1, u2} R I (CommSemiring.toCommMonoid.{u1} R _inst_1) (HasCompl.compl.{u2} (Finset.{u2} I) (BooleanAlgebra.toHasCompl.{u2} (Finset.{u2} I) (Finset.instBooleanAlgebraFinset.{u2} I _inst_2 (fun (a : I) (b : I) => _inst_4 a b))) (Singleton.singleton.{u2, u2} I (Finset.{u2} I) (Finset.instSingletonFinset.{u2} I) i)) (fun (j : I) => s j)))) (OfNat.ofNat.{u1} R 1 (One.toOfNat1.{u1} R (Semiring.toOne.{u1} R (CommSemiring.toSemiring.{u1} R _inst_1)))))) (Pairwise.{u2} I (Function.onFun.{succ u2, succ u1, 1} I R Prop (IsCoprime.{u1} R _inst_1) s))
Case conversion may be inaccurate. Consider using '#align exists_sum_eq_one_iff_pairwise_coprime' exists_sum_eq_one_iff_pairwise_coprime'ₓ'. -/
theorem exists_sum_eq_one_iff_pairwise_coprime' [Fintype I] [Nonempty I] [DecidableEq I] :
    (∃ μ : I → R, (∑ i : I, μ i * ∏ j in {i}ᶜ, s j) = 1) ↔ Pairwise (IsCoprime on s) :=
  by
  convert exists_sum_eq_one_iff_pairwise_coprime Finset.univ_nonempty using 1
  simp only [Function.onFun, pairwise_subtype_iff_pairwise_finset', coe_univ, Set.pairwise_univ]
  assumption
#align exists_sum_eq_one_iff_pairwise_coprime' exists_sum_eq_one_iff_pairwise_coprime'

#print pairwise_coprime_iff_coprime_prod /-
theorem pairwise_coprime_iff_coprime_prod [DecidableEq I] :
    Pairwise (IsCoprime on fun i : t => s i) ↔ ∀ i ∈ t, IsCoprime (s i) (∏ j in t \ {i}, s j) :=
  by
  refine' ⟨fun hp i hi => is_coprime.prod_right_iff.mpr fun j hj => _, fun hp => _⟩
  · rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
    obtain ⟨hj, ji⟩ := hj
    exact @hp ⟨i, hi⟩ ⟨j, hj⟩ fun h => ji (congr_arg coe h).symm
  · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    apply is_coprime.prod_right_iff.mp (hp i hi)
    exact finset.mem_sdiff.mpr ⟨hj, fun f => h <| Subtype.ext (finset.mem_singleton.mp f).symm⟩
#align pairwise_coprime_iff_coprime_prod pairwise_coprime_iff_coprime_prod
-/

variable {m n : ℕ}

#print IsCoprime.pow_left /-
theorem IsCoprime.pow_left (H : IsCoprime x y) : IsCoprime (x ^ m) y :=
  by
  rw [← Finset.card_range m, ← Finset.prod_const]
  exact IsCoprime.prod_left fun _ _ => H
#align is_coprime.pow_left IsCoprime.pow_left
-/

#print IsCoprime.pow_right /-
theorem IsCoprime.pow_right (H : IsCoprime x y) : IsCoprime x (y ^ n) :=
  by
  rw [← Finset.card_range n, ← Finset.prod_const]
  exact IsCoprime.prod_right fun _ _ => H
#align is_coprime.pow_right IsCoprime.pow_right
-/

#print IsCoprime.pow /-
theorem IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y ^ n) :=
  H.pow_leftₓ.pow_right
#align is_coprime.pow IsCoprime.pow
-/

#print IsCoprime.pow_left_iff /-
theorem IsCoprime.pow_left_iff (hm : 0 < m) : IsCoprime (x ^ m) y ↔ IsCoprime x y :=
  by
  refine' ⟨fun h => _, IsCoprime.pow_left⟩
  rw [← Finset.card_range m, ← Finset.prod_const] at h
  exact h.of_prod_left 0 (finset.mem_range.mpr hm)
#align is_coprime.pow_left_iff IsCoprime.pow_left_iff
-/

#print IsCoprime.pow_right_iff /-
theorem IsCoprime.pow_right_iff (hm : 0 < m) : IsCoprime x (y ^ m) ↔ IsCoprime x y :=
  isCoprime_comm.trans <| (IsCoprime.pow_left_iff hm).trans <| isCoprime_comm
#align is_coprime.pow_right_iff IsCoprime.pow_right_iff
-/

#print IsCoprime.pow_iff /-
theorem IsCoprime.pow_iff (hm : 0 < m) (hn : 0 < n) : IsCoprime (x ^ m) (y ^ n) ↔ IsCoprime x y :=
  (IsCoprime.pow_left_iff hm).trans <| IsCoprime.pow_right_iff hn
#align is_coprime.pow_iff IsCoprime.pow_iff
-/

