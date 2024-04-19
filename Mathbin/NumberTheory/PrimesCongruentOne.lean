/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import RingTheory.Polynomial.Cyclotomic.Eval

#align_import number_theory.primes_congruent_one from "leanprover-community/mathlib"@"2a0ce625dbb0ffbc7d1316597de0b25c1ec75303"

/-!
# Primes congruent to one

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/


namespace Nat

open Polynomial Nat Filter

open scoped Nat

#print Nat.exists_prime_gt_modEq_one /-
/-- For any positive `k : ℕ` there exists an arbitrarily large prime `p` such that
`p ≡ 1 [MOD k]`. -/
theorem exists_prime_gt_modEq_one {k : ℕ} (n : ℕ) (hk0 : k ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k] :=
  by
  rcases(one_le_iff_ne_zero.2 hk0).eq_or_lt with (rfl | hk1)
  · rcases exists_infinite_primes (n + 1) with ⟨p, hnp, hp⟩
    exact ⟨p, hp, hnp, modeq_one⟩
  let b := k * n !
  have hgt : 1 < (eval (↑b) (cyclotomic k ℤ)).natAbs :=
    by
    rcases le_iff_exists_add'.1 hk1.le with ⟨k, rfl⟩
    have hb : 2 ≤ b := le_mul_of_le_of_one_le hk1 n.factorial_pos
    calc
      1 ≤ b - 1 := le_tsub_of_add_le_left hb
      _ < (eval (b : ℤ) (cyclotomic (k + 1) ℤ)).natAbs :=
        sub_one_lt_nat_abs_cyclotomic_eval hk1 (succ_le_iff.1 hb).ne'
  let p := min_fac (eval (↑b) (cyclotomic k ℤ)).natAbs
  haveI hprime : Fact p.prime := ⟨min_fac_prime (ne_of_lt hgt).symm⟩
  have hroot : is_root (cyclotomic k (ZMod p)) (cast_ring_hom (ZMod p) b) :=
    by
    rw [is_root.def, ← map_cyclotomic_int k (ZMod p), eval_map, coe_cast_ring_hom, ←
      Int.cast_natCast, ← Int.coe_castRingHom, eval₂_hom, Int.coe_castRingHom,
      ZMod.intCast_zmod_eq_zero_iff_dvd _ _]
    apply Int.dvd_natAbs.1
    exact_mod_cast min_fac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hpb : ¬p ∣ b :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hk0.bot_lt hroot).symm
  refine' ⟨p, hprime.1, not_le.1 fun habs => _, _⟩
  · exact hpb (dvd_mul_of_dvd_right (dvd_factorial (min_fac_pos _) habs) _)
  · have hdiv : orderOf (b : ZMod p) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hpb)
    haveI : NeZero (k : ZMod p) :=
      NeZero.of_not_dvd (ZMod p) fun hpk => hpb (dvd_mul_of_dvd_left hpk _)
    have : k = orderOf (b : ZMod p) := (is_root_cyclotomic_iff.mp hroot).eq_orderOf
    rw [← this] at hdiv
    exact ((modeq_iff_dvd' hprime.1.Pos).2 hdiv).symm
#align nat.exists_prime_gt_modeq_one Nat.exists_prime_gt_modEq_one
-/

#print Nat.frequently_atTop_modEq_one /-
theorem frequently_atTop_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    ∃ᶠ p in atTop, Nat.Prime p ∧ p ≡ 1 [MOD k] :=
  by
  refine' frequently_at_top.2 fun n => _
  obtain ⟨p, hp⟩ := exists_prime_gt_modeq_one n hk0
  exact ⟨p, ⟨hp.2.1.le, hp.1, hp.2.2⟩⟩
#align nat.frequently_at_top_modeq_one Nat.frequently_atTop_modEq_one
-/

#print Nat.infinite_setOf_prime_modEq_one /-
/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
theorem infinite_setOf_prime_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_modEq_one hk0)
#align nat.infinite_set_of_prime_modeq_one Nat.infinite_setOf_prime_modEq_one
-/

end Nat

