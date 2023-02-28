/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll

! This file was ported from Lean 3 source module number_theory.pell
! leanprover-community/mathlib commit 35c1956cb727c474aa8863c13ca3abca4c2f885e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Qify
import Mathbin.Data.Zmod.Basic
import Mathbin.NumberTheory.DiophantineApproximation

/-!
# Pell's Equation

We prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `pell.exists_of_not_is_square`.

This is the beginning of a development that aims at providing all of the essential theory
of Pell's Equation for general $d$ (as opposed to the contents of `number_theory.pell_matiyasevic`,
which is specific to the case $d = a^2 - 1$ for some $a > 1$).

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Provide the structure theory of the solution set to Pell's equation
  and furthermore also for `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/


namespace Pell

section Existence

open Set Real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_of_not_isSquare {d : ℤ} (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 :=
  by
  let ξ : ℝ := sqrt d
  have hξ : Irrational ξ :=
    by
    refine' irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| int.cast_nonneg.mpr h₀.le) _ two_pos
    rintro ⟨x, hx⟩
    refine' hd ⟨x, @Int.cast_injective ℝ _ _ d (x * x) _⟩
    rw [← sq_sqrt <| int.cast_nonneg.mpr h₀.le, Int.cast_mul, ← hx, sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : { q : ℚ | |q.1 ^ 2 - d * q.2 ^ 2| < M }.Infinite :=
    by
    refine' infinite.mono (fun q h => _) (infinite_rat_abs_sub_lt_one_div_denom_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : ℝ) / (q.denom : ℝ) = q := by exact_mod_cast q.num_div_denom
    rw [mem_set_of, abs_sub_comm, ← @Int.cast_lt ℝ, ← div_lt_div_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel _ h0.ne', ← div_pow, h1, ←
      sq_sqrt (int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div]
    refine' mul_lt_mul'' (((abs_add ξ q).trans _).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add']
    rw [mem_set_of, abs_sub_comm] at h
    refine' (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans _)
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, { q : ℚ | q.1 ^ 2 - d * q.2 ^ 2 = m }.Infinite :=
    by
    contrapose! hM
    simp only [not_infinite] at hM⊢
    refine' (congr_arg _ (ext fun x => _)).mp (finite.bUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_set_of_eq, mem_Ioo, mem_Union, exists_prop, exists_eq_right']
  have hm₀ : m ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_set_of, sub_eq_zero, mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_pos).mp ⟨d, hq⟩
    rw [ha, mul_pow, mul_right_inj' (pow_pos (int.coe_nat_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  haveI := ne_zero_iff.mpr (int.nat_abs_ne_zero.mpr hm₀)
  let f : ℚ → ZMod m.nat_abs × ZMod m.nat_abs := fun q => (q.1, q.2)
  obtain ⟨q₁, h₁ : q₁.1 ^ 2 - d * q₁.2 ^ 2 = m, q₂, h₂ : q₂.1 ^ 2 - d * q₂.2 ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_maps_to (maps_to_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.1 : ZMod m.nat_abs) = q₂.1, hq2 : (q₁.2 : ZMod m.nat_abs) = q₂.2⟩ :=
    prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.1 * q₂.1 - d * (q₁.2 * q₂.2) :=
    by
    rw [← Int.natAbs_dvd, ← ZMod.int_coe_zMod_eq_zero_iff_dvd]
    push_cast
    rw [hq1, hq2, ← sq, ← sq]
    norm_cast
    rw [ZMod.int_coe_zMod_eq_zero_iff_dvd, Int.natAbs_dvd, Nat.cast_pow, ← h₂]
  have hd₂ : m ∣ q₁.1 * q₂.2 - q₂.1 * q₁.2 :=
    by
    rw [← Int.natAbs_dvd, ← ZMod.int_coe_eq_int_coe_iff_dvd_sub]
    push_cast
    rw [hq1, hq2]
  replace hm₀ : (m : ℚ) ≠ 0 := int.cast_ne_zero.mpr hm₀
  refine' ⟨(q₁.1 * q₂.1 - d * (q₁.2 * q₂.2)) / m, (q₁.1 * q₂.2 - q₂.1 * q₁.2) / m, _, _⟩
  · qify [hd₁, hd₂]
    field_simp [hm₀]
    norm_cast
    conv_rhs =>
      congr
      rw [sq]
      congr
      rw [← h₁]
      skip
      rw [← h₂]
    push_cast
    ring
  · qify [hd₂]
    refine' div_ne_zero_iff.mpr ⟨_, hm₀⟩
    exact_mod_cast mt sub_eq_zero.mp (mt rat.eq_iff_mul_eq_mul.mpr hne)
#align pell.exists_of_not_is_square Pell.exists_of_not_isSquare

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
theorem exists_iff_not_isSquare {d : ℤ} (h₀ : 0 < d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬IsSquare d :=
  by
  refine' ⟨_, exists_of_not_is_square h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy
  simpa [mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy
#align pell.exists_iff_not_is_square Pell.exists_iff_not_isSquare

end Existence

end Pell

