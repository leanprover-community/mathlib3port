/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll

! This file was ported from Lean 3 source module number_theory.pell
! leanprover-community/mathlib commit 842557b6253ace82c125d567a80b5f74f6ce9f99
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Tactic.Qify
import Mathbin.Data.Zmod.Basic
import Mathbin.NumberTheory.DiophantineApproximation
import Mathbin.NumberTheory.Zsqrtd.Basic

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

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `pell.solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*y' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `pell.solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `pell.solution₁ d`.
-/


open Zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `pell.is_pell_iff_mem_unitary`. -/
theorem is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]
#align pell.is_pell_solution_iff_mem_unitary Pell.is_pell_solution_iff_mem_unitary

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.
/-- `pell.solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
def Solution₁ (d : ℤ) : Type :=
  ↥(unitary (ℤ√d))deriving CommGroup, HasDistribNeg, Inhabited
#align pell.solution₁ Pell.Solution₁

namespace Solution₁

variable {d : ℤ}

instance : Coe (Solution₁ d) (ℤ√d) where coe := Subtype.val

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def x (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).re
#align pell.solution₁.x Pell.Solution₁.x

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def y (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).im
#align pell.solution₁.y Pell.Solution₁.y

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property
#align pell.solution₁.prop Pell.Solution₁.prop

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 :=
  by
  rw [← a.prop]
  ring
#align pell.solution₁.prop_x Pell.Solution₁.prop_x

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 :=
  by
  rw [← a.prop]
  ring
#align pell.solution₁.prop_y Pell.Solution₁.prop_y

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
  Subtype.ext <| ext.mpr ⟨hx, hy⟩
#align pell.solution₁.ext Pell.Solution₁.ext

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d
    where
  val := ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop
#align pell.solution₁.mk Pell.Solution₁.mk

@[simp]
theorem x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x :=
  rfl
#align pell.solution₁.x_mk Pell.Solution₁.x_mk

@[simp]
theorem y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y :=
  rfl
#align pell.solution₁.y_mk Pell.Solution₁.y_mk

@[simp]
theorem coe_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x, y⟩ :=
  Zsqrtd.ext.mpr ⟨x_mk x y prop, y_mk x y prop⟩
#align pell.solution₁.coe_mk Pell.Solution₁.coe_mk

@[simp]
theorem x_one : (1 : Solution₁ d).x = 1 :=
  rfl
#align pell.solution₁.x_one Pell.Solution₁.x_one

@[simp]
theorem y_one : (1 : Solution₁ d).y = 0 :=
  rfl
#align pell.solution₁.y_one Pell.Solution₁.y_one

@[simp]
theorem x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) :=
  by
  rw [← mul_assoc]
  rfl
#align pell.solution₁.x_mul Pell.Solution₁.x_mul

@[simp]
theorem y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x :=
  rfl
#align pell.solution₁.y_mul Pell.Solution₁.y_mul

@[simp]
theorem x_inv (a : Solution₁ d) : a⁻¹.x = a.x :=
  rfl
#align pell.solution₁.x_inv Pell.Solution₁.x_inv

@[simp]
theorem y_inv (a : Solution₁ d) : a⁻¹.y = -a.y :=
  rfl
#align pell.solution₁.y_inv Pell.Solution₁.y_inv

@[simp]
theorem x_neg (a : Solution₁ d) : (-a).x = -a.x :=
  rfl
#align pell.solution₁.x_neg Pell.Solution₁.x_neg

@[simp]
theorem y_neg (a : Solution₁ d) : (-a).y = -a.y :=
  rfl
#align pell.solution₁.y_neg Pell.Solution₁.y_neg

end Solution₁

section Existence

/-!
### Existence of nontrivial solutions
-/


variable {d : ℤ}

open Set Real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
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
    rw [← Int.natAbs_dvd, ← ZMod.int_cast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1, hq2, ← sq, ← sq]
    norm_cast
    rw [ZMod.int_cast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd, Nat.cast_pow, ← h₂]
  have hd₂ : m ∣ q₁.1 * q₂.2 - q₂.1 * q₁.2 :=
    by
    rw [← Int.natAbs_dvd, ← ZMod.int_cast_eq_int_cast_iff_dvd_sub]
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
theorem exists_iff_not_isSquare (h₀ : 0 < d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬IsSquare d :=
  by
  refine' ⟨_, exists_of_not_is_square h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy
  simpa [mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy
#align pell.exists_iff_not_is_square Pell.exists_iff_not_isSquare

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
theorem exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ 1 < x ∧ 0 < y :=
  by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_is_square h₀ hd
  refine' ⟨|x|, |y|, by rwa [sq_abs, sq_abs], _, abs_pos.mpr hy⟩
  rw [← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero y hy)
#align pell.exists_pos_of_not_is_square Pell.exists_pos_of_not_isSquare

end Existence

end Pell

