/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.fin
! leanprover-community/mathlib commit cc5dd6244981976cc9da7afc4eee5682b037a013
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.BigOperators
import Mathbin.Data.Fintype.Fin
import Mathbin.Data.List.FinRange
import Mathbin.Logic.Equiv.Fin

/-!
# Big operators and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Some results about products and sums over the type `fin`.

The most important results are the induction formulas `fin.prod_univ_cast_succ`
and `fin.prod_univ_succ`, and the formula `fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

## Main declarations

* `fin_function_fin_equiv`: An explicit equivalence between `fin n → fin m` and `fin (m ^ n)`.
-/


open scoped BigOperators

open Finset

variable {α : Type _} {β : Type _}

namespace Finset

#print Finset.prod_range /-
@[to_additive]
theorem prod_range [CommMonoid β] {n : ℕ} (f : ℕ → β) :
    ∏ i in Finset.range n, f i = ∏ i : Fin n, f i :=
  prod_bij' (fun k w => ⟨k, mem_range.mp w⟩) (fun a ha => mem_univ _)
    (fun a ha => congr_arg _ (Fin.val_mk _).symm) (fun a m => a) (fun a m => mem_range.mpr a.Prop)
    (fun a ha => Fin.val_mk _) fun a ha => Fin.eta _ _
#align finset.prod_range Finset.prod_range
#align finset.sum_range Finset.sum_range
-/

end Finset

namespace Fin

#print Fin.prod_univ_def /-
@[to_additive]
theorem prod_univ_def [CommMonoid β] {n : ℕ} (f : Fin n → β) :
    ∏ i, f i = ((List.finRange n).map f).Prod := by simp [univ_def]
#align fin.prod_univ_def Fin.prod_univ_def
#align fin.sum_univ_def Fin.sum_univ_def
-/

#print Fin.prod_ofFn /-
@[to_additive]
theorem prod_ofFn [CommMonoid β] {n : ℕ} (f : Fin n → β) : (List.ofFn f).Prod = ∏ i, f i := by
  rw [List.ofFn_eq_map, prod_univ_def]
#align fin.prod_of_fn Fin.prod_ofFn
#align fin.sum_of_fn Fin.sum_ofFn
-/

#print Fin.prod_univ_zero /-
/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [CommMonoid β] (f : Fin 0 → β) : ∏ i, f i = 1 :=
  rfl
#align fin.prod_univ_zero Fin.prod_univ_zero
#align fin.sum_univ_zero Fin.sum_univ_zero
-/

#print Fin.prod_univ_succAbove /-
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f x`,\nfor some `x : fin (n + 1)` plus the remaining product"]
theorem prod_univ_succAbove [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i) := by
  rw [univ_succ_above, prod_cons, Finset.prod_map, RelEmbedding.coe_toEmbedding]
#align fin.prod_univ_succ_above Fin.prod_univ_succAbove
#align fin.sum_univ_succ_above Fin.sum_univ_succAbove
-/

#print Fin.prod_univ_succ /-
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of `f 0`\nplus the remaining product"]
theorem prod_univ_succ [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ :=
  prod_univ_succAbove f 0
#align fin.prod_univ_succ Fin.prod_univ_succ
#align fin.sum_univ_succ Fin.sum_univ_succ
-/

#print Fin.prod_univ_castSuccEmb /-
/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
@[to_additive
      "A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)` is the sum of\n`f (fin.last n)` plus the remaining sum"]
theorem prod_univ_castSuccEmb [CommMonoid β] {n : ℕ} (f : Fin (n + 1) → β) :
    ∏ i, f i = (∏ i : Fin n, f i.cast_succ) * f (last n) := by
  simpa [mul_comm] using prod_univ_succ_above f (last n)
#align fin.prod_univ_cast_succ Fin.prod_univ_castSuccEmb
#align fin.sum_univ_cast_succ Fin.sum_univ_castSuccEmb
-/

#print Fin.prod_cons /-
@[to_additive]
theorem prod_cons [CommMonoid β] {n : ℕ} (x : β) (f : Fin n → β) :
    ∏ i : Fin n.succ, (cons x f : Fin n.succ → β) i = x * ∏ i : Fin n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]
#align fin.prod_cons Fin.prod_cons
#align fin.sum_cons Fin.sum_cons
-/

#print Fin.prod_univ_one /-
@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoid β] (f : Fin 1 → β) : ∏ i, f i = f 0 := by simp
#align fin.prod_univ_one Fin.prod_univ_one
#align fin.sum_univ_one Fin.sum_univ_one
-/

#print Fin.prod_univ_two /-
@[simp, to_additive]
theorem prod_univ_two [CommMonoid β] (f : Fin 2 → β) : ∏ i, f i = f 0 * f 1 := by
  simp [prod_univ_succ]
#align fin.prod_univ_two Fin.prod_univ_two
#align fin.sum_univ_two Fin.sum_univ_two
-/

#print Fin.prod_univ_three /-
@[to_additive]
theorem prod_univ_three [CommMonoid β] (f : Fin 3 → β) : ∏ i, f i = f 0 * f 1 * f 2 := by
  rw [prod_univ_cast_succ, prod_univ_two]; rfl
#align fin.prod_univ_three Fin.prod_univ_three
#align fin.sum_univ_three Fin.sum_univ_three
-/

#print Fin.prod_univ_four /-
@[to_additive]
theorem prod_univ_four [CommMonoid β] (f : Fin 4 → β) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 := by
  rw [prod_univ_cast_succ, prod_univ_three]; rfl
#align fin.prod_univ_four Fin.prod_univ_four
#align fin.sum_univ_four Fin.sum_univ_four
-/

#print Fin.prod_univ_five /-
@[to_additive]
theorem prod_univ_five [CommMonoid β] (f : Fin 5 → β) : ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 := by
  rw [prod_univ_cast_succ, prod_univ_four]; rfl
#align fin.prod_univ_five Fin.prod_univ_five
#align fin.sum_univ_five Fin.sum_univ_five
-/

#print Fin.prod_univ_six /-
@[to_additive]
theorem prod_univ_six [CommMonoid β] (f : Fin 6 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 := by rw [prod_univ_cast_succ, prod_univ_five]; rfl
#align fin.prod_univ_six Fin.prod_univ_six
#align fin.sum_univ_six Fin.sum_univ_six
-/

#print Fin.prod_univ_seven /-
@[to_additive]
theorem prod_univ_seven [CommMonoid β] (f : Fin 7 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 := by
  rw [prod_univ_cast_succ, prod_univ_six]; rfl
#align fin.prod_univ_seven Fin.prod_univ_seven
#align fin.sum_univ_seven Fin.sum_univ_seven
-/

#print Fin.prod_univ_eight /-
@[to_additive]
theorem prod_univ_eight [CommMonoid β] (f : Fin 8 → β) :
    ∏ i, f i = f 0 * f 1 * f 2 * f 3 * f 4 * f 5 * f 6 * f 7 := by
  rw [prod_univ_cast_succ, prod_univ_seven]; rfl
#align fin.prod_univ_eight Fin.prod_univ_eight
#align fin.sum_univ_eight Fin.sum_univ_eight
-/

#print Fin.sum_pow_mul_eq_add_pow /-
theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type _} [CommSemiring R] (a b : R) :
    ∑ s : Finset (Fin n), a ^ s.card * b ^ (n - s.card) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Fin n) a b
#align fin.sum_pow_mul_eq_add_pow Fin.sum_pow_mul_eq_add_pow
-/

#print Fin.prod_const /-
theorem prod_const [CommMonoid α] (n : ℕ) (x : α) : ∏ i : Fin n, x = x ^ n := by simp
#align fin.prod_const Fin.prod_const
-/

#print Fin.sum_const /-
theorem sum_const [AddCommMonoid α] (n : ℕ) (x : α) : ∑ i : Fin n, x = n • x := by simp
#align fin.sum_const Fin.sum_const
-/

#print Fin.prod_Ioi_zero /-
@[to_additive]
theorem prod_Ioi_zero {M : Type _} [CommMonoid M] {n : ℕ} {v : Fin n.succ → M} :
    ∏ i in Ioi 0, v i = ∏ j : Fin n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, RelEmbedding.coe_toEmbedding, coe_succ_embedding]
#align fin.prod_Ioi_zero Fin.prod_Ioi_zero
#align fin.sum_Ioi_zero Fin.sum_Ioi_zero
-/

#print Fin.prod_Ioi_succ /-
@[to_additive]
theorem prod_Ioi_succ {M : Type _} [CommMonoid M] {n : ℕ} (i : Fin n) (v : Fin n.succ → M) :
    ∏ j in Ioi i.succ, v j = ∏ j in Ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, RelEmbedding.coe_toEmbedding, coe_succ_embedding]
#align fin.prod_Ioi_succ Fin.prod_Ioi_succ
#align fin.sum_Ioi_succ Fin.sum_Ioi_succ
-/

#print Fin.prod_congr' /-
@[to_additive]
theorem prod_congr' {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin b → M) (h : a = b) :
    ∏ i : Fin a, f (castIso h i) = ∏ i : Fin b, f i := by subst h; congr; ext; congr; ext;
  rw [coe_cast]
#align fin.prod_congr' Fin.prod_congr'
#align fin.sum_congr' Fin.sum_congr'
-/

#print Fin.prod_univ_add /-
@[to_additive]
theorem prod_univ_add {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    ∏ i : Fin (a + b), f i = (∏ i : Fin a, f (castAdd b i)) * ∏ i : Fin b, f (natAdd a i) :=
  by
  rw [Fintype.prod_equiv fin_sum_fin_equiv.symm f fun i => f (fin_sum_fin_equiv.to_fun i)]; swap
  · intro x
    simp only [Equiv.toFun_as_coe, Equiv.apply_symm_apply]
  apply Fintype.prod_sum_type
#align fin.prod_univ_add Fin.prod_univ_add
#align fin.sum_univ_add Fin.sum_univ_add
-/

#print Fin.prod_trunc /-
@[to_additive]
theorem prod_trunc {M : Type _} [CommMonoid M] {a b : ℕ} (f : Fin (a + b) → M)
    (hf : ∀ j : Fin b, f (natAdd a j) = 1) :
    ∏ i : Fin (a + b), f i = ∏ i : Fin a, f (castLE (Nat.le.intro rfl) i) := by
  simpa only [prod_univ_add, Fintype.prod_eq_one _ hf, mul_one]
#align fin.prod_trunc Fin.prod_trunc
#align fin.sum_trunc Fin.sum_trunc
-/

section PartialProd

variable [Monoid α] {n : ℕ}

#print Fin.partialProd /-
/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_prod f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive
      "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_sum f` is\n`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Fin n → α) (i : Fin (n + 1)) : α :=
  ((List.ofFn f).take i).Prod
#align fin.partial_prod Fin.partialProd
#align fin.partial_sum Fin.partialSum
-/

#print Fin.partialProd_zero /-
@[simp, to_additive]
theorem partialProd_zero (f : Fin n → α) : partialProd f 0 = 1 := by simp [partial_prod]
#align fin.partial_prod_zero Fin.partialProd_zero
#align fin.partial_sum_zero Fin.partialSum_zero
-/

#print Fin.partialProd_succ /-
@[to_additive]
theorem partialProd_succ (f : Fin n → α) (j : Fin n) :
    partialProd f j.succ = partialProd f j.cast_succ * f j := by
  simp [partial_prod, List.take_succ, List.ofFnNthVal, dif_pos j.is_lt, ← Option.coe_def]
#align fin.partial_prod_succ Fin.partialProd_succ
#align fin.partial_sum_succ Fin.partialSum_succ
-/

#print Fin.partialProd_succ' /-
@[to_additive]
theorem partialProd_succ' (f : Fin (n + 1) → α) (j : Fin (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Fin.tail f) j := by simpa [partial_prod]
#align fin.partial_prod_succ' Fin.partialProd_succ'
#align fin.partial_sum_succ' Fin.partialSum_succ'
-/

#print Fin.partialProd_left_inv /-
@[to_additive]
theorem partialProd_left_inv {G : Type _} [Group G] (f : Fin (n + 1) → G) :
    (f 0 • partialProd fun i : Fin n => (f i)⁻¹ * f i.succ) = f :=
  funext fun x =>
    Fin.inductionOn x (by simp) fun x hx =>
      by
      simp only [coe_eq_cast_succ, Pi.smul_apply, smul_eq_mul] at hx ⊢
      rw [partial_prod_succ, ← mul_assoc, hx, mul_inv_cancel_left]
#align fin.partial_prod_left_inv Fin.partialProd_left_inv
#align fin.partial_sum_left_neg Fin.partialSum_left_neg
-/

#print Fin.partialProd_right_inv /-
@[to_additive]
theorem partialProd_right_inv {G : Type _} [Group G] (f : Fin n → G) (i : Fin n) :
    (partialProd f i.cast_succ)⁻¹ * partialProd f i.succ = f i :=
  by
  cases' i with i hn
  induction' i with i hi generalizing hn
  · simp [-Fin.succ_mk, partial_prod_succ]
  · specialize hi (lt_trans (Nat.lt_succ_self i) hn)
    simp only [Fin.coe_eq_castSuccEmb, Fin.succ_mk, Fin.castSuccEmb_mk] at hi ⊢
    rw [← Fin.succ_mk _ _ (lt_trans (Nat.lt_succ_self _) hn), ← Fin.succ_mk]
    simp only [partial_prod_succ, mul_inv_rev, Fin.castSuccEmb_mk]
    assoc_rw [hi, inv_mul_cancel_left]
#align fin.partial_prod_right_inv Fin.partialProd_right_inv
#align fin.partial_sum_right_neg Fin.partialSum_right_neg
-/

#print Fin.inv_partialProd_mul_eq_contractNth /-
/-- Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.
Then if `k < j`, this says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ = gₖ`.
If `k = j`, it says `(g₀g₁...gₖ₋₁)⁻¹ * g₀g₁...gₖ₊₁ = gₖgₖ₊₁`.
If `k > j`, it says `(g₀g₁...gₖ)⁻¹ * g₀g₁...gₖ₊₁ = gₖ₊₁.`
Useful for defining group cohomology. -/
@[to_additive
      "Let `(g₀, g₁, ..., gₙ)` be a tuple of elements in `Gⁿ⁺¹`.\nThen if `k < j`, this says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ) = gₖ`.\nIf `k = j`, it says `-(g₀ + g₁ + ... + gₖ₋₁) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ + gₖ₊₁`.\nIf `k > j`, it says `-(g₀ + g₁ + ... + gₖ) + (g₀ + g₁ + ... + gₖ₊₁) = gₖ₊₁.`\nUseful for defining group cohomology."]
theorem inv_partialProd_mul_eq_contractNth {G : Type _} [Group G] (g : Fin (n + 1) → G)
    (j : Fin (n + 1)) (k : Fin n) :
    (partialProd g (j.succ.succAbove k.cast_succ))⁻¹ * partialProd g (j.succAbove k).succ =
      j.contractNth Mul.mul g k :=
  by
  rcases lt_trichotomy (k : ℕ) j with (h | h | h)
  · rwa [succ_above_below, succ_above_below, partial_prod_right_inv, contract_nth_apply_of_lt]
    · assumption
    · rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe]
      exact le_of_lt h
  · rwa [succ_above_below, succ_above_above, partial_prod_succ, cast_succ_fin_succ, ← mul_assoc,
      partial_prod_right_inv, contract_nth_apply_of_eq]
    · simpa only [le_iff_coe_le_coe, ← h]
    · rw [cast_succ_lt_iff_succ_le, succ_le_succ_iff, le_iff_coe_le_coe]
      exact le_of_eq h
  · rwa [succ_above_above, succ_above_above, partial_prod_succ, partial_prod_succ,
      cast_succ_fin_succ, partial_prod_succ, inv_mul_cancel_left, contract_nth_apply_of_gt]
    · exact le_iff_coe_le_coe.2 (le_of_lt h)
    · rw [le_iff_coe_le_coe, coe_succ]
      exact Nat.succ_le_of_lt h
#align fin.inv_partial_prod_mul_eq_contract_nth Fin.inv_partialProd_mul_eq_contractNth
#align fin.neg_partial_sum_add_eq_contract_nth Fin.neg_partialSum_add_eq_contractNth
-/

end PartialProd

end Fin

#print finFunctionFinEquiv /-
/-- Equivalence between `fin n → fin m` and `fin (m ^ n)`. -/
@[simps]
def finFunctionFinEquiv {m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n) :=
  Equiv.ofRightInverseOfCardLe (le_of_eq <| by simp_rw [Fintype.card_fun, Fintype.card_fin])
    (fun f =>
      ⟨∑ i, f i * m ^ (i : ℕ), by
        induction' n with n ih generalizing f
        · simp
        cases m
        · exact isEmptyElim (f <| Fin.last _)
        simp_rw [Fin.sum_univ_castSuccEmb, Fin.coe_castSuccEmb, Fin.val_last]
        refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
        rw [← one_add_mul, add_comm, pow_succ]⟩)
    (fun a b =>
      ⟨a / m ^ (b : ℕ) % m, by
        cases n
        · exact b.elim0
        cases m
        · rw [zero_pow n.succ_pos] at a 
          exact a.elim0
        · exact Nat.mod_lt _ m.succ_pos⟩)
    fun a => by
    dsimp
    induction' n with n ih generalizing a
    · haveI : Subsingleton (Fin (m ^ 0)) := (Fin.castIso <| pow_zero _).toEquiv.Subsingleton
      exact Subsingleton.elim _ _
    simp_rw [Fin.forall_iff, Fin.ext_iff, Fin.val_mk] at ih 
    ext
    simp_rw [Fin.val_mk, Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, pow_zero, Nat.div_one,
      mul_one, pow_succ, ← Nat.div_div_eq_div_mul, mul_left_comm _ m, ← mul_sum]
    rw [ih _ (Nat.div_lt_of_lt_mul a.is_lt), Nat.mod_add_div]
#align fin_function_fin_equiv finFunctionFinEquiv
-/

#print finFunctionFinEquiv_apply /-
theorem finFunctionFinEquiv_apply {m n : ℕ} (f : Fin n → Fin m) :
    (finFunctionFinEquiv f : ℕ) = ∑ i : Fin n, ↑(f i) * m ^ (i : ℕ) :=
  rfl
#align fin_function_fin_equiv_apply finFunctionFinEquiv_apply
-/

#print finFunctionFinEquiv_single /-
theorem finFunctionFinEquiv_single {m n : ℕ} [NeZero m] (i : Fin n) (j : Fin m) :
    (finFunctionFinEquiv (Pi.single i j) : ℕ) = j * m ^ (i : ℕ) :=
  by
  rw [finFunctionFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, MulZeroClass.zero_mul]
#align fin_function_fin_equiv_single finFunctionFinEquiv_single
-/

#print finPiFinEquiv /-
/-- Equivalence between `Π i : fin m, fin (n i)` and `fin (∏ i : fin m, n i)`. -/
def finPiFinEquiv {m : ℕ} {n : Fin m → ℕ} : (∀ i : Fin m, Fin (n i)) ≃ Fin (∏ i : Fin m, n i) :=
  Equiv.ofRightInverseOfCardLe (le_of_eq <| by simp_rw [Fintype.card_pi, Fintype.card_fin])
    (fun f =>
      ⟨∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j),
        by
        induction' m with m ih generalizing f
        · simp
        rw [Fin.prod_univ_castSuccEmb, Fin.sum_univ_castSuccEmb]
        suffices
          ∀ (n : Fin m → ℕ) (nn : ℕ) (f : ∀ i : Fin m, Fin (n i)) (fn : Fin nn),
            ∑ i : Fin m, ↑(f i) * ∏ j : Fin i, n (Fin.castLE i.prop.le j) + ↑fn * ∏ j, n j <
              (∏ i : Fin m, n i) * nn
          by
          replace this := this (Fin.init n) (n (Fin.last _)) (Fin.init f) (f (Fin.last _))
          rw [← Fin.snoc_init_self f]
          simp (config := { singlePass := true }) only [← Fin.snoc_init_self n]
          simp_rw [Fin.snoc_castSuccEmb, Fin.init_snoc, Fin.snoc_last, Fin.snoc_init_self n]
          exact this
        intro n nn f fn
        cases nn
        · exact isEmptyElim fn
        refine' (add_lt_add_of_lt_of_le (ih _) <| mul_le_mul_right' (Fin.is_le _) _).trans_eq _
        rw [← one_add_mul, mul_comm, add_comm]⟩)
    (fun a b =>
      ⟨(a / ∏ j : Fin b, n (Fin.castLE b.is_lt.le j)) % n b,
        by
        cases m
        · exact b.elim0
        cases' h : n b with nb
        · rw [prod_eq_zero (Finset.mem_univ _) h] at a 
          exact isEmptyElim a
        exact Nat.mod_lt _ nb.succ_pos⟩)
    (by
      intro a; revert a; dsimp only [Fin.val_mk]
      refine' Fin.consInduction _ _ n
      · intro a
        haveI : Subsingleton (Fin (∏ i : Fin 0, i.elim0ₓ)) :=
          (Fin.castIso <| prod_empty).toEquiv.Subsingleton
        exact Subsingleton.elim _ _
      · intro n x xs ih a
        simp_rw [Fin.forall_iff, Fin.ext_iff, Fin.val_mk] at ih 
        ext
        simp_rw [Fin.val_mk, Fin.sum_univ_succ, Fin.cons_succ]
        have := fun i : Fin n =>
          Fintype.prod_equiv (Fin.castIso <| Fin.val_succ i).toEquiv
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Fin.is_lt _).le j))
            (fun j => (Fin.cons x xs : _ → ℕ) (Fin.castLE (Nat.succ_le_succ (Fin.is_lt _).le) j))
            fun j => rfl
        simp_rw [this]; clear this
        dsimp only [Fin.val_zero]
        simp_rw [Fintype.prod_empty, Nat.div_one, mul_one, Fin.cons_zero, Fin.prod_univ_succ]
        change _ + ∑ y : _, _ / (x * _) % _ * (x * _) = _
        simp_rw [← Nat.div_div_eq_div_mul, mul_left_comm (_ % _ : ℕ), ← mul_sum]
        convert Nat.mod_add_div _ _
        refine' Eq.trans _ (ih (a / x) (Nat.div_lt_of_lt_mul <| a.is_lt.trans_eq _))
        swap
        · convert Fin.prod_univ_succ (Fin.cons x xs : ∀ _, ℕ)
          simp_rw [Fin.cons_succ]
        congr with i
        congr with j
        · cases j; rfl
        · cases j; rfl)
#align fin_pi_fin_equiv finPiFinEquiv
-/

#print finPiFinEquiv_apply /-
theorem finPiFinEquiv_apply {m : ℕ} {n : Fin m → ℕ} (f : ∀ i : Fin m, Fin (n i)) :
    (finPiFinEquiv f : ℕ) = ∑ i, f i * ∏ j, n (Fin.castLE i.is_lt.le j) :=
  rfl
#align fin_pi_fin_equiv_apply finPiFinEquiv_apply
-/

#print finPiFinEquiv_single /-
theorem finPiFinEquiv_single {m : ℕ} {n : Fin m → ℕ} [∀ i, NeZero (n i)] (i : Fin m)
    (j : Fin (n i)) :
    (finPiFinEquiv (Pi.single i j : ∀ i : Fin m, Fin (n i)) : ℕ) =
      j * ∏ j, n (Fin.castLE i.is_lt.le j) :=
  by
  rw [finPiFinEquiv_apply, Fintype.sum_eq_single i, Pi.single_eq_same]
  rintro x hx
  rw [Pi.single_eq_of_ne hx, Fin.val_zero, MulZeroClass.zero_mul]
#align fin_pi_fin_equiv_single finPiFinEquiv_single
-/

namespace List

section CommMonoid

variable [CommMonoid α]

#print List.prod_take_ofFn /-
@[to_additive]
theorem prod_take_ofFn {n : ℕ} (f : Fin n → α) (i : ℕ) :
    ((ofFn f).take i).Prod = ∏ j in Finset.univ.filterₓ fun j : Fin n => j.val < i, f j :=
  by
  have A : ∀ j : Fin n, ¬(j : ℕ) < 0 := fun j => not_lt_bot
  induction' i with i IH; · simp [A]
  by_cases h : i < n
  · have : i < length (of_fn f) := by rwa [length_of_fn f]
    rw [prod_take_succ _ _ this]
    have A :
      ((Finset.univ : Finset (Fin n)).filterₓ fun j => j.val < i + 1) =
        ((Finset.univ : Finset (Fin n)).filterₓ fun j => j.val < i) ∪ {(⟨i, h⟩ : Fin n)} :=
      by ext ⟨_, _⟩; simp [Nat.lt_succ_iff_lt_or_eq]
    have B :
      _root_.disjoint (Finset.filter (fun j : Fin n => j.val < i) Finset.univ)
        (singleton (⟨i, h⟩ : Fin n)) :=
      by simp
    rw [A, Finset.prod_union B, IH]
    simp
  · have A : (of_fn f).take i = (of_fn f).take i.succ :=
      by
      rw [← length_of_fn f] at h 
      have : length (of_fn f) ≤ i := not_lt.mp h
      rw [take_all_of_le this, take_all_of_le (le_trans this (Nat.le_succ _))]
    have B : ∀ j : Fin n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) :=
      by
      intro j
      have : (j : ℕ) < i := lt_of_lt_of_le j.2 (not_lt.mp h)
      simp [this, lt_trans this (Nat.lt_succ_self _)]
    simp [← A, B, IH]
#align list.prod_take_of_fn List.prod_take_ofFn
#align list.sum_take_of_fn List.sum_take_ofFn
-/

#print List.prod_ofFn /-
@[to_additive]
theorem prod_ofFn {n : ℕ} {f : Fin n → α} : (ofFn f).Prod = ∏ i, f i :=
  by
  convert prod_take_of_fn f n
  · rw [take_all_of_le (le_of_eq (length_of_fn f))]
  · have : ∀ j : Fin n, (j : ℕ) < n := fun j => j.is_lt
    simp [this]
#align list.prod_of_fn List.prod_ofFn
#align list.sum_of_fn List.sum_ofFn
-/

end CommMonoid

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print List.alternatingSum_eq_finset_sum /-
theorem alternatingSum_eq_finset_sum {G : Type _} [AddCommGroup G] :
    ∀ L : List G, alternatingSum L = ∑ i : Fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.is_lt
  | [] => by rw [alternating_sum, Finset.sum_eq_zero]; rintro ⟨i, ⟨⟩⟩
  | g::[] => by simp
  | g::h::L =>
    calc
      g + -h + L.alternatingSum = g + -h + ∑ i : Fin L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.2 :=
        congr_arg _ (alternating_sum_eq_finset_sum _)
      _ = ∑ i : Fin (L.length + 2), (-1 : ℤ) ^ (i : ℕ) • List.nthLe (g::h::L) i _ :=
        by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, add_assoc]
        unfold_coes
        simp [Nat.succ_eq_add_one, pow_add]
        rfl
#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sum
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print List.alternatingProd_eq_finset_prod /-
@[to_additive]
theorem alternatingProd_eq_finset_prod {G : Type _} [CommGroup G] :
    ∀ L : List G, alternatingProd L = ∏ i : Fin L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by rw [alternating_prod, Finset.prod_eq_one]; rintro ⟨i, ⟨⟩⟩
  | g::[] => by
    show g = ∏ i : Fin 1, [g].nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Fin.prod_univ_succ]; simp
  | g::h::L =>
    calc
      g * h⁻¹ * L.alternatingProd =
          g * h⁻¹ * ∏ i : Fin L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternating_prod_eq_finset_prod _)
      _ = ∏ i : Fin (L.length + 2), List.nthLe (g::h::L) i _ ^ (-1 : ℤ) ^ (i : ℕ) :=
        by
        rw [Fin.prod_univ_succ, Fin.prod_univ_succ, mul_assoc]
        unfold_coes
        simp [Nat.succ_eq_add_one, pow_add]
        rfl
#align list.alternating_prod_eq_finset_prod List.alternatingProd_eq_finset_prod
#align list.alternating_sum_eq_finset_sum List.alternatingSum_eq_finset_sum
-/

end List

