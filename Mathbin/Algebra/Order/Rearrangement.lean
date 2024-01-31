/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import Algebra.BigOperators.Basic
import Algebra.Order.Module
import Data.Prod.Lex
import GroupTheory.Perm.Support
import Order.Monotone.Monovary
import Tactic.Abel

#align_import algebra.order.rearrangement from "leanprover-community/mathlib"@"25a9423c6b2c8626e91c688bfd6c1d0a986a3e6e"

/-!
# Rearrangement inequality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the rearrangement inequality and deduces the conditions for equality and strict
inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

The inequality also tells you that `∑ i, f i * g (σ i) = ∑ i, f i * g i` if and only if `g ∘ σ`
monovaries with `f` when `g` monovaries with `f`. The above equality also holds if and only if
`g ∘ σ` antivaries with `f` when `g` antivaries with `f`.

From the above two statements, we deduce that the inequality is strict if and only if `g ∘ σ` does
not monovary with `f` when `g` monovaries with `f`. Analogously, the inequality is strict if and
only if `g ∘ σ` does not antivary with `f` when `g` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/


open Equiv Equiv.Perm Finset Function OrderDual

open scoped BigOperators

variable {ι α β : Type _}

/-! ### Scalar multiplication versions -/


section Smul

variable [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β] [OrderedSMul α β]
  {s : Finset ι} {σ : Perm ι} {f : ι → α} {g : ι → β}

#print MonovaryOn.sum_smul_comp_perm_le_sum_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_smul_comp_perm_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i := by classical
#align monovary_on.sum_smul_comp_perm_le_sum_smul MonovaryOn.sum_smul_comp_perm_le_sum_smul
-/

#print MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ MonovaryOn f (g ∘ σ) s := by classical
#align monovary_on.sum_smul_comp_perm_eq_sum_smul_iff MonovaryOn.sum_smul_comp_perm_eq_sum_smul_iff
-/

#print MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ ¬MonovaryOn f (g ∘ σ) s := by
  simp [← hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ, lt_iff_le_and_ne,
    hfg.sum_smul_comp_perm_le_sum_smul hσ]
#align monovary_on.sum_smul_comp_perm_lt_sum_smul_iff MonovaryOn.sum_smul_comp_perm_lt_sum_smul_iff
-/

#print MonovaryOn.sum_comp_perm_smul_le_sum_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_smul_le_sum_smul (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i in s, f (σ i) • g i ≤ ∑ i in s, f i • g i :=
  by
  convert
    hfg.sum_smul_comp_perm_le_sum_smul
      (show {x | σ⁻¹ x ≠ x} ⊆ s by simp only [set_support_inv_eq, hσ]) using
    1
  exact σ.sum_comp' s (fun i j => f i • g j) hσ
#align monovary_on.sum_comp_perm_smul_le_sum_smul MonovaryOn.sum_comp_perm_smul_le_sum_smul
-/

#print MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ MonovaryOn (f ∘ σ) g s :=
  by
  have hσinv : {x | σ⁻¹ x ≠ x} ⊆ s := (set_support_inv_eq _).Subset.trans hσ
  refine'
    (Iff.trans _ <| hfg.sum_smul_comp_perm_eq_sum_smul_iff hσinv).trans ⟨fun h => _, fun h => _⟩
  · simpa only [σ.sum_comp' s (fun i j => f i • g j) hσ]
  · convert h.comp_right σ
    · rw [comp.assoc, inv_def, symm_comp_self, comp.right_id]
    · rw [σ.eq_preimage_iff_image_eq, Set.image_perm hσ]
  · convert h.comp_right σ.symm
    · rw [comp.assoc, self_comp_symm, comp.right_id]
    · rw [σ.symm.eq_preimage_iff_image_eq]
      exact Set.image_perm hσinv
#align monovary_on.sum_comp_perm_smul_eq_sum_smul_iff MonovaryOn.sum_comp_perm_smul_eq_sum_smul_iff
-/

#print MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) • g i < ∑ i in s, f i • g i ↔ ¬MonovaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ, lt_iff_le_and_ne,
    hfg.sum_comp_perm_smul_le_sum_smul hσ]
#align monovary_on.sum_comp_perm_smul_lt_sum_smul_iff MonovaryOn.sum_comp_perm_smul_lt_sum_smul_iff
-/

#print AntivaryOn.sum_smul_le_sum_smul_comp_perm /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_smul_le_sum_smul_comp_perm (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
  hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ
#align antivary_on.sum_smul_le_sum_smul_comp_perm AntivaryOn.sum_smul_le_sum_smul_comp_perm
-/

#print AntivaryOn.sum_smul_eq_sum_smul_comp_perm_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_smul_eq_sum_smul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ AntivaryOn f (g ∘ σ) s :=
  (hfg.dual_right.sum_smul_comp_perm_eq_sum_smul_iff hσ).trans monovaryOn_toDual_right
#align antivary_on.sum_smul_eq_sum_smul_comp_perm_iff AntivaryOn.sum_smul_eq_sum_smul_comp_perm_iff
-/

#print AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g i < ∑ i in s, f i • g (σ i) ↔ ¬AntivaryOn f (g ∘ σ) s := by
  simp [← hfg.sum_smul_eq_sum_smul_comp_perm_iff hσ, lt_iff_le_and_ne, eq_comm,
    hfg.sum_smul_le_sum_smul_comp_perm hσ]
#align antivary_on.sum_smul_lt_sum_smul_comp_perm_iff AntivaryOn.sum_smul_lt_sum_smul_comp_perm_iff
-/

#print AntivaryOn.sum_smul_le_sum_comp_perm_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_smul_le_sum_comp_perm_smul (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) : ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
  hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ
#align antivary_on.sum_smul_le_sum_comp_perm_smul AntivaryOn.sum_smul_le_sum_comp_perm_smul
-/

#print AntivaryOn.sum_smul_eq_sum_comp_perm_smul_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_smul_eq_sum_comp_perm_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ AntivaryOn (f ∘ σ) g s :=
  (hfg.dual_right.sum_comp_perm_smul_eq_sum_smul_iff hσ).trans monovaryOn_toDual_right
#align antivary_on.sum_smul_eq_sum_comp_perm_smul_iff AntivaryOn.sum_smul_eq_sum_comp_perm_smul_iff
-/

#print AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g i < ∑ i in s, f (σ i) • g i ↔ ¬AntivaryOn (f ∘ σ) g s := by
  simp [← hfg.sum_smul_eq_sum_comp_perm_smul_iff hσ, eq_comm, lt_iff_le_and_ne,
    hfg.sum_smul_le_sum_comp_perm_smul hσ]
#align antivary_on.sum_smul_lt_sum_comp_perm_smul_iff AntivaryOn.sum_smul_lt_sum_comp_perm_smul_iff
-/

variable [Fintype ι]

#print Monovary.sum_smul_comp_perm_le_sum_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_smul_comp_perm_le_sum_smul (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
  (hfg.MonovaryOn _).sum_smul_comp_perm_le_sum_smul fun i _ => mem_univ _
#align monovary.sum_smul_comp_perm_le_sum_smul Monovary.sum_smul_comp_perm_le_sum_smul
-/

#print Monovary.sum_smul_comp_perm_eq_sum_smul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ Monovary f (g ∘ σ) := by
  simp [(hfg.monovary_on _).sum_smul_comp_perm_eq_sum_smul_iff fun i _ => mem_univ _]
#align monovary.sum_smul_comp_perm_eq_sum_smul_iff Monovary.sum_smul_comp_perm_eq_sum_smul_iff
-/

#print Monovary.sum_smul_comp_perm_lt_sum_smul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_smul_comp_perm_lt_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f i • g (σ i) < ∑ i, f i • g i ↔ ¬Monovary f (g ∘ σ) := by
  simp [(hfg.monovary_on _).sum_smul_comp_perm_lt_sum_smul_iff fun i _ => mem_univ _]
#align monovary.sum_smul_comp_perm_lt_sum_smul_iff Monovary.sum_smul_comp_perm_lt_sum_smul_iff
-/

#print Monovary.sum_comp_perm_smul_le_sum_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
theorem Monovary.sum_comp_perm_smul_le_sum_smul (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i ≤ ∑ i, f i • g i :=
  (hfg.MonovaryOn _).sum_comp_perm_smul_le_sum_smul fun i _ => mem_univ _
#align monovary.sum_comp_perm_smul_le_sum_smul Monovary.sum_comp_perm_smul_le_sum_smul
-/

#print Monovary.sum_comp_perm_smul_eq_sum_smul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ Monovary (f ∘ σ) g := by
  simp [(hfg.monovary_on _).sum_comp_perm_smul_eq_sum_smul_iff fun i _ => mem_univ _]
#align monovary.sum_comp_perm_smul_eq_sum_smul_iff Monovary.sum_comp_perm_smul_eq_sum_smul_iff
-/

#print Monovary.sum_comp_perm_smul_lt_sum_smul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_comp_perm_smul_lt_sum_smul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) • g i < ∑ i, f i • g i ↔ ¬Monovary (f ∘ σ) g := by
  simp [(hfg.monovary_on _).sum_comp_perm_smul_lt_sum_smul_iff fun i _ => mem_univ _]
#align monovary.sum_comp_perm_smul_lt_sum_smul_iff Monovary.sum_comp_perm_smul_lt_sum_smul_iff
-/

#print Antivary.sum_smul_le_sum_smul_comp_perm /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_smul_le_sum_smul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) :=
  (hfg.AntivaryOn _).sum_smul_le_sum_smul_comp_perm fun i _ => mem_univ _
#align antivary.sum_smul_le_sum_smul_comp_perm Antivary.sum_smul_le_sum_smul_comp_perm
-/

#print Antivary.sum_smul_eq_sum_smul_comp_perm_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_smul_eq_sum_smul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ Antivary f (g ∘ σ) := by
  simp [(hfg.antivary_on _).sum_smul_eq_sum_smul_comp_perm_iff fun i _ => mem_univ _]
#align antivary.sum_smul_eq_sum_smul_comp_perm_iff Antivary.sum_smul_eq_sum_smul_comp_perm_iff
-/

#print Antivary.sum_smul_lt_sum_smul_comp_perm_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_smul_lt_sum_smul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ) := by
  simp [(hfg.antivary_on _).sum_smul_lt_sum_smul_comp_perm_iff fun i _ => mem_univ _]
#align antivary.sum_smul_lt_sum_smul_comp_perm_iff Antivary.sum_smul_lt_sum_smul_comp_perm_iff
-/

#print Antivary.sum_smul_le_sum_comp_perm_smul /-
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_smul_le_sum_comp_perm_smul (hfg : Antivary f g) :
    ∑ i, f i • g i ≤ ∑ i, f (σ i) • g i :=
  (hfg.AntivaryOn _).sum_smul_le_sum_comp_perm_smul fun i _ => mem_univ _
#align antivary.sum_smul_le_sum_comp_perm_smul Antivary.sum_smul_le_sum_comp_perm_smul
-/

#print Antivary.sum_smul_eq_sum_comp_perm_smul_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_smul_eq_sum_comp_perm_smul_iff (hfg : Antivary f g) :
    ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ Antivary (f ∘ σ) g := by
  simp [(hfg.antivary_on _).sum_smul_eq_sum_comp_perm_smul_iff fun i _ => mem_univ _]
#align antivary.sum_smul_eq_sum_comp_perm_smul_iff Antivary.sum_smul_eq_sum_comp_perm_smul_iff
-/

#print Antivary.sum_smul_lt_sum_comp_perm_smul_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_smul_lt_sum_comp_perm_smul_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f (σ i) • g i ↔ ¬Antivary (f ∘ σ) g := by
  simp [(hfg.antivary_on _).sum_smul_lt_sum_comp_perm_smul_iff fun i _ => mem_univ _]
#align antivary.sum_smul_lt_sum_comp_perm_smul_iff Antivary.sum_smul_lt_sum_comp_perm_smul_iff
-/

end Smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul

variable [LinearOrderedRing α] {s : Finset ι} {σ : Perm ι} {f g : ι → α}

#print MonovaryOn.sum_mul_comp_perm_le_sum_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_mul_comp_perm_le_sum_mul (hfg : MonovaryOn f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g (σ i) ≤ ∑ i in s, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul hσ
#align monovary_on.sum_mul_comp_perm_le_sum_mul MonovaryOn.sum_mul_comp_perm_le_sum_mul
-/

#print MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ MonovaryOn f (g ∘ σ) s :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ
#align monovary_on.sum_mul_comp_perm_eq_sum_mul_iff MonovaryOn.sum_mul_comp_perm_eq_sum_mul_iff
-/

#print MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ ¬MonovaryOn f (g ∘ σ) s :=
  hfg.sum_smul_comp_perm_lt_sum_smul_iff hσ
#align monovary_on.sum_mul_comp_perm_lt_sum_mul_iff MonovaryOn.sum_mul_comp_perm_lt_sum_mul_iff
-/

#print MonovaryOn.sum_comp_perm_mul_le_sum_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_mul_le_sum_mul (hfg : MonovaryOn f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) * g i ≤ ∑ i in s, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul hσ
#align monovary_on.sum_comp_perm_mul_le_sum_mul MonovaryOn.sum_comp_perm_mul_le_sum_mul
-/

#print MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ MonovaryOn (f ∘ σ) g s :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ
#align monovary_on.sum_comp_perm_mul_eq_sum_mul_iff MonovaryOn.sum_comp_perm_mul_eq_sum_mul_iff
-/

#print MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff (hfg : MonovaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) * g i < ∑ i in s, f i * g i ↔ ¬MonovaryOn (f ∘ σ) g s :=
  hfg.sum_comp_perm_smul_lt_sum_smul_iff hσ
#align monovary_on.sum_comp_perm_mul_lt_sum_mul_iff MonovaryOn.sum_comp_perm_mul_lt_sum_mul_iff
-/

#print AntivaryOn.sum_mul_le_sum_mul_comp_perm /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_mul_le_sum_mul_comp_perm (hfg : AntivaryOn f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g i ≤ ∑ i in s, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm hσ
#align antivary_on.sum_mul_le_sum_mul_comp_perm AntivaryOn.sum_mul_le_sum_mul_comp_perm
-/

#print AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ AntivaryOn f (g ∘ σ) s :=
  hfg.sum_smul_eq_sum_smul_comp_perm_iff hσ
#align antivary_on.sum_mul_eq_sum_mul_comp_perm_iff AntivaryOn.sum_mul_eq_sum_mul_comp_perm_iff
-/

#print AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
theorem AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g i < ∑ i in s, f i * g (σ i) ↔ ¬AntivaryOn f (g ∘ σ) s :=
  hfg.sum_smul_lt_sum_smul_comp_perm_iff hσ
#align antivary_on.sum_mul_lt_sum_mul_comp_perm_iff AntivaryOn.sum_mul_lt_sum_mul_comp_perm_iff
-/

#print AntivaryOn.sum_mul_le_sum_comp_perm_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_mul_le_sum_comp_perm_mul (hfg : AntivaryOn f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g i ≤ ∑ i in s, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul hσ
#align antivary_on.sum_mul_le_sum_comp_perm_mul AntivaryOn.sum_mul_le_sum_comp_perm_mul
-/

#print AntivaryOn.sum_mul_eq_sum_comp_perm_mul_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_mul_eq_sum_comp_perm_mul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ AntivaryOn (f ∘ σ) g s :=
  hfg.sum_smul_eq_sum_comp_perm_smul_iff hσ
#align antivary_on.sum_mul_eq_sum_comp_perm_mul_iff AntivaryOn.sum_mul_eq_sum_comp_perm_mul_iff
-/

#print AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff (hfg : AntivaryOn f g s)
    (hσ : {x | σ x ≠ x} ⊆ s) :
    ∑ i in s, f i * g i < ∑ i in s, f (σ i) * g i ↔ ¬AntivaryOn (f ∘ σ) g s :=
  hfg.sum_smul_lt_sum_comp_perm_smul_iff hσ
#align antivary_on.sum_mul_lt_sum_comp_perm_mul_iff AntivaryOn.sum_mul_lt_sum_comp_perm_mul_iff
-/

variable [Fintype ι]

#print Monovary.sum_mul_comp_perm_le_sum_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_mul_comp_perm_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul
#align monovary.sum_mul_comp_perm_le_sum_mul Monovary.sum_mul_comp_perm_le_sum_mul
-/

#print Monovary.sum_mul_comp_perm_eq_sum_mul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_mul_comp_perm_eq_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ Monovary f (g ∘ σ) :=
  hfg.sum_smul_comp_perm_eq_sum_smul_iff
#align monovary.sum_mul_comp_perm_eq_sum_mul_iff Monovary.sum_mul_comp_perm_eq_sum_mul_iff
-/

#print Monovary.sum_mul_comp_perm_lt_sum_mul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_mul_comp_perm_lt_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f i * g (σ i) < ∑ i, f i * g i ↔ ¬Monovary f (g ∘ σ) :=
  hfg.sum_smul_comp_perm_lt_sum_smul_iff
#align monovary.sum_mul_comp_perm_lt_sum_mul_iff Monovary.sum_mul_comp_perm_lt_sum_mul_iff
-/

#print Monovary.sum_comp_perm_mul_le_sum_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
theorem Monovary.sum_comp_perm_mul_le_sum_mul (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul
#align monovary.sum_comp_perm_mul_le_sum_mul Monovary.sum_comp_perm_mul_le_sum_mul
-/

#print Monovary.sum_comp_perm_mul_eq_sum_mul_iff /-
/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ Monovary (f ∘ σ) g :=
  hfg.sum_comp_perm_smul_eq_sum_smul_iff
#align monovary.sum_comp_perm_mul_eq_sum_mul_iff Monovary.sum_comp_perm_mul_eq_sum_mul_iff
-/

#print Monovary.sum_comp_perm_mul_lt_sum_mul_iff /-
/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
theorem Monovary.sum_comp_perm_mul_lt_sum_mul_iff (hfg : Monovary f g) :
    ∑ i, f (σ i) * g i < ∑ i, f i * g i ↔ ¬Monovary (f ∘ σ) g :=
  hfg.sum_comp_perm_smul_lt_sum_smul_iff
#align monovary.sum_comp_perm_mul_lt_sum_mul_iff Monovary.sum_comp_perm_mul_lt_sum_mul_iff
-/

#print Antivary.sum_mul_le_sum_mul_comp_perm /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_mul_le_sum_mul_comp_perm (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm
#align antivary.sum_mul_le_sum_mul_comp_perm Antivary.sum_mul_le_sum_mul_comp_perm
-/

#print Antivary.sum_mul_eq_sum_mul_comp_perm_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_mul_eq_sum_mul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ Antivary f (g ∘ σ) :=
  hfg.sum_smul_eq_sum_smul_comp_perm_iff
#align antivary.sum_mul_eq_sum_mul_comp_perm_iff Antivary.sum_mul_eq_sum_mul_comp_perm_iff
-/

#print Antivary.sum_mul_lt_sum_mul_comp_perm_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
theorem Antivary.sum_mul_lt_sum_mul_comp_perm_iff (hfg : Antivary f g) :
    ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬Antivary f (g ∘ σ) :=
  hfg.sum_smul_lt_sum_smul_comp_perm_iff
#align antivary.sum_mul_lt_sum_mul_comp_perm_iff Antivary.sum_mul_lt_sum_mul_comp_perm_iff
-/

#print Antivary.sum_mul_le_sum_comp_perm_mul /-
/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_mul_le_sum_comp_perm_mul (hfg : Antivary f g) :
    ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul
#align antivary.sum_mul_le_sum_comp_perm_mul Antivary.sum_mul_le_sum_comp_perm_mul
-/

#print Antivary.sum_mul_eq_sum_comp_perm_mul_iff /-
/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_mul_eq_sum_comp_perm_mul_iff (hfg : Antivary f g) :
    ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ Antivary (f ∘ σ) g :=
  hfg.sum_smul_eq_sum_comp_perm_smul_iff
#align antivary.sum_mul_eq_sum_comp_perm_mul_iff Antivary.sum_mul_eq_sum_comp_perm_mul_iff
-/

#print Antivary.sum_mul_lt_sum_comp_perm_mul_iff /-
/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_mul_lt_sum_comp_perm_mul_iff (hfg : Antivary f g) :
    ∑ i, f i * g i < ∑ i, f (σ i) * g i ↔ ¬Antivary (f ∘ σ) g :=
  hfg.sum_smul_lt_sum_comp_perm_smul_iff
#align antivary.sum_mul_lt_sum_comp_perm_mul_iff Antivary.sum_mul_lt_sum_comp_perm_mul_iff
-/

end Mul

