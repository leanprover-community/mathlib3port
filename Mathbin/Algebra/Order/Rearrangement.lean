/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import Mathbin.Algebra.Order.Module
import Mathbin.Data.Prod.Lex
import Mathbin.GroupTheory.Perm.Support
import Mathbin.Order.Monovary
import Mathbin.Tactic.Abel

/-!
# Rearrangement inequality

This file proves the rearrangement inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/


open Equivₓ Equivₓ.Perm Finset OrderDual

open BigOperators

variable {ι α β : Type _}

/-! ### Scalar multiplication versions -/


section Smul

variable [LinearOrderedRing α] [LinearOrderedAddCommGroup β] [Module α β] [OrderedSmul α β] {s : Finset ι} {σ : Perm ι}
  {f : ι → α} {g : ι → β}

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
theorem MonovaryOn.sum_smul_comp_perm_le_sum_smul (hfg : MonovaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i • g (σ i)) ≤ ∑ i in s, f i • g i := by
  classical
  revert hσ σ hfg
  apply Finset.induction_on_max_value (fun i => toLex (g i, f i)) s
  · simp only [le_rfl, Finset.sum_empty, implies_true_iff]
    
  intro a s has hamax hind σ hfg hσ
  set τ : perm ι := σ.trans (swap a (σ a)) with hτ
  have hτs : { x | τ x ≠ x } ⊆ s := by
    intro x hx
    simp only [Ne.def, Set.mem_set_of_eq, Equivₓ.coe_trans, Equivₓ.swap_comp_apply] at hx
    split_ifs  at hx with h₁ h₂ h₃
    · obtain rfl | hax := eq_or_ne x a
      · contradiction
        
      · exact mem_of_mem_insert_of_ne (hσ fun h => hax <| h.symm.trans h₁) hax
        
      
    · exact (hx <| σ.injective h₂.symm).elim
      
    · exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂)
      
  specialize hind (hfg.subset <| subset_insert _ _) hτs
  simp_rw [sum_insert has]
  refine' le_transₓ _ (add_le_add_left hind _)
  obtain hσa | hσa := eq_or_ne a (σ a)
  · rw [← hσa, swap_self, trans_refl] at hτ
    rw [← hσa, hτ]
    
  have h1s : σ⁻¹ a ∈ s := by
    rw [Ne.def, ← inv_eq_iff_eq] at hσa
    refine' mem_of_mem_insert_of_ne (hσ fun h => hσa _) hσa
    rwa [apply_inv_self, eq_comm] at h
  simp only [← s.sum_erase_add _ h1s, add_commₓ]
  rw [← add_assocₓ, ← add_assocₓ]
  refine' add_le_add _ ((sum_congr rfl) fun x hx => _).le
  · simp only [hτ, swap_apply_left, Function.comp_app, Equivₓ.coe_trans, apply_inv_self]
    suffices 0 ≤ (f a - f (σ⁻¹ a)) • (g a - g (σ a)) by
      rw [← sub_nonneg]
      convert this
      simp only [smul_sub, sub_smul]
      abel
    refine' smul_nonneg (sub_nonneg_of_le _) (sub_nonneg_of_le _)
    · specialize hamax (σ⁻¹ a) h1s
      rw [Prod.Lex.le_iff] at hamax
      cases hamax
      · exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax
        
      · exact hamax.2
        
      
    · specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ <| σ.injective.ne hσa.symm) hσa.symm)
      rw [Prod.Lex.le_iff] at hamax
      cases hamax
      · exact hamax.le
        
      · exact hamax.1.le
        
      
    
  · congr 2
    rw [eq_comm, hτ]
    rw [mem_erase, Ne.def, eq_inv_iff_eq] at hx
    refine' swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _)
    rintro rfl
    exact has hx.2
    

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_smul_le_sum_smul (hfg : MonovaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f (σ i) • g i) ≤ ∑ i in s, f i • g i := by
  convert
    hfg.sum_smul_comp_perm_le_sum_smul
      (show { x | σ⁻¹ x ≠ x } ⊆ s by
        simp only [set_support_inv_eq, hσ]) using
    1
  exact σ.sum_comp' s (fun i j => f i • g j) hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
theorem AntivaryOn.sum_smul_le_sum_smul_comp_perm (hfg : AntivaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i • g i) ≤ ∑ i in s, f i • g (σ i) :=
  hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_smul_le_sum_comp_perm_smul (hfg : AntivaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i • g i) ≤ ∑ i in s, f (σ i) • g i :=
  hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ

variable [Fintype ι]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
theorem Monovary.sum_smul_comp_perm_le_sum_smul (hfg : Monovary f g) : (∑ i, f i • g (σ i)) ≤ ∑ i, f i • g i :=
  (hfg.MonovaryOn _).sum_smul_comp_perm_le_sum_smul fun i _ => mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
theorem Monovary.sum_comp_perm_smul_le_sum_smul (hfg : Monovary f g) : (∑ i, f (σ i) • g i) ≤ ∑ i, f i • g i :=
  (hfg.MonovaryOn _).sum_comp_perm_smul_le_sum_smul fun i _ => mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
theorem Antivary.sum_smul_le_sum_smul_comp_perm (hfg : Antivary f g) : (∑ i, f i • g i) ≤ ∑ i, f i • g (σ i) :=
  (hfg.AntivaryOn _).sum_smul_le_sum_smul_comp_perm fun i _ => mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_smul_le_sum_comp_perm_smul (hfg : Antivary f g) : (∑ i, f i • g i) ≤ ∑ i, f (σ i) • g i :=
  (hfg.AntivaryOn _).sum_smul_le_sum_comp_perm_smul fun i _ => mem_univ _

end Smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/


section Mul

variable [LinearOrderedRing α] {s : Finset ι} {σ : Perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
theorem MonovaryOn.sum_mul_comp_perm_le_sum_mul (hfg : MonovaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i * g (σ i)) ≤ ∑ i in s, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
theorem MonovaryOn.sum_comp_perm_mul_le_sum_mul (hfg : MonovaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f (σ i) * g i) ≤ ∑ i in s, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
theorem AntivaryOn.sum_mul_le_sum_mul_comp_perm (hfg : AntivaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i * g i) ≤ ∑ i in s, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
theorem AntivaryOn.sum_mul_le_sum_comp_perm_mul (hfg : AntivaryOn f g s) (hσ : { x | σ x ≠ x } ⊆ s) :
    (∑ i in s, f i * g i) ≤ ∑ i in s, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul hσ

variable [Fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
theorem Monovary.sum_mul_comp_perm_le_sum_mul (hfg : Monovary f g) : (∑ i, f i * g (σ i)) ≤ ∑ i, f i * g i :=
  hfg.sum_smul_comp_perm_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
theorem Monovary.sum_comp_perm_mul_le_sum_mul (hfg : Monovary f g) : (∑ i, f (σ i) * g i) ≤ ∑ i, f i * g i :=
  hfg.sum_comp_perm_smul_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
theorem Antivary.sum_mul_le_sum_mul_comp_perm (hfg : Antivary f g) : (∑ i, f i * g i) ≤ ∑ i, f i * g (σ i) :=
  hfg.sum_smul_le_sum_smul_comp_perm

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
theorem Antivary.sum_mul_le_sum_comp_perm_mul (hfg : Antivary f g) : (∑ i, f i * g i) ≤ ∑ i, f (σ i) * g i :=
  hfg.sum_smul_le_sum_comp_perm_smul

end Mul

