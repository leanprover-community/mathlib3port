/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Algebra.Support

/-!
# Support of a function composed with a scalar action

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/


open Pointwise

open Function Set

section Group

variable {α β γ : Type _} [Group α] [MulAction α β]

theorem mul_support_comp_inv_smul [One γ] (c : α) (f : β → γ) : (MulSupport fun x => f (c⁻¹ • x)) = c • MulSupport f :=
  by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mul_support]

theorem support_comp_inv_smul [Zero γ] (c : α) (f : β → γ) : (Support fun x => f (c⁻¹ • x)) = c • Support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

attribute [to_additive support_comp_inv_smul] mul_support_comp_inv_smul

end Group

section GroupWithZero

variable {α β γ : Type _} [GroupWithZero α] [MulAction α β]

theorem mul_support_comp_inv_smul₀ [One γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (MulSupport fun x => f (c⁻¹ • x)) = c • MulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mul_support]

theorem support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (Support fun x => f (c⁻¹ • x)) = c • Support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]

attribute [to_additive support_comp_inv_smul₀] mul_support_comp_inv_smul₀

end GroupWithZero

