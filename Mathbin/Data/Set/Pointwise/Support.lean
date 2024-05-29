/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Data.Set.Pointwise.SMul
import Algebra.Group.Support

#align_import data.set.pointwise.support from "leanprover-community/mathlib"@"68d1483e8a718ec63219f0e227ca3f0140361086"

/-!
# Support of a function composed with a scalar action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/


open scoped Pointwise

open Function Set

section Group

variable {α β γ : Type _} [Group α] [MulAction α β]

#print mulSupport_comp_inv_smul /-
theorem mulSupport_comp_inv_smul [One γ] (c : α) (f : β → γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f := by ext x;
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mul_support]
#align mul_support_comp_inv_smul mulSupport_comp_inv_smul
-/

#print support_comp_inv_smul /-
theorem support_comp_inv_smul [Zero γ] (c : α) (f : β → γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f := by ext x;
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]
#align support_comp_inv_smul support_comp_inv_smul
-/

attribute [to_additive support_comp_inv_smul] mulSupport_comp_inv_smul

end Group

section GroupWithZero

variable {α β γ : Type _} [GroupWithZero α] [MulAction α β]

#print mulSupport_comp_inv_smul₀ /-
theorem mulSupport_comp_inv_smul₀ [One γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f := by ext x;
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mul_support]
#align mul_support_comp_inv_smul₀ mulSupport_comp_inv_smul₀
-/

#print support_comp_inv_smul₀ /-
theorem support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f := by ext x;
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]
#align support_comp_inv_smul₀ support_comp_inv_smul₀
-/

attribute [to_additive support_comp_inv_smul₀] mulSupport_comp_inv_smul₀

end GroupWithZero

