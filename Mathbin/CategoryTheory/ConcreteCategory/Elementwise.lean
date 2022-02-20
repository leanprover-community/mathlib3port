/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w kernel.condition cokernel.condition is_iso.hom_inv_id is_iso.inv_hom_id

-- Note that the elementwise forms of `iso.hom_inv_id` and `iso.inv_hom_id` are already
-- provided as `category_theory.coe_hom_inv_id` and `category_theory.coe_inv_hom_id`.
