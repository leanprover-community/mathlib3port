import Mathbin.Tactic.Elementwise
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.CategoryTheory.Limits.Shapes.Kernels

/-!
In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

attribute [elementwise]
  cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w kernel.condition cokernel.condition is_iso.hom_inv_id is_iso.inv_hom_id

