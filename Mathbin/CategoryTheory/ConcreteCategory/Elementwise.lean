/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Tactic.Elementwise
import CategoryTheory.Limits.HasLimits
import CategoryTheory.Limits.Shapes.Kernels
import CategoryTheory.ConcreteCategory.Basic
import Tactic.FreshNames

#align_import category_theory.concrete_category.elementwise from "leanprover-community/mathlib"@"cb3ceec8485239a61ed51d944cb9a95b68c6bafc"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we provide various simp lemmas in its elementwise form via `tactic.elementwise`.
-/


open CategoryTheory CategoryTheory.Limits

attribute [elementwise] cone.w limit.lift_π limit.w cocone.w colimit.ι_desc colimit.w kernel.lift_ι
  cokernel.π_desc kernel.condition cokernel.condition

