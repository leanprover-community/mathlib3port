/-
Copyright (c) 2019 Chris Hughes All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import Mathbin.Analysis.Complex.Liouville
import Mathbin.FieldTheory.IsAlgClosed.Basic

#align_import analysis.complex.polynomial from "leanprover-community/mathlib"@"660b3a2db3522fa0db036e569dc995a615c4c848"

/-!
# The fundamental theorem of algebra

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves that every nonconstant complex polynomial has a root using Liouville's theorem.

As a consequence, the complex numbers are algebraically closed.
-/


open Polynomial

open scoped Polynomial

namespace Complex

#print Complex.exists_root /-
/-- **Fundamental theorem of algebra**: every non constant complex polynomial
  has a root -/
theorem exists_root {f : ℂ[X]} (hf : 0 < degree f) : ∃ z : ℂ, IsRoot f z :=
  by
  contrapose! hf
  obtain ⟨c, hc⟩ := (f.differentiable.inv hf).exists_const_forall_eq_of_bounded _
  · obtain rfl : f = C c⁻¹ := Polynomial.funext fun z => by rw [eval_C, ← hc z, inv_inv]
    exact degree_C_le
  · obtain ⟨z₀, h₀⟩ := f.exists_forall_norm_le
    simp only [bounded_iff_forall_norm_le, Set.forall_range_iff, norm_inv]
    exact ⟨‖eval z₀ f‖⁻¹, fun z => inv_le_inv_of_le (norm_pos_iff.2 <| hf z₀) (h₀ z)⟩
#align complex.exists_root Complex.exists_root
-/

#print Complex.isAlgClosed /-
instance isAlgClosed : IsAlgClosed ℂ :=
  IsAlgClosed.of_exists_root _ fun p _ hp => Complex.exists_root <| degree_pos_of_irreducible hp
#align complex.is_alg_closed Complex.isAlgClosed
-/

end Complex

