/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import LinearAlgebra.QuadraticForm.Basic
import Algebra.CharP.Two
import Data.ZMod.Basic

#align_import quadratic_form from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# `quadratic_form R M` and `subtype bilin_form.is_symm` are distinct notions in characteristic 2

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The main result of this file is `bilin_form.not_inj_on_to_quadratic_form_is_symm`.

The counterexample we use is $B (x, y) (x', y') ↦ xy' + x'y$ where `x y x' y' : zmod 2`.
-/


variable (F : Type _) [Nontrivial F] [CommRing F] [CharP F 2]

open BilinForm

namespace Counterexample

/-- The bilinear form we will use as a counterexample, over some field `F` of characteristic two. -/
def b : BilinForm F (F × F) :=
  LinearMap.BilinForm.linMulLin (LinearMap.fst _ _ _) (LinearMap.snd _ _ _) +
    LinearMap.BilinForm.linMulLin (LinearMap.snd _ _ _) (LinearMap.fst _ _ _)
#align counterexample.B Counterexample.b

@[simp]
theorem b_apply (x y : F × F) : b F x y = x.1 * y.2 + x.2 * y.1 :=
  rfl
#align counterexample.B_apply Counterexample.b_apply

theorem isSymm_b : (b F).IsSymm := fun x y => by simp [mul_comm, add_comm]
#align counterexample.is_symm_B Counterexample.isSymm_b

theorem isAlt_b : (b F).IsAlt := fun x => by simp [mul_comm, CharTwo.add_self_eq_zero (x.1 * x.2)]
#align counterexample.is_alt_B Counterexample.isAlt_b

theorem b_ne_zero : b F ≠ 0 := fun h => by simpa using LinearMap.BilinForm.congr_fun h (1, 0) (1, 1)
#align counterexample.B_ne_zero Counterexample.b_ne_zero

/-- `bilin_form.to_quadratic_form` is not injective on symmetric bilinear forms.

This disproves a weaker version of `quadratic_form.associated_left_inverse`.
-/
theorem BilinForm.not_injOn_toQuadraticForm_isSymm.{u} :
    ¬∀ {R M : Type u} [Semiring R] [AddCommMonoid M],
        ∀ [Module R M],
          Set.InjOn (to_quadratic_form : BilinForm R M → QuadraticForm R M) {B | B.IsSymm} :=
  by
  intro h
  let F := ULift.{u} (ZMod 2)
  apply B_ne_zero F
  apply h (is_symm_B F) is_symm_zero
  rw [LinearMap.BilinForm.toQuadraticForm_zero, LinearMap.BilinForm.toQuadraticForm_eq_zero]
  exact is_alt_B F
#align counterexample.bilin_form.not_inj_on_to_quadratic_form_is_symm Counterexample.BilinForm.not_injOn_toQuadraticForm_isSymm

end Counterexample

