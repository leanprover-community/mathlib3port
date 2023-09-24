/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import NumberTheory.ModularForms.JacobiTheta.Basic
import Analysis.Complex.UpperHalfPlane.Manifold

#align_import number_theory.modular_forms.jacobi_theta.manifold from "leanprover-community/mathlib"@"728ef9dbb281241906f25cbeb30f90d83e0bb451"

/-!
# Manifold differentiability of the Jacobi's theta function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we reformulate differentiability of the Jacobi's theta function in terms of manifold
differentiability.

## TODO

Prove smoothness (in terms of `smooth`).
-/


open scoped UpperHalfPlane Manifold

#print mdifferentiable_jacobiTheta /-
theorem mdifferentiable_jacobiTheta : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (jacobiTheta ∘ coe : ℍ → ℂ) :=
  fun τ => (differentiableAt_jacobiTheta τ.2).MDifferentiableAt.comp τ τ.mdifferentiable_coe
#align mdifferentiable_jacobi_theta mdifferentiable_jacobiTheta
-/

