/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module linear_algebra.multilinear.finite_dimensional
! leanprover-community/mathlib commit 7c523cb78f4153682c2929e3006c863bfef463d0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Multilinear.Basic
import Mathbin.LinearAlgebra.FreeModule.Finite.Matrix

/-! # Multilinear maps over finite dimensional spaces

The main results are that multilinear maps over finitely-generated, free modules are
finitely-generated and free.

* `module.finite.multilinear_map`
* `module.free.multilinear_map`

We do not put this in `linear_algebra/multilinear_map/basic` to avoid making the imports too large
there.
-/


namespace MultilinearMap

variable {ι R M₂ : Type _} {M₁ : ι → Type _}

variable [DecidableEq ι] [Finite ι]

variable [CommRing R] [AddCommGroup M₂] [Module R M₂]

variable [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]

variable [Module.Finite R M₂] [Module.Free R M₂]

variable [∀ i, Module.Finite R (M₁ i)] [∀ i, Module.Free R (M₁ i)]

-- the induction requires us to show both at once
private theorem free_and_finite :
    Module.Free R (MultilinearMap R M₁ M₂) ∧ Module.Finite R (MultilinearMap R M₁ M₂) :=
  by
  -- the `fin n` case is sufficient
  suffices
    ∀ (n) (N : Fin n → Type _) [∀ i, AddCommGroup (N i)],
      ∀ [∀ i, Module R (N i)],
        ∀ [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)],
          Module.Free R (MultilinearMap R N M₂) ∧ Module.Finite R (MultilinearMap R N M₂)
    by
    cases nonempty_fintype ι
    cases this _ (M₁ ∘ (Fintype.equivFin ι).symm)
    have e := dom_dom_congr_linear_equiv' R M₁ M₂ (Fintype.equivFin ι)
    exact ⟨Module.Free.ofEquiv e.symm, Module.Finite.equiv e.symm⟩
  intro n N _ _ _ _
  induction' n with n ih
  ·
    exact
      ⟨Module.Free.ofEquiv (const_linear_equiv_of_is_empty R N M₂),
        Module.Finite.equiv (const_linear_equiv_of_is_empty R N M₂)⟩
  · suffices
      Module.Free R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) ∧
        Module.Finite R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂)
      by
      cases this
      exact
        ⟨Module.Free.ofEquiv (multilinearCurryLeftEquiv R N M₂),
          Module.Finite.equiv (multilinearCurryLeftEquiv R N M₂)⟩
    cases ih fun i => N i.succ
    exact ⟨Module.Free.linearMap _ _ _, Module.Finite.linearMap _ _⟩
#align multilinear_map.free_and_finite multilinear_map.free_and_finite

instance Module.Finite.multilinearMap : Module.Finite R (MultilinearMap R M₁ M₂) :=
  free_and_finite.2
#align module.finite.multilinear_map Module.Finite.multilinearMap

instance Module.Free.multilinearMap : Module.Free R (MultilinearMap R M₁ M₂) :=
  free_and_finite.1
#align module.free.multilinear_map Module.Free.multilinearMap

end MultilinearMap

