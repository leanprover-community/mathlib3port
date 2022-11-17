/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathbin.LinearAlgebra.FreeModule.Basic
import Mathbin.RingTheory.Finiteness

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `module.free.choose_basis_index.fintype` : If a free module is finite, then any basis is
  finite.
* `module.free.linear_map.free ` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.free.linear_map.module.finite` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

namespace Module.Free

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [Module.Free R M]

/-- If a free module is finite, then any basis is finite. -/
noncomputable instance [Nontrivial R] [Module.Finite R M] : Fintype (Module.Free.ChooseBasisIndex R M) := by
  obtain ⟨h⟩ := id ‹Module.Finite R M›
  choose s hs using h
  exact basisFintypeOfFiniteSpans (↑s) hs (choose_basis _ _)

end Ring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

variable {R}

/-- A free module with a basis indexed by a `fintype` is finite. -/
theorem _root_.module.finite.of_basis {R M ι : Type _} [CommRing R] [AddCommGroup M] [Module R M] [Finite ι]
    (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
  refine' ⟨⟨finset.univ.image b, _⟩⟩
  simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]
#align module.free._root_.module.finite.of_basis module.free._root_.module.finite.of_basis

instance _root_.module.finite.matrix {ι₁ ι₂ : Type _} [Finite ι₁] [Finite ι₂] : Module.Finite R (Matrix ι₁ ι₂ R) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
  exact Module.Finite.of_basis (Pi.basis $ fun i => Pi.basisFun R _)
#align module.free._root_.module.finite.matrix module.free._root_.module.finite.matrix

end CommRing

end Module.Free

