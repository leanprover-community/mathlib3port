/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import LinearAlgebra.Dimension
import LinearAlgebra.FreeModule.Basic
import RingTheory.Finiteness

#align_import linear_algebra.free_module.finite.basic from "leanprover-community/mathlib"@"25a9423c6b2c8626e91c688bfd6c1d0a986a3e6e"

/-!
# Finite and free modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
noncomputable instance [Nontrivial R] [Module.Finite R M] :
    Fintype (Module.Free.ChooseBasisIndex R M) :=
  by
  obtain ⟨h⟩ := id ‹Module.Finite R M›
  choose s hs using h
  exact basis_finite_of_finite_spans (↑s) hs (choose_basis _ _)

end Ring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

variable {R}

#print Module.Finite.of_basis /-
/-- A free module with a basis indexed by a `fintype` is finite. -/
theorem Module.Finite.of_basis {R M ι : Type _} [CommRing R] [AddCommGroup M] [Module R M]
    [Finite ι] (b : Basis ι R M) : Module.Finite R M :=
  by
  cases nonempty_fintype ι
  classical
  refine' ⟨⟨finset.univ.image b, _⟩⟩
  simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]
#align module.finite.of_basis Module.Finite.of_basis
-/

#print Module.Finite.matrix /-
instance Module.Finite.matrix {ι₁ ι₂ : Type _} [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) :=
  by
  cases nonempty_fintype ι₁; cases nonempty_fintype ι₂
  exact Module.Finite.of_basis (Pi.basis fun i => Pi.basisFun R _)
#align module.finite.matrix Module.Finite.matrix
-/

end CommRing

end Module.Free

