/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module linear_algebra.free_module.finite.matrix
! leanprover-community/mathlib commit 1f0096e6caa61e9c849ec2adbd227e960e9dff58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Finrank
import Mathbin.LinearAlgebra.FreeModule.Finite.Basic
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!
# Finite and free modules using matrices

We provide some instances for finite and free modules involving matrices.

## Main results

* `module.free.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N` is free.
* `module.finite.of_basis` : A free module with a basis indexed by a `fintype` is finite.
* `module.finite.linear_map` : if `M` and `N` are finite and free, then `M →ₗ[R] N`
  is finite.
-/


universe u v w

variable (R : Type u) (M : Type v) (N : Type w)

namespace Module.Free

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N]

instance linearMap [Module.Finite R M] [Module.Finite R N] : Module.Free R (M →ₗ[R] N) :=
  by
  cases subsingleton_or_nontrivial R
  · apply Module.Free.ofSubsingleton'
  classical exact
      of_equiv (LinearMap.toMatrix (Module.Free.chooseBasis R M) (Module.Free.chooseBasis R N)).symm
#align module.free.linear_map Module.Free.linearMap

variable {R}

instance Module.Finite.linearMap [Module.Finite R M] [Module.Finite R N] :
    Module.Finite R (M →ₗ[R] N) :=
  by
  cases subsingleton_or_nontrivial R
  · infer_instance
  classical
    have f := (LinearMap.toMatrix (choose_basis R M) (choose_basis R N)).symm
    exact Module.Finite.ofSurjective f.to_linear_map (LinearEquiv.surjective f)
#align module.finite.linear_map Module.Finite.linearMap

end CommRing

section Integer

variable [AddCommGroup M] [Module.Finite ℤ M] [Module.Free ℤ M]

variable [AddCommGroup N] [Module.Finite ℤ N] [Module.Free ℤ N]

instance Module.Finite.addMonoidHom : Module.Finite ℤ (M →+ N) :=
  Module.Finite.equiv (addMonoidHomLequivInt ℤ).symm
#align module.finite.add_monoid_hom Module.Finite.addMonoidHom

instance addMonoidHom : Module.Free ℤ (M →+ N) :=
  letI : Module.Free ℤ (M →ₗ[ℤ] N) := Module.Free.linearMap _ _ _
  Module.Free.ofEquiv (addMonoidHomLequivInt ℤ).symm
#align module.free.add_monoid_hom Module.Free.addMonoidHom

end Integer

section CommRing

open FiniteDimensional

variable [CommRing R] [StrongRankCondition R]

variable [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

variable [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

--TODO: this should follow from `linear_equiv.finrank_eq`, that is over a field.
/-- The finrank of `M →ₗ[R] N` is `(finrank R M) * (finrank R N)`. -/
theorem finrank_linear_hom : finrank R (M →ₗ[R] N) = finrank R M * finrank R N := by
  classical
    letI := nontrivial_of_invariantBasisNumber R
    have h := LinearMap.toMatrix (choose_basis R M) (choose_basis R N)
    let b := (Matrix.stdBasis _ _ _).map h.symm
    rw [finrank, dim_eq_card_basis b, ← Cardinal.mk_fintype, Cardinal.mk_toNat_eq_card, finrank,
      finrank, rank_eq_card_choose_basis_index, rank_eq_card_choose_basis_index,
      Cardinal.mk_toNat_eq_card, Cardinal.mk_toNat_eq_card, Fintype.card_prod, mul_comm]
#align module.free.finrank_linear_hom Module.Free.finrank_linear_hom

end CommRing

end Module.Free

