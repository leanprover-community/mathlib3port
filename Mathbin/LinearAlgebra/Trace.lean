/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.Matrix.Trace
import Mathbin.LinearAlgebra.Contraction
import Mathbin.LinearAlgebra.TensorProductBasis
import Mathbin.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `linear_algebra/matrix/trace.lean` for the trace of a matrix.

## Tags

linear_map, trace, diagonal

-/


noncomputable section

universe u v w

namespace LinearMap

open BigOperators

open Matrix

open FiniteDimensional

section

variable (R : Type u) [CommRingₓ R] {M : Type v} [AddCommGroupₓ M] [Module R M]

variable {ι : Type w} [DecidableEq ι] [Fintype ι]

variable {κ : Type _} [DecidableEq κ] [Fintype κ]

variable (b : Basis ι R M) (c : Basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def traceAux : (M →ₗ[R] M) →ₗ[R] R :=
  Matrix.trace ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

-- Can't be `simp` because it would cause a loop.
theorem trace_aux_def (b : Basis ι R M) (f : M →ₗ[R] M) :
    traceAux R b f = Matrix.trace ι R R (LinearMap.toMatrix b b f) :=
  rfl

theorem trace_aux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace ι R R (LinearMap.toMatrix b b f) =
          Matrix.trace ι R R (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) :=
        by
        rw [LinearMap.id_comp, LinearMap.comp_id]
      _ =
          Matrix.trace ι R R
            (LinearMap.toMatrix c b LinearMap.id ⬝ LinearMap.toMatrix c c f ⬝ LinearMap.toMatrix b c LinearMap.id) :=
        by
        rw [LinearMap.to_matrix_comp _ c, LinearMap.to_matrix_comp _ c]
      _ =
          Matrix.trace κ R R
            (LinearMap.toMatrix c c f ⬝ LinearMap.toMatrix b c LinearMap.id ⬝ LinearMap.toMatrix c b LinearMap.id) :=
        by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
      _ = Matrix.trace κ R R (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.to_matrix_comp _ b, LinearMap.to_matrix_comp _ c]
      _ = Matrix.trace κ R R (LinearMap.toMatrix c c f) := by
        rw [LinearMap.comp_id, LinearMap.comp_id]
      

open Classical

variable (R) (M)

/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then traceAux R H.some_spec.some else 0

variable (R) {M}

/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M →ₗ[R] M) :
    trace R M f = Matrix.trace s R R (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace, dif_pos this, ← trace_aux_def]
  congr 1
  apply trace_aux_eq

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) : trace R M f = Matrix.trace ι R R (LinearMap.toMatrix b b f) := by
  rw [trace_eq_matrix_trace_of_finset R b.reindex_finset_range, ← trace_aux_def, ← trace_aux_def, trace_aux_eq R b]

theorem trace_mul_comm (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) :=
  if H : ∃ s : Finset M, Nonempty (Basis s R M) then by
    let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.to_matrix_mul]
    apply Matrix.trace_mul_comm
  else by
    rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj (g : M →ₗ[R] M) (f : (M →ₗ[R] M)ˣ) : trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
theorem trace_conj' (f g : M →ₗ[R] M) [Invertible f] : trace R M (f * g * ⅟ f) = trace R M g := by
  rw [trace_mul_comm]
  simp

end

section

variable (R : Type u) [CommRingₓ R] {M : Type v} [AddCommGroupₓ M] [Module R M]

variable {ι : Type w} [Fintype ι]

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract_of_basis (b : Basis ι R M) : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  by
  classical
  apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
  rintro ⟨i, j⟩
  simp only [Function.comp_app, Basis.tensor_product_apply, Basis.coe_dual_basis, coe_comp]
  rw [trace_eq_matrix_trace R b, to_matrix_dual_tensor_hom]
  by_cases' hij : i = j
  · rw [hij]
    simp
    
  rw [Matrix.stdBasisMatrix.trace_zero j i (1 : R) hij]
  simp [Finsupp.single_eq_pi_single, hij]

/-- The trace of a linear map correspond to the contraction pairing under the isomorphism
 `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract_of_basis' [DecidableEq ι] (b : Basis ι R M) :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.toLinearMap := by
  simp [LinearEquiv.eq_comp_to_linear_map_symm, trace_eq_contract_of_basis R b]

variable [Module.Free R M] [Module.Finite R M] [Nontrivial R]

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
@[simp]
theorem trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  trace_eq_contract_of_basis R (Module.Free.chooseBasis R M)

open Classical

/-- When `M` is finite free, the trace of a linear map correspond to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`-/
theorem trace_eq_contract' : LinearMap.trace R M = contractLeft R M ∘ₗ dualTensorHomEquiv.symm.toLinearMap :=
  trace_eq_contract_of_basis' R (Module.Free.chooseBasis R M)

/-- The trace of the identity endomorphism is the dimension of the free module -/
@[simp]
theorem trace_one : trace R M 1 = (finrank R M : R) := by
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b, to_matrix_one, Module.Free.finrank_eq_card_choose_basis_index]
  simp

end

end LinearMap

