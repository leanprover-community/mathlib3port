/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module measure_theory.measure.haar_of_basis
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.MeasureTheory.Measure.Haar
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
nonempty interior.
* `basis.add_haar` is the Lebesgue measure associated to a basis, giving measure `1` to the
corresponding parallelepiped.

In particular, we declare a `measure_space` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure FiniteDimensional

open BigOperators

noncomputable section

variable {ι ι' E F : Type _} [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The closed parallelepiped spanned by a finite family of vectors. -/
def parallelepiped (v : ι → E) : Set E :=
  (fun t : ι → ℝ => ∑ i, t i • v i) '' Icc 0 1
#align parallelepiped parallelepiped

theorem mem_parallelepiped_iff (v : ι → E) (x : E) :
    x ∈ parallelepiped v ↔ ∃ (t : ι → ℝ)(ht : t ∈ Icc (0 : ι → ℝ) 1), x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]
#align mem_parallelepiped_iff mem_parallelepiped_iff

theorem image_parallelepiped (f : E →ₗ[ℝ] F) (v : ι → E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, LinearMap.map_sum, LinearMap.map_smulₛₗ, RingHom.id_apply]
#align image_parallelepiped image_parallelepiped

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
theorem parallelepiped_comp_equiv (v : ι → E) (e : ι' ≃ ι) :
    parallelepiped (v ∘ e) = parallelepiped v := by
  simp only [parallelepiped]
  let K : (ι' → ℝ) ≃ (ι → ℝ) := Equiv.piCongrLeft' (fun a : ι' => ℝ) e
  have : Icc (0 : ι → ℝ) 1 = K '' Icc (0 : ι' → ℝ) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Equiv.Pi_congr_left'_apply,
      Pi.one_apply]
    refine'
      ⟨fun h => ⟨fun i => _, fun i => _⟩, fun h =>
        ⟨fun i => h.1 (e.symm i), fun i => h.2 (e.symm i)⟩⟩
    · simpa only [Equiv.symm_apply_apply] using h.1 (e i)
    · simpa only [Equiv.symm_apply_apply] using h.2 (e i)
  rw [this, ← image_comp]
  congr 1 with x
  simpa only [OrthonormalBasis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.Pi_congr_left'_apply, Equiv.apply_symm_apply] using
    (e.symm.sum_comp fun i : ι' => x i • v (e i)).symm
#align parallelepiped_comp_equiv parallelepiped_comp_equiv

-- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`.
theorem parallelepiped_orthonormal_basis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0 := by
  have e : ι ≃ Fin 1 := by 
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.to_basis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  rw [← B]
  let F : ℝ → Fin 1 → ℝ := fun t => fun i => t
  have A : Icc (0 : Fin 1 → ℝ) 1 = F '' Icc (0 : ℝ) 1 := by
    apply subset.antisymm
    · intro x hx
      refine' ⟨x 0, ⟨hx.1 0, hx.2 0⟩, _⟩
      ext j
      simp only [Subsingleton.elim j 0]
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨fun j => hy.1, fun j => hy.2⟩
  rcases orthonormal_basis_one_dim (b.reindex e) with (H | H)
  · left
    simp only [H, parallelepiped, Algebra.id.smul_eq_mul, mul_one, A, Finset.sum_singleton, ←
      image_comp, image_id', Finset.univ_unique]
  · right
    simp only [H, parallelepiped, Algebra.id.smul_eq_mul, mul_one]
    rw [A]
    simp only [← image_comp, mul_neg, mul_one, Finset.sum_singleton, image_neg, preimage_neg_Icc,
      neg_zero, Finset.univ_unique]
#align parallelepiped_orthonormal_basis_one_dim parallelepiped_orthonormal_basis_one_dim

end AddCommGroup

section NormedSpace

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The parallelepiped spanned by a basis, as a compact set with nonempty interior. -/
def Basis.parallelepiped (b : Basis ι ℝ E) :
    PositiveCompacts E where 
  carrier := parallelepiped b
  is_compact' :=
    is_compact_Icc.image
      (continuous_finset_sum Finset.univ fun (i : ι) (H : i ∈ Finset.univ) =>
        (continuous_apply i).smul continuous_const)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equiv_funL.symm.to_homeomorph '' Icc 0 1))
    · dsimp only [parallelepiped]
      convert H
      ext t
      exact (b.equiv_fun_symm_apply t).symm
    have A : Set.Nonempty (interior (Icc (0 : ι → ℝ) 1)) := by
      rw [← pi_univ_Icc, interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, nonempty_image_iff]
#align basis.parallelepiped Basis.parallelepiped

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def Basis.addHaar (b : Basis ι ℝ E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped
#align basis.add_haar Basis.addHaar

instance isAddHaarMeasureBasisAddHaar (b : Basis ι ℝ E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]
  exact measure.is_add_haar_measure_add_haar_measure _
#align is_add_haar_measure_basis_add_haar isAddHaarMeasureBasisAddHaar

theorem Basis.add_haar_self (b : Basis ι ℝ E) : b.addHaar (parallelepiped b) = 1 := by
  rw [Basis.addHaar]
  exact add_haar_measure_self
#align basis.add_haar_self Basis.add_haar_self

end NormedSpace

/-- A finite dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormal_basis.volume_parallelepiped`. -/
instance (priority := 100) measureSpaceOfInnerProductSpace [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis ℝ E).toBasis.addHaar
#align measure_space_of_inner_product_space measureSpaceOfInnerProductSpace

/- This instance should not be necessary, but Lean has difficulties to find it in product
situations if we do not declare it explicitly. -/
instance Real.measureSpace : MeasureSpace ℝ := by infer_instance
#align real.measure_space Real.measureSpace

