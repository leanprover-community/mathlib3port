/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
import Algebra.Algebra.Spectrum
import LinearAlgebra.GeneralLinearGroup
import LinearAlgebra.FiniteDimensional.Defs

#align_import linear_algebra.eigenspace.basic from "leanprover-community/mathlib"@"6b31d1eebd64eab86d5bd9936bfaada6ca8b5842"

/-!
# Eigenvectors and eigenvalues

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines eigenspaces, eigenvalues, and eigenvalues, as well as their generalized
counterparts. We follow Axler's approach [axler2015] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`has_eigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

The fact that the eigenvalues are the roots of the minimal polynomial is proved in
`linear_algebra.eigenspace.minpoly`.

The existence of eigenvalues over an algebraically closed field
(and the fact that the generalized eigenspaces then span) is deferred to
`linear_algebra.eigenspace.is_alg_closed`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2015]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/


universe u v w

namespace Module

namespace End

open FiniteDimensional

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

#print Module.End.eigenspace /-
/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
    such that `f x = μ • x`. (Def 5.36 of [axler2015])-/
def eigenspace (f : End R M) (μ : R) : Submodule R M :=
  (f - algebraMap R (End R M) μ).ker
#align module.End.eigenspace Module.End.eigenspace
-/

#print Module.End.eigenspace_zero /-
@[simp]
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = f.ker := by simp [eigenspace]
#align module.End.eigenspace_zero Module.End.eigenspace_zero
-/

#print Module.End.HasEigenvector /-
/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.7 of [axler2015]) -/
def HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  x ∈ eigenspace f μ ∧ x ≠ 0
#align module.End.has_eigenvector Module.End.HasEigenvector
-/

#print Module.End.HasEigenvalue /-
/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
    such that `f x = μ • x`. (Def 5.5 of [axler2015]) -/
def HasEigenvalue (f : End R M) (a : R) : Prop :=
  eigenspace f a ≠ ⊥
#align module.End.has_eigenvalue Module.End.HasEigenvalue
-/

#print Module.End.Eigenvalues /-
/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
def Eigenvalues (f : End R M) : Type _ :=
  { μ : R // f.HasEigenvalue μ }
#align module.End.eigenvalues Module.End.Eigenvalues
-/

instance (f : End R M) : Coe f.Eigenvalues R :=
  coeSubtype

#print Module.End.hasEigenvalue_of_hasEigenvector /-
theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ := by
  rw [has_eigenvalue, Submodule.ne_bot_iff]
  use x; exact h
#align module.End.has_eigenvalue_of_has_eigenvector Module.End.hasEigenvalue_of_hasEigenvector
-/

#print Module.End.mem_eigenspace_iff /-
theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x := by
  rw [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, algebra_map_End_apply, sub_eq_zero]
#align module.End.mem_eigenspace_iff Module.End.mem_eigenspace_iff
-/

#print Module.End.HasEigenvector.apply_eq_smul /-
theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) :
    f x = μ • x :=
  mem_eigenspace_iff.mp hx.1
#align module.End.has_eigenvector.apply_eq_smul Module.End.HasEigenvector.apply_eq_smul
-/

#print Module.End.HasEigenvalue.exists_hasEigenvector /-
theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ
#align module.End.has_eigenvalue.exists_has_eigenvector Module.End.HasEigenvalue.exists_hasEigenvector
-/

#print Module.End.HasEigenvalue.mem_spectrum /-
theorem Module.End.HasEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) :
    μ ∈ spectrum R f := by
  refine' spectrum.mem_iff.mpr fun h_unit => _
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_has_eigenvector with ⟨v, hv⟩
  refine' hv.2 ((linear_map.ker_eq_bot'.mp f'.ker) v (_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul, sub_self]
#align module.End.mem_spectrum_of_has_eigenvalue Module.End.HasEigenvalue.mem_spectrum
-/

#print Module.End.hasEigenvalue_iff_mem_spectrum /-
theorem hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ ∈ spectrum K f :=
  Iff.intro Module.End.HasEigenvalue.mem_spectrum fun h => by
    rwa [spectrum.mem_iff, IsUnit.sub_iff, LinearMap.isUnit_iff_ker_eq_bot] at h
#align module.End.has_eigenvalue_iff_mem_spectrum Module.End.hasEigenvalue_iff_mem_spectrum
-/

#print Module.End.eigenspace_div /-
theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = (b • f - algebraMap K (End K V) a).ker :=
  calc
    eigenspace f (a / b) = eigenspace f (b⁻¹ * a) := by rw [div_eq_mul_inv, mul_comm]
    _ = (f - (b⁻¹ * a) • LinearMap.id).ker := rfl
    _ = (f - b⁻¹ • a • LinearMap.id).ker := by rw [smul_smul]
    _ = (f - b⁻¹ • algebraMap K (End K V) a).ker := rfl
    _ = (b • (f - b⁻¹ • algebraMap K (End K V) a)).ker := by rw [LinearMap.ker_smul _ b hb]
    _ = (b • f - algebraMap K (End K V) a).ker := by rw [smul_sub, smul_inv_smul₀ hb]
#align module.End.eigenspace_div Module.End.eigenspace_div
-/

#print Module.End.eigenspaces_independent /-
/-- The eigenspaces of a linear operator form an independent family of subspaces of `V`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
theorem eigenspaces_independent (f : End K V) : CompleteLattice.Independent f.eigenspace := by
  classical
  -- Define an operation from `Π₀ μ : K, f.eigenspace μ`, the vector space of of finitely-supported
  -- choices of an eigenvector from each eigenspace, to `V`, by sending a collection to its sum.
  let S :
    @LinearMap K K _ _ (RingHom.id K) (Π₀ μ : K, f.eigenspace μ) V
      (@DFinsupp.addCommMonoid K (fun μ => f.eigenspace μ) _) _
      (@DFinsupp.module K _ (fun μ => f.eigenspace μ) _ _ _) _ :=
    @DFinsupp.lsum K K ℕ _ V _ _ _ _ _ _ _ _ _ fun μ => (f.eigenspace μ).Subtype
  -- We need to show that if a finitely-supported collection `l` of representatives of the
  -- eigenspaces has sum `0`, then it itself is zero.
  suffices ∀ l : Π₀ μ, f.eigenspace μ, S l = 0 → l = 0
    by
    rw [CompleteLattice.independent_iff_dfinsupp_lsum_injective]
    change Function.Injective S
    rw [←
      @LinearMap.ker_eq_bot K K (Π₀ μ, f.eigenspace μ) V _ _
        (@DFinsupp.addCommGroup K (fun μ => f.eigenspace μ) _)]
    rw [eq_bot_iff]
    exact this
  intro l hl
  -- We apply induction on the finite set of eigenvalues from which `l` selects a nonzero
  -- eigenvector, i.e. on the support of `l`.
  induction' h_l_support : l.support using Finset.induction with μ₀ l_support' hμ₀ ih generalizing l
  -- If the support is empty, all coefficients are zero and we are done.
  · exact DFinsupp.support_eq_empty.1 h_l_support
  -- Now assume that the support of `l` contains at least one eigenvalue `μ₀`. We define a new
  -- collection of representatives `l'` to apply the induction hypothesis on later. The collection
  -- of representatives `l'` is derived from `l` by multiplying the coefficient of the eigenvector
  -- with eigenvalue `μ` by `μ - μ₀`.
  · let l' :=
      DFinsupp.mapRange.linearMap (fun μ => (μ - μ₀) • @LinearMap.id K (f.eigenspace μ) _ _ _) l
    -- The support of `l'` is the support of `l` without `μ₀`.
    have h_l_support' : l'.support = l_support' :=
      by
      rw [← Finset.erase_insert hμ₀, ← h_l_support]
      ext a
      have : ¬(a = μ₀ ∨ l a = 0) ↔ ¬a = μ₀ ∧ ¬l a = 0 := not_or
      simp only [l', DFinsupp.mapRange.linearMap_apply, DFinsupp.mapRange_apply,
        DFinsupp.mem_support_iff, Finset.mem_erase, id.def, LinearMap.id_coe, LinearMap.smul_apply,
        Ne.def, smul_eq_zero, sub_eq_zero, this]
    -- The entries of `l'` add up to `0`.
    have total_l' : S l' = 0 := by
      let g := f - algebraMap K (End K V) μ₀
      let a : Π₀ μ : K, V := DFinsupp.mapRange.linearMap (fun μ => (f.eigenspace μ).Subtype) l
      calc
        S l' =
            DFinsupp.lsum ℕ (fun μ => (f.eigenspace μ).Subtype.comp ((μ - μ₀) • LinearMap.id)) l :=
          _
        _ = DFinsupp.lsum ℕ (fun μ => g.comp (f.eigenspace μ).Subtype) l := _
        _ = DFinsupp.lsum ℕ (fun μ => g) a := _
        _ = g (DFinsupp.lsum ℕ (fun μ => (LinearMap.id : V →ₗ[K] V)) a) := _
        _ = g (S l) := _
        _ = 0 := by rw [hl, g.map_zero]
      · exact DFinsupp.sum_mapRange_index.linearMap
      · congr
        ext μ v
        simp only [g, eq_self_iff_true, Function.comp_apply, id.def, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply,
          sub_left_inj, sub_smul, Submodule.coe_smul_of_tower, Submodule.coe_sub,
          Submodule.subtype_apply, mem_eigenspace_iff.1 v.prop]
      · rw [DFinsupp.sum_mapRange_index.linearMap]
      ·
        simp only [DFinsupp.sumAddHom_apply, LinearMap.id_coe, map_dfinsupp_sum, id.def,
          LinearMap.toAddMonoidHom_coe, DFinsupp.lsum_apply_apply]
      · congr
        simp only [S, a, DFinsupp.sum_mapRange_index.linearMap, LinearMap.id_comp]
    -- Therefore, by the induction hypothesis, all entries of `l'` are zero.
    have l'_eq_0 := ih l' total_l' h_l_support'
    -- By the definition of `l'`, this means that `(μ - μ₀) • l μ = 0` for all `μ`.
    have h_smul_eq_0 : ∀ μ, (μ - μ₀) • l μ = 0 :=
      by
      intro μ
      calc
        (μ - μ₀) • l μ = l' μ := by
          simp only [l', LinearMap.id_coe, id.def, LinearMap.smul_apply, DFinsupp.mapRange_apply,
            DFinsupp.mapRange.linearMap_apply]
        _ = 0 := by rw [l'_eq_0]; rfl
    -- Thus, the eigenspace-representatives in `l` for all `μ ≠ μ₀` are `0`.
    have h_lμ_eq_0 : ∀ μ : K, μ ≠ μ₀ → l μ = 0 :=
      by
      intro μ hμ
      apply Classical.or_iff_not_imp_left.1 (smul_eq_zero.1 (h_smul_eq_0 μ))
      rwa [sub_eq_zero]
    -- So if we sum over all these representatives, we obtain `0`.
    have h_sum_l_support'_eq_0 : (Finset.sum l_support' fun μ => (l μ : V)) = 0 :=
      by
      rw [← Finset.sum_const_zero]
      apply Finset.sum_congr rfl
      intro μ hμ
      rw [Submodule.coe_eq_zero, h_lμ_eq_0]
      rintro rfl
      exact hμ₀ hμ
    -- The only potentially nonzero eigenspace-representative in `l` is the one corresponding to
    -- `μ₀`. But since the overall sum is `0` by assumption, this representative must also be `0`.
    have : l μ₀ = 0 :=
      by
      simp only [S, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply,
        LinearMap.toAddMonoidHom_coe, DFinsupp.sum, h_l_support, Submodule.subtype_apply,
        Submodule.coe_eq_zero, Finset.sum_insert hμ₀, h_sum_l_support'_eq_0, add_zero] at hl
      exact hl
    -- Thus, all coefficients in `l` are `0`.
    show l = 0
    · ext μ
      by_cases h_cases : μ = μ₀
      · rwa [h_cases, SetLike.coe_eq_coe, DFinsupp.coe_zero, Pi.zero_apply]
      exact congr_arg (coe : _ → V) (h_lμ_eq_0 μ h_cases)
#align module.End.eigenspaces_independent Module.End.eigenspaces_independent
-/

#print Module.End.eigenvectors_linearIndependent /-
/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
    independent. (Lemma 5.10 of [axler2015])

    We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
    eigenvalue in the image of `xs`. -/
theorem eigenvectors_linearIndependent (f : End K V) (μs : Set K) (xs : μs → V)
    (h_eigenvec : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent K xs :=
  CompleteLattice.Independent.linearIndependent _
    (f.eigenspaces_independent.comp Subtype.coe_injective) (fun μ => (h_eigenvec μ).1) fun μ =>
    (h_eigenvec μ).2
#align module.End.eigenvectors_linear_independent Module.End.eigenvectors_linearIndependent
-/

#print Module.End.genEigenspace /-
/-- The generalized eigenspace for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
kernel of `(f - μ • id) ^ k`. (Def 8.10 of [axler2015]). Furthermore, a generalized eigenspace for
some exponent `k` is contained in the generalized eigenspace for exponents larger than `k`. -/
def genEigenspace (f : End R M) (μ : R) : ℕ →o Submodule R M
    where
  toFun k := ((f - algebraMap R (End R M) μ) ^ k).ker
  monotone' k m hm := by
    simp only [← pow_sub_mul_pow _ hm]
    exact
      LinearMap.ker_le_ker_comp ((f - algebraMap R (End R M) μ) ^ k)
        ((f - algebraMap R (End R M) μ) ^ (m - k))
#align module.End.generalized_eigenspace Module.End.genEigenspace
-/

#print Module.End.mem_genEigenspace /-
@[simp]
theorem mem_genEigenspace (f : End R M) (μ : R) (k : ℕ) (m : M) :
    m ∈ f.genEigenspace μ k ↔ ((f - μ • 1) ^ k) m = 0 :=
  Iff.rfl
#align module.End.mem_generalized_eigenspace Module.End.mem_genEigenspace
-/

#print Module.End.genEigenspace_zero /-
@[simp]
theorem genEigenspace_zero (f : End R M) (k : ℕ) : f.genEigenspace 0 k = (f ^ k).ker := by
  simp [Module.End.genEigenspace]
#align module.End.generalized_eigenspace_zero Module.End.genEigenspace_zero
-/

#print Module.End.HasGenEigenvector /-
/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
    (Def 8.9 of [axler2015])-/
def HasGenEigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  x ≠ 0 ∧ x ∈ genEigenspace f μ k
#align module.End.has_generalized_eigenvector Module.End.HasGenEigenvector
-/

#print Module.End.HasGenEigenvalue /-
/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
    are generalized eigenvectors for `f`, `k`, and `μ`. -/
def HasGenEigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  genEigenspace f μ k ≠ ⊥
#align module.End.has_generalized_eigenvalue Module.End.HasGenEigenvalue
-/

#print Module.End.genEigenrange /-
/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ` is the
    range of `(f - μ • id) ^ k`. -/
def genEigenrange (f : End R M) (μ : R) (k : ℕ) : Submodule R M :=
  ((f - algebraMap R (End R M) μ) ^ k).range
#align module.End.generalized_eigenrange Module.End.genEigenrange
-/

#print Module.End.exp_ne_zero_of_hasGenEigenvalue /-
/-- The exponent of a generalized eigenvalue is never 0. -/
theorem exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ} (h : f.HasGenEigenvalue μ k) :
    k ≠ 0 := by
  rintro rfl
  exact h LinearMap.ker_id
#align module.End.exp_ne_zero_of_has_generalized_eigenvalue Module.End.exp_ne_zero_of_hasGenEigenvalue
-/

#print Module.End.maxGenEigenspace /-
/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
def maxGenEigenspace (f : End R M) (μ : R) : Submodule R M :=
  ⨆ k, f.genEigenspace μ k
#align module.End.maximal_generalized_eigenspace Module.End.maxGenEigenspace
-/

#print Module.End.genEigenspace_le_maximal /-
theorem genEigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.genEigenspace μ k ≤ f.maxGenEigenspace μ :=
  le_iSup _ _
#align module.End.generalized_eigenspace_le_maximal Module.End.genEigenspace_le_maximal
-/

#print Module.End.mem_maxGenEigenspace /-
@[simp]
theorem mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maxGenEigenspace μ ↔ ∃ k : ℕ, ((f - μ • 1) ^ k) m = 0 := by
  simp only [maximal_generalized_eigenspace, ← mem_generalized_eigenspace,
    Submodule.mem_iSup_of_chain]
#align module.End.mem_maximal_generalized_eigenspace Module.End.mem_maxGenEigenspace
-/

#print Module.End.maxGenEigenspaceIndex /-
/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
noncomputable def maxGenEigenspaceIndex (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex (f.genEigenspace μ)
#align module.End.maximal_generalized_eigenspace_index Module.End.maxGenEigenspaceIndex
-/

#print Module.End.maxGenEigenspace_eq /-
/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
theorem maxGenEigenspace_eq [h : IsNoetherian R M] (f : End R M) (μ : R) :
    maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ) :=
  by
  rw [isNoetherian_iff_wellFounded] at h
  exact (WellFounded.iSup_eq_monotonicSequenceLimit h (f.generalized_eigenspace μ) : _)
#align module.End.maximal_generalized_eigenspace_eq Module.End.maxGenEigenspace_eq
-/

#print Module.End.hasGenEigenvalue_of_hasGenEigenvalue_of_le /-
/-- A generalized eigenvalue for some exponent `k` is also
    a generalized eigenvalue for exponents larger than `k`. -/
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : ℕ} {m : ℕ}
    (hm : k ≤ m) (hk : f.HasGenEigenvalue μ k) : f.HasGenEigenvalue μ m :=
  by
  unfold has_generalized_eigenvalue at *
  contrapose! hk
  rw [← le_bot_iff, ← hk]
  exact (f.generalized_eigenspace μ).Monotone hm
#align module.End.has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le Module.End.hasGenEigenvalue_of_hasGenEigenvalue_of_le
-/

#print Module.End.eigenspace_le_genEigenspace /-
/-- The eigenspace is a subspace of the generalized eigenspace. -/
theorem eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.genEigenspace μ k :=
  (f.genEigenspace μ).Monotone (Nat.succ_le_of_lt hk)
#align module.End.eigenspace_le_generalized_eigenspace Module.End.eigenspace_le_genEigenspace
-/

#print Module.End.hasGenEigenvalue_of_hasEigenvalue /-
/-- All eigenvalues are generalized eigenvalues. -/
theorem hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k :=
  by
  apply has_generalized_eigenvalue_of_has_generalized_eigenvalue_of_le hk
  rw [has_generalized_eigenvalue, generalized_eigenspace, OrderHom.coe_mk, pow_one]
  exact hμ
#align module.End.has_generalized_eigenvalue_of_has_eigenvalue Module.End.hasGenEigenvalue_of_hasEigenvalue
-/

#print Module.End.hasEigenvalue_of_hasGenEigenvalue /-
/-- All generalized eigenvalues are eigenvalues. -/
theorem hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.HasGenEigenvalue μ k) : f.HasEigenvalue μ :=
  by
  intro contra; apply hμ
  erw [LinearMap.ker_eq_bot] at contra ⊢; rw [LinearMap.coe_pow]
  exact Function.Injective.iterate contra k
#align module.End.has_eigenvalue_of_has_generalized_eigenvalue Module.End.hasEigenvalue_of_hasGenEigenvalue
-/

#print Module.End.hasGenEigenvalue_iff_hasEigenvalue /-
/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
theorem hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ :=
  ⟨hasEigenvalue_of_hasGenEigenvalue, hasGenEigenvalue_of_hasEigenvalue hk⟩
#align module.End.has_generalized_eigenvalue_iff_has_eigenvalue Module.End.hasGenEigenvalue_iff_hasEigenvalue
-/

#print Module.End.genEigenspace_le_genEigenspace_finrank /-
/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
    (Lemma 8.11 of [axler2015]) -/
theorem genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K)
    (k : ℕ) : f.genEigenspace μ k ≤ f.genEigenspace μ (finrank K V) :=
  ker_pow_le_ker_pow_finrank _ _
#align module.End.generalized_eigenspace_le_generalized_eigenspace_finrank Module.End.genEigenspace_le_genEigenspace_finrank
-/

#print Module.End.genEigenspace_eq_genEigenspace_finrank_of_le /-
/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
theorem genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V] (f : End K V) (μ : K)
    {k : ℕ} (hk : finrank K V ≤ k) : f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  ker_pow_eq_ker_pow_finrank_of_le hk
#align module.End.generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le Module.End.genEigenspace_eq_genEigenspace_finrank_of_le
-/

#print Module.End.genEigenspace_restrict /-
/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
    of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
theorem genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    genEigenspace (LinearMap.restrict f hfp) μ k =
      Submodule.comap p.Subtype (f.genEigenspace μ k) :=
  by
  simp only [generalized_eigenspace, OrderHom.coe_mk, ← LinearMap.ker_comp]
  induction' k with k ih
  · rw [pow_zero, pow_zero, LinearMap.one_eq_id]
    apply (Submodule.ker_subtype _).symm
  ·
    erw [pow_succ, pow_succ, LinearMap.ker_comp, LinearMap.ker_comp, ih, ← LinearMap.ker_comp,
      LinearMap.comp_assoc]
#align module.End.generalized_eigenspace_restrict Module.End.genEigenspace_restrict
-/

#print Module.End.eigenspace_restrict_le_eigenspace /-
/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    (μ : R) : (eigenspace (f.restrict hfp) μ).map p.Subtype ≤ f.eigenspace μ :=
  by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg coe hx
#align module.End.eigenspace_restrict_le_eigenspace Module.End.eigenspace_restrict_le_eigenspace
-/

#print Module.End.generalized_eigenvec_disjoint_range_ker /-
/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.genEigenrange μ (finrank K V)) (f.genEigenspace μ (finrank K V)) :=
  by
  have h :=
    calc
      Submodule.comap ((f - algebraMap _ _ μ) ^ finrank K V)
            (f.generalized_eigenspace μ (finrank K V)) =
          ((f - algebraMap _ _ μ) ^ finrank K V *
              (f - algebraMap K (End K V) μ) ^ finrank K V).ker :=
        by simpa only [generalized_eigenspace, OrderHom.coe_mk, ← LinearMap.ker_comp]
      _ = f.generalized_eigenspace μ (finrank K V + finrank K V) := by rw [← pow_add]; rfl
      _ = f.generalized_eigenspace μ (finrank K V) := by
        rw [generalized_eigenspace_eq_generalized_eigenspace_finrank_of_le]; linarith
  rw [disjoint_iff_inf_le, generalized_eigenrange, LinearMap.range_eq_map,
    Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h]
  apply Submodule.map_comap_le
#align module.End.generalized_eigenvec_disjoint_range_ker Module.End.generalized_eigenvec_disjoint_range_ker
-/

#print Module.End.eigenspace_restrict_eq_bot /-
/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ :=
  by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩
#align module.End.eigenspace_restrict_eq_bot Module.End.eigenspace_restrict_eq_bot
-/

#print Module.End.pos_finrank_genEigenspace_of_hasEigenvalue /-
/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
theorem pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V} {k : ℕ}
    {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) : 0 < finrank K (f.genEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := (Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx))
    _ ≤ finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).Monotone (Nat.succ_le_of_lt hk))
#align module.End.pos_finrank_generalized_eigenspace_of_has_eigenvalue Module.End.pos_finrank_genEigenspace_of_hasEigenvalue
-/

#print Module.End.map_genEigenrange_le /-
/-- A linear map maps a generalized eigenrange into itself. -/
theorem map_genEigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.genEigenrange μ n) ≤ f.genEigenrange μ n :=
  calc
    Submodule.map f (f.genEigenrange μ n) = (f * (f - algebraMap _ _ μ) ^ n).range :=
      (LinearMap.range_comp _ _).symm
    _ = ((f - algebraMap _ _ μ) ^ n * f).range := by rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) f.range := (LinearMap.range_comp _ _)
    _ ≤ f.genEigenrange μ n := LinearMap.map_le_range
#align module.End.map_generalized_eigenrange_le Module.End.map_genEigenrange_le
-/

end End

end Module

