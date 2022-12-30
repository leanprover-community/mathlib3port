/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module linear_algebra.matrix.charpoly.linear_map
! leanprover-community/mathlib commit 986c4d5761f938b2e1c43c01f001b6d9d88c2055
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathbin.LinearAlgebra.Matrix.ToLin

/-!

# Calyley-Hamilton theorem for f.g. modules.

Given a fixed finite spanning set `b : ι → M` of a `R`-module `M`, we say that a matrix `M`
represents an endomorphism `f : M →ₗ[R] M` if the matrix as an endomorphism of `ι → R` commutes
with `f` via the projection `(ι → R) →ₗ[R] M` given by `b`.

We show that every endomorphism has a matrix representation, and if `f.range ≤ I • ⊤` for some
ideal `I`, we may furthermore obtain a matrix representation whose entries fall in `I`.

This is used to conclude the Cayley-Hamilton theorem for f.g. modules over arbitrary rings.
-/


variable {ι : Type _} [Fintype ι]

variable {M : Type _} [AddCommGroup M] (R : Type _) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M) (hb : Submodule.span R (Set.range b) = ⊤)

open BigOperators

open Polynomial

/-- The composition of a matrix (as an endomporphism of `ι → R`) with the projection
`(ι → R) →ₗ[R] M`.  -/
def PiToModule.fromMatrix [DecidableEq ι] : Matrix ι ι R →ₗ[R] (ι → R) →ₗ[R] M :=
  (LinearMap.llcomp R _ _ _ (Fintype.total R R b)).comp algEquivMatrix'.symm.toLinearMap
#align pi_to_module.from_matrix PiToModule.fromMatrix

theorem PiToModule.from_matrix_apply [DecidableEq ι] (A : Matrix ι ι R) (w : ι → R) :
    PiToModule.fromMatrix R b A w = Fintype.total R R b (A.mulVec w) :=
  rfl
#align pi_to_module.from_matrix_apply PiToModule.from_matrix_apply

theorem PiToModule.from_matrix_apply_single_one [DecidableEq ι] (A : Matrix ι ι R) (j : ι) :
    PiToModule.fromMatrix R b A (Pi.single j 1) = ∑ i : ι, A i j • b i :=
  by
  rw [PiToModule.from_matrix_apply, Fintype.total_apply, Matrix.mul_vec_single]
  simp_rw [mul_one]
#align pi_to_module.from_matrix_apply_single_one PiToModule.from_matrix_apply_single_one

/-- The endomorphisms of `M` acts on `(ι → R) →ₗ[R] M`, and takes the projection
to a `(ι → R) →ₗ[R] M`. -/
def PiToModule.fromEnd : Module.EndCat R M →ₗ[R] (ι → R) →ₗ[R] M :=
  LinearMap.lcomp _ _ (Fintype.total R R b)
#align pi_to_module.from_End PiToModule.fromEnd

theorem PiToModule.from_End_apply (f : Module.EndCat R M) (w : ι → R) :
    PiToModule.fromEnd R b f w = f (Fintype.total R R b w) :=
  rfl
#align pi_to_module.from_End_apply PiToModule.from_End_apply

theorem PiToModule.from_End_apply_single_one [DecidableEq ι] (f : Module.EndCat R M) (i : ι) :
    PiToModule.fromEnd R b f (Pi.single i 1) = f (b i) :=
  by
  rw [PiToModule.from_End_apply]
  congr
  convert Fintype.total_apply_single R b i 1
  rw [one_smul]
#align pi_to_module.from_End_apply_single_one PiToModule.from_End_apply_single_one

theorem PiToModule.from_End_injective (hb : Submodule.span R (Set.range b) = ⊤) :
    Function.Injective (PiToModule.fromEnd R b) :=
  by
  intro x y e
  ext m
  obtain ⟨m, rfl⟩ : m ∈ (Fintype.total R R b).range :=
    by
    rw [(Fintype.range_total R b).trans hb]
    trivial
  exact (LinearMap.congr_fun e m : _)
#align pi_to_module.from_End_injective PiToModule.from_End_injective

section

variable {R} [DecidableEq ι]

/-- We say that a matrix represents an endomorphism of `M` if the matrix acting on `ι → R` is
equal to `f` via the projection `(ι → R) →ₗ[R] M` given by a fixed (spanning) set.  -/
def Matrix.Represents (A : Matrix ι ι R) (f : Module.EndCat R M) : Prop :=
  PiToModule.fromMatrix R b A = PiToModule.fromEnd R b f
#align matrix.represents Matrix.Represents

variable {b}

theorem Matrix.Represents.congr_fun {A : Matrix ι ι R} {f : Module.EndCat R M}
    (h : A.Represents b f) (x) : Fintype.total R R b (A.mulVec x) = f (Fintype.total R R b x) :=
  LinearMap.congr_fun h x
#align matrix.represents.congr_fun Matrix.Represents.congr_fun

theorem Matrix.represents_iff {A : Matrix ι ι R} {f : Module.EndCat R M} :
    A.Represents b f ↔ ∀ x, Fintype.total R R b (A.mulVec x) = f (Fintype.total R R b x) :=
  ⟨fun e x => e.congr_fun x, fun H => LinearMap.ext fun x => H x⟩
#align matrix.represents_iff Matrix.represents_iff

theorem Matrix.represents_iff' {A : Matrix ι ι R} {f : Module.EndCat R M} :
    A.Represents b f ↔ ∀ j, (∑ i : ι, A i j • b i) = f (b j) :=
  by
  constructor
  · intro h i
    have := LinearMap.congr_fun h (Pi.single i 1)
    rwa [PiToModule.from_End_apply_single_one, PiToModule.from_matrix_apply_single_one] at this
  · intro h
    ext
    simp_rw [LinearMap.comp_apply, LinearMap.coe_single, PiToModule.from_End_apply_single_one,
      PiToModule.from_matrix_apply_single_one]
    apply h
#align matrix.represents_iff' Matrix.represents_iff'

theorem Matrix.Represents.mul {A A' : Matrix ι ι R} {f f' : Module.EndCat R M}
    (h : A.Represents b f) (h' : Matrix.Represents b A' f') : (A * A').Represents b (f * f') :=
  by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.to_linear_map_apply, map_mul]
  ext
  dsimp [PiToModule.fromEnd]
  rw [← h'.congr_fun, ← h.congr_fun]
  rfl
#align matrix.represents.mul Matrix.Represents.mul

theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 :=
  by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.to_linear_map_apply, map_one]
  ext
  rfl
#align matrix.represents.one Matrix.Represents.one

theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.EndCat R M}
    (h : A.Represents b f) (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h'⊢; rw [map_add, map_add, h, h']
#align matrix.represents.add Matrix.Represents.add

theorem Matrix.Represents.zero : (0 : Matrix ι ι R).Represents b 0 := by delta Matrix.Represents;
  rw [map_zero, map_zero]
#align matrix.represents.zero Matrix.Represents.zero

theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.EndCat R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by delta Matrix.Represents at h⊢;
  rw [map_smul, map_smul, h]
#align matrix.represents.smul Matrix.Represents.smul

theorem Matrix.Represents.eq {A : Matrix ι ι R} {f f' : Module.EndCat R M} (h : A.Represents b f)
    (h' : A.Represents b f') : f = f' :=
  PiToModule.from_End_injective R b hb (h.symm.trans h')
#align matrix.represents.eq Matrix.Represents.eq

variable (b R)

/-- The subalgebra of `matrix ι ι R` that consists of matrices that actually represent
endomorphisms on `M`. -/
def Matrix.isRepresentation : Subalgebra R (Matrix ι ι R)
    where
  carrier := { A | ∃ f : Module.EndCat R M, A.Represents b f }
  mul_mem' := fun A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ * f₂, e₁.mul e₂⟩
  one_mem' := ⟨1, Matrix.Represents.one⟩
  add_mem' := fun A₁ A₂ ⟨f₁, e₁⟩ ⟨f₂, e₂⟩ => ⟨f₁ + f₂, e₁.add e₂⟩
  zero_mem' := ⟨0, Matrix.Represents.zero⟩
  algebra_map_mem' r := ⟨r • 1, Matrix.Represents.one.smul r⟩
#align matrix.is_representation Matrix.isRepresentation

/-- The map sending a matrix to the endomorphism it represents. This is an `R`-algebra morphism. -/
noncomputable def Matrix.isRepresentation.toEnd :
    Matrix.isRepresentation R b →ₐ[R] Module.EndCat R M
    where
  toFun A := A.2.some
  map_one' := (1 : Matrix.isRepresentation R b).2.some_spec.Eq hb Matrix.Represents.one
  map_mul' A₁ A₂ := (A₁ * A₂).2.some_spec.Eq hb (A₁.2.some_spec.mul A₂.2.some_spec)
  map_zero' := (0 : Matrix.isRepresentation R b).2.some_spec.Eq hb Matrix.Represents.zero
  map_add' A₁ A₂ := (A₁ + A₂).2.some_spec.Eq hb (A₁.2.some_spec.add A₂.2.some_spec)
  commutes' r :=
    (r • 1 : Matrix.isRepresentation R b).2.some_spec.Eq hb (Matrix.Represents.one.smul r)
#align matrix.is_representation.to_End Matrix.isRepresentation.toEnd

theorem Matrix.isRepresentation.to_End_represents (A : Matrix.isRepresentation R b) :
    (A : Matrix ι ι R).Represents b (Matrix.isRepresentation.toEnd R b hb A) :=
  A.2.some_spec
#align matrix.is_representation.to_End_represents Matrix.isRepresentation.to_End_represents

theorem Matrix.isRepresentation.eq_to_End_of_represents (A : Matrix.isRepresentation R b)
    {f : Module.EndCat R M} (h : (A : Matrix ι ι R).Represents b f) :
    Matrix.isRepresentation.toEnd R b hb A = f :=
  A.2.some_spec.Eq hb h
#align
  matrix.is_representation.eq_to_End_of_represents Matrix.isRepresentation.eq_to_End_of_represents

theorem Matrix.isRepresentation.to_End_exists_mem_ideal (f : Module.EndCat R M) (I : Ideal R)
    (hI : f.range ≤ I • ⊤) : ∃ M, Matrix.isRepresentation.toEnd R b hb M = f ∧ ∀ i j, M.1 i j ∈ I :=
  by
  have : ∀ x, f x ∈ (Ideal.finsuppTotal ι M I b).range :=
    by
    rw [Ideal.range_finsupp_total, hb]
    exact fun x => hI (f.mem_range_self x)
  choose bM' hbM'
  let A : Matrix ι ι R := fun i j => bM' (b j) i
  have : A.represents b f := by
    rw [Matrix.represents_iff']
    dsimp [A]
    intro j
    specialize hbM' (b j)
    rwa [Ideal.finsupp_total_apply_eq_of_fintype] at hbM'
  exact
    ⟨⟨A, f, this⟩, Matrix.isRepresentation.eq_to_End_of_represents R b hb ⟨A, f, this⟩ this,
      fun i j => (bM' (b j) i).Prop⟩
#align
  matrix.is_representation.to_End_exists_mem_ideal Matrix.isRepresentation.to_End_exists_mem_ideal

theorem Matrix.isRepresentation.to_End_surjective :
    Function.Surjective (Matrix.isRepresentation.toEnd R b hb) :=
  by
  intro f
  obtain ⟨M, e, -⟩ := Matrix.isRepresentation.to_End_exists_mem_ideal R b hb f ⊤ _
  exact ⟨M, e⟩
  simp
#align matrix.is_representation.to_End_surjective Matrix.isRepresentation.to_End_surjective

end

/-- The **Cayley-Hamilton Theorem** for f.g. modules over arbitrary rings states that for each
`R`-endomorphism `φ` of an `R`-module `M` such that `φ(M) ≤ I • M` for some ideal `I`, there
exists some `n` and some `aᵢ ∈ Iⁱ` such that `φⁿ + a₁ φⁿ⁻¹ + ⋯ + aₙ = 0`.

This is the version found in Eisenbud 4.3, which is slightly weaker than Matsumura 2.1
(this lacks the constraint on `n`), and is slightly stronger than Atiyah-Macdonald 2.4.
-/
theorem LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
    [Module.Finite R M] (f : Module.EndCat R M) (I : Ideal R) (hI : f.range ≤ I • ⊤) :
    ∃ p : R[X], p.Monic ∧ (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧ Polynomial.aeval f p = 0 := by
  classical
    cases subsingleton_or_nontrivial R
    · exact ⟨0, Polynomial.monic_of_subsingleton _, by simp⟩
    obtain ⟨s : Finset M, hs : Submodule.span R (s : Set M) = ⊤⟩ := Module.Finite.out
    obtain ⟨A, rfl, h⟩ :=
      Matrix.isRepresentation.to_End_exists_mem_ideal R (coe : s → M)
        (by rw [Subtype.range_coe_subtype, Finset.set_of_mem, hs]) f I hI
    refine' ⟨A.1.charpoly, A.1.charpoly_monic, _, _⟩
    · rw [A.1.charpoly_nat_degree_eq_dim]
      exact coeff_charpoly_mem_ideal_pow h
    · rw [Polynomial.aeval_alg_hom_apply, ← map_zero (Matrix.isRepresentation.toEnd R coe _)]
      congr 1
      ext1
      rw [Polynomial.aeval_subalgebra_coe, Subtype.val_eq_coe, Matrix.aeval_self_charpoly,
        Subalgebra.coe_zero]
    · infer_instance
#align
  linear_map.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul

theorem LinearMap.exists_monic_and_aeval_eq_zero [Module.Finite R M] (f : Module.EndCat R M) :
    ∃ p : R[X], p.Monic ∧ Polynomial.aeval f p = 0 :=
  (LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul R f ⊤ (by simp)).imp
    fun p h => h.imp_right And.right
#align linear_map.exists_monic_and_aeval_eq_zero LinearMap.exists_monic_and_aeval_eq_zero

