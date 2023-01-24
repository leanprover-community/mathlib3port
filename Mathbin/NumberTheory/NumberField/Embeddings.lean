/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot

! This file was ported from Lean 3 source module number_theory.number_field.embeddings
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Polynomial
import Mathbin.Data.Complex.Basic
import Mathbin.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathbin.NumberTheory.NumberField.Basic

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.range_eval_eq_root_set_minpoly`: let `x ∈ K` with `K` number field and
  let `A` be an algebraic closed field of char. 0, then the images of `x` by the embeddings of `K`
   in `A` are exactly the roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings, places, infinite places
-/


open Classical

namespace NumberField.Embeddings

section Fintype

open FiniteDimensional

variable (K : Type _) [Field K] [NumberField K]

variable (A : Type _) [Field A] [CharZero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : Fintype (K →+* A) :=
  Fintype.ofEquiv (K →ₐ[ℚ] A) RingHom.equivRatAlgHom.symm

variable [IsAlgClosed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
theorem card : Fintype.card (K →+* A) = finrank ℚ K := by
  rw [Fintype.ofEquiv_card ring_hom.equiv_rat_alg_hom.symm, AlgHom.card]
#align number_field.embeddings.card NumberField.Embeddings.card

instance : Nonempty (K →+* A) :=
  by
  rw [← Fintype.card_pos_iff, NumberField.Embeddings.card K A]
  exact FiniteDimensional.finrank_pos

end Fintype

section Roots

open Set Polynomial

variable (K A : Type _) [Field K] [NumberField K] [Field A] [Algebra ℚ A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
theorem range_eval_eq_rootSet_minpoly : (range fun φ : K →+* A => φ x) = (minpoly ℚ x).rootSet A :=
  by
  convert (NumberField.isAlgebraic K).range_eval_eq_root_set_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩
#align number_field.embeddings.range_eval_eq_root_set_minpoly NumberField.Embeddings.range_eval_eq_rootSet_minpoly

end Roots

section Bounded

open FiniteDimensional Polynomial Set

variable {K : Type _} [Field K] [NumberField K]

variable {A : Type _} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) :=
  by
  have hx := IsSeparable.isIntegral ℚ x
  rw [← norm_algebra_map' A, ← coeff_map (algebraMap ℚ A)]
  refine'
    coeff_bdd_of_roots_le _ (minpoly.monic hx) (IsAlgClosed.splits_codomain _)
      (minpoly.natDegree_le hx) (fun z hz => _) i
  classical
    rw [← Multiset.mem_toFinset] at hz
    obtain ⟨φ, rfl⟩ := (range_eval_eq_root_set_minpoly K A x).symm.Subset hz
    exact h φ
#align number_field.embeddings.coeff_bdd_of_norm_le NumberField.Embeddings.coeff_bdd_of_norm_le

variable (K A)

/-- Let `B` be a real number. The set of algebraic integers in `K` whose conjugates are all
smaller in norm than `B` is finite. -/
theorem finite_of_norm_le (B : ℝ) : { x : K | IsIntegral ℤ x ∧ ∀ φ : K →+* A, ‖φ x‖ ≤ B }.Finite :=
  by
  let C := Nat.ceil (max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2))
  have := bUnion_roots_finite (algebraMap ℤ K) (finrank ℚ K) (finite_Icc (-C : ℤ) C)
  refine' this.subset fun x hx => _; simp_rw [mem_Union]
  have h_map_ℚ_minpoly := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hx.1
  refine' ⟨_, ⟨_, fun i => _⟩, mem_root_set.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩
  · rw [← (minpoly.monic hx.1).nat_degree_map (algebraMap ℤ ℚ), ← h_map_ℚ_minpoly]
    exact minpoly.natDegree_le (isIntegral_of_isScalarTower hx.1)
  rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  refine' (Eq.trans_le _ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_ℚ_minpoly, coeff_map, eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
#align number_field.embeddings.finite_of_norm_le NumberField.Embeddings.finite_of_norm_le

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ)(hn : 0 < n), x ^ n = 1 :=
  by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_mapsTo _ _ _ _ ((· ^ ·) x : ℕ → K) Set.infinite_univ _
      (finite_of_norm_le K A (1 : ℝ))
  · replace habne := habne.lt_or_lt
    have : _
    swap
    cases habne
    swap
    · revert a b
      exact this
    · exact this b a h.symm habne
    refine' fun a b h hlt => ⟨a - b, tsub_pos_of_lt hlt, _⟩
    rw [← Nat.sub_add_cancel hlt.le, pow_add, mul_left_eq_self₀] at h
    refine' h.resolve_right fun hp => _
    specialize hx (IsAlgClosed.lift (NumberField.isAlgebraic K)).toRingHom
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx
    norm_num at hx
  · exact fun a _ => ⟨hxi.pow a, fun φ => by simp only [hx φ, norm_pow, one_pow, map_pow]⟩
#align number_field.embeddings.pow_eq_one_of_norm_eq_one NumberField.Embeddings.pow_eq_one_of_norm_eq_one

end Bounded

end NumberField.Embeddings

section Place

variable {K : Type _} [Field K] {A : Type _} [NormedDivisionRing A] [Nontrivial A] (φ : K →+* A)

/-- An embedding into a normed division ring defines a place of `K` -/
def NumberField.place : AbsoluteValue K ℝ :=
  (IsAbsoluteValue.toAbsoluteValue (norm : A → ℝ)).comp φ.Injective
#align number_field.place NumberField.place

@[simp]
theorem NumberField.place_apply (x : K) : (NumberField.place φ) x = norm (φ x) :=
  rfl
#align number_field.place_apply NumberField.place_apply

end Place

namespace NumberField.ComplexEmbedding

open Complex NumberField

open ComplexConjugate

variable {K : Type _} [Field K]

/-- The conjugate of a complex embedding as a complex embedding. -/
@[reducible]
def conjugate (φ : K →+* ℂ) : K →+* ℂ :=
  star φ
#align number_field.complex_embedding.conjugate NumberField.ComplexEmbedding.conjugate

@[simp]
theorem conjugate_coe_eq (φ : K →+* ℂ) (x : K) : (conjugate φ) x = conj (φ x) :=
  rfl
#align number_field.complex_embedding.conjugate_coe_eq NumberField.ComplexEmbedding.conjugate_coe_eq

theorem place_conjugate (φ : K →+* ℂ) : place (conjugate φ) = place φ :=
  by
  ext
  simp only [place_apply, norm_eq_abs, abs_conj, conjugate_coe_eq]
#align number_field.complex_embedding.place_conjugate NumberField.ComplexEmbedding.place_conjugate

/-- A embedding into `ℂ` is real if it is fixed by complex conjugation. -/
@[reducible]
def IsReal (φ : K →+* ℂ) : Prop :=
  IsSelfAdjoint φ
#align number_field.complex_embedding.is_real NumberField.ComplexEmbedding.IsReal

theorem isReal_iff {φ : K →+* ℂ} : IsReal φ ↔ conjugate φ = φ :=
  isSelfAdjoint_iff
#align number_field.complex_embedding.is_real_iff NumberField.ComplexEmbedding.isReal_iff

/-- A real embedding as a ring homomorphism from `K` to `ℝ` . -/
def IsReal.embedding {φ : K →+* ℂ} (hφ : IsReal φ) : K →+* ℝ
    where
  toFun x := (φ x).re
  map_one' := by simp only [map_one, one_re]
  map_mul' := by
    simp only [complex.eq_conj_iff_im.mp (RingHom.congr_fun hφ _), map_mul, mul_re, mul_zero,
      tsub_zero, eq_self_iff_true, forall_const]
  map_zero' := by simp only [map_zero, zero_re]
  map_add' := by simp only [map_add, add_re, eq_self_iff_true, forall_const]
#align number_field.complex_embedding.is_real.embedding NumberField.ComplexEmbedding.IsReal.embedding

@[simp]
theorem IsReal.coe_embedding_apply {φ : K →+* ℂ} (hφ : IsReal φ) (x : K) :
    (hφ.Embedding x : ℂ) = φ x := by
  ext; · rfl
  · rw [of_real_im, eq_comm, ← Complex.eq_conj_iff_im]
    rw [is_real] at hφ
    exact RingHom.congr_fun hφ x
#align number_field.complex_embedding.is_real.coe_embedding_apply NumberField.ComplexEmbedding.IsReal.coe_embedding_apply

theorem IsReal.place_embedding {φ : K →+* ℂ} (hφ : IsReal φ) : place hφ.Embedding = place φ :=
  by
  ext x
  simp only [place_apply, Real.norm_eq_abs, ← abs_of_real, norm_eq_abs, hφ.coe_embedding_apply x]
#align number_field.complex_embedding.is_real.place_embedding NumberField.ComplexEmbedding.IsReal.place_embedding

theorem isReal_conjugate_iff {φ : K →+* ℂ} : IsReal (conjugate φ) ↔ IsReal φ :=
  IsSelfAdjoint.star_iff
#align number_field.complex_embedding.is_real_conjugate_iff NumberField.ComplexEmbedding.isReal_conjugate_iff

end NumberField.ComplexEmbedding

section InfinitePlace

open NumberField

variable (K : Type _) [Field K]

/-- An infinite place of a number field `K` is a place associated to a complex embedding. -/
def NumberField.InfinitePlace :=
  { w : AbsoluteValue K ℝ // ∃ φ : K →+* ℂ, place φ = w }
#align number_field.infinite_place NumberField.InfinitePlace

instance [NumberField K] : Nonempty (NumberField.InfinitePlace K) :=
  Set.range.nonempty _

variable {K}

/-- Return the infinite place defined by a complex embedding `φ`. -/
noncomputable def NumberField.InfinitePlace.mk (φ : K →+* ℂ) : NumberField.InfinitePlace K :=
  ⟨place φ, ⟨φ, rfl⟩⟩
#align number_field.infinite_place.mk NumberField.InfinitePlace.mk

namespace NumberField.InfinitePlace

open NumberField

instance : CoeFun (InfinitePlace K) fun _ => K → ℝ where coe w := w.1

instance : MonoidWithZeroHomClass (InfinitePlace K) K ℝ
    where
  coe w x := w.1 x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)
  map_mul w _ _ := w.1.map_mul _ _
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (InfinitePlace K) K ℝ
    where
  coe w x := w x
  coe_injective' _ _ h := Subtype.eq (AbsoluteValue.ext fun x => congr_fun h x)
  map_nonneg w x := w.1.Nonneg _

theorem coe_mk (φ : K →+* ℂ) : ⇑(mk φ) = place φ :=
  rfl
#align number_field.infinite_place.coe_mk NumberField.InfinitePlace.coe_mk

theorem apply (φ : K →+* ℂ) (x : K) : (mk φ) x = Complex.abs (φ x) :=
  rfl
#align number_field.infinite_place.apply NumberField.InfinitePlace.apply

/-- For an infinite place `w`, return an embedding `φ` such that `w = infinite_place φ` . -/
noncomputable def embedding (w : InfinitePlace K) : K →+* ℂ :=
  w.2.some
#align number_field.infinite_place.embedding NumberField.InfinitePlace.embedding

theorem mk_embedding (w : InfinitePlace K) : mk (embedding w) = w :=
  Subtype.ext w.2.some_spec
#align number_field.infinite_place.mk_embedding NumberField.InfinitePlace.mk_embedding

theorem pos_iff (w : InfinitePlace K) (x : K) : 0 < w x ↔ x ≠ 0 :=
  AbsoluteValue.pos_iff w.1
#align number_field.infinite_place.pos_iff NumberField.InfinitePlace.pos_iff

end NumberField.InfinitePlace

end InfinitePlace

