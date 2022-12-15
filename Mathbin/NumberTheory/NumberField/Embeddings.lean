/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Xavier Roblot

! This file was ported from Lean 3 source module number_theory.number_field.embeddings
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.NumberTheory.NumberField.Basic
import Mathbin.Topology.Algebra.Polynomial

/-!
# Embeddings of number fields
This file defines the embeddings of a number field into an algebraic closed field.

## Main Results
* `number_field.embeddings.eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic
  closed field of char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the
  roots in `A` of the minimal polynomial of `x` over `ℚ`.
* `number_field.embeddings.pow_eq_one_of_norm_eq_one`: an algebraic integer whose conjugates are
  all of norm one is a root of unity.

## Tags
number field, embeddings
-/


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
  rw [Fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, AlgHom.card]
#align number_field.embeddings.card NumberField.Embeddings.card

end Fintype

section Roots

open Set Polynomial

variable (K A : Type _) [Field K] [NumberField K] [Field A] [Algebra ℚ A] [IsAlgClosed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ`. -/
theorem range_eval_eq_root_set_minpoly : (range fun φ : K →+* A => φ x) = (minpoly ℚ x).rootSet A :=
  by 
  convert (NumberField.is_algebraic K).range_eval_eq_root_set_minpoly A x using 1
  ext a
  exact ⟨fun ⟨φ, hφ⟩ => ⟨φ.toRatAlgHom, hφ⟩, fun ⟨φ, hφ⟩ => ⟨φ.toRingHom, hφ⟩⟩
#align
  number_field.embeddings.range_eval_eq_root_set_minpoly NumberField.Embeddings.range_eval_eq_root_set_minpoly

end Roots

section Bounded

open FiniteDimensional Polynomial Set

variable {K : Type _} [Field K] [NumberField K]

variable {A : Type _} [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem coeff_bdd_of_norm_le {B : ℝ} {x : K} (h : ∀ φ : K →+* A, ‖φ x‖ ≤ B) (i : ℕ) :
    ‖(minpoly ℚ x).coeff i‖ ≤ max B 1 ^ finrank ℚ K * (finrank ℚ K).choose (finrank ℚ K / 2) := by
  have hx := IsSeparable.is_integral ℚ x
  rw [← norm_algebra_map' A, ← coeff_map (algebraMap ℚ A)]
  refine'
    coeff_bdd_of_roots_le _ (minpoly.monic hx) (IsAlgClosed.splits_codomain _)
      (minpoly.nat_degree_le hx) (fun z hz => _) i
  classical 
    rw [← Multiset.mem_to_finset] at hz
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
  have h_map_ℚ_minpoly := minpoly.gcd_domain_eq_field_fractions' ℚ hx.1
  refine' ⟨_, ⟨_, fun i => _⟩, mem_root_set.2 ⟨minpoly.ne_zero hx.1, minpoly.aeval ℤ x⟩⟩
  · rw [← (minpoly.monic hx.1).nat_degree_map (algebraMap ℤ ℚ), ← h_map_ℚ_minpoly]
    exact minpoly.nat_degree_le (is_integral_of_is_scalar_tower hx.1)
  rw [mem_Icc, ← abs_le, ← @Int.cast_le ℝ]
  refine' (Eq.trans_le _ <| coeff_bdd_of_norm_le hx.2 i).trans (Nat.le_ceil _)
  rw [h_map_ℚ_minpoly, coeff_map, eq_int_cast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs]
#align number_field.embeddings.finite_of_norm_le NumberField.Embeddings.finite_of_norm_le

/-- An algebraic integer whose conjugates are all of norm one is a root of unity. -/
theorem pow_eq_one_of_norm_eq_one {x : K} (hxi : IsIntegral ℤ x) (hx : ∀ φ : K →+* A, ‖φ x‖ = 1) :
    ∃ (n : ℕ)(hn : 0 < n), x ^ n = 1 := by
  obtain ⟨a, -, b, -, habne, h⟩ :=
    @Set.Infinite.exists_ne_map_eq_of_maps_to _ _ _ _ ((· ^ ·) x : ℕ → K) Set.infinite_univ _
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
    specialize hx (IsAlgClosed.lift (NumberField.is_algebraic K)).toRingHom
    rw [pow_eq_zero hp, map_zero, norm_zero] at hx
    norm_num at hx
  · exact fun a _ => ⟨hxi.pow a, fun φ => by simp only [hx φ, norm_pow, one_pow, map_pow]⟩
#align
  number_field.embeddings.pow_eq_one_of_norm_eq_one NumberField.Embeddings.pow_eq_one_of_norm_eq_one

end Bounded

end NumberField.Embeddings

