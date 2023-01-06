/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

! This file was ported from Lean 3 source module number_theory.ramification_inertia
! leanprover-community/mathlib commit 26f081a2fb920140ed5bc5cc5344e84bcc7cb2b2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.RingTheory.DedekindDomain.Ideal

/-!
# Ramification index and inertia degree

Given `P : ideal S` lying over `p : ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `ideal.ramification_idx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `ideal.inertia_deg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## Main results

The main theorem `ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
 * `R` is the ring of integers of a number field `K`,
 * `L` is a finite separable extension of `K`,
 * `S` is the integral closure of `R` in `L`,
 * `p` and `P` are maximal ideals,
 * `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

## Notation

In this file, `e` stands for the ramification index and `f` for the inertia degree of `P` over `p`,
leaving `p` and `P` implicit.

-/


namespace Ideal

universe u v

variable {R : Type u} [CommRing R]

variable {S : Type v} [CommRing S] (f : R →+* S)

variable (p : Ideal R) (P : Ideal S)

open FiniteDimensional

open UniqueFactorizationMonoid

section DecEq

open Classical

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramification_idx` is
defined to be 0.
-/
noncomputable def ramificationIdx : ℕ :=
  supₛ { n | map f p ≤ P ^ n }
#align ideal.ramification_idx Ideal.ramificationIdx

variable {f p P}

theorem ramification_idx_eq_find (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) :
    ramificationIdx f p P = Nat.find h :=
  Nat.Sup_def h
#align ideal.ramification_idx_eq_find Ideal.ramification_idx_eq_find

theorem ramification_idx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) :
    ramificationIdx f p P = 0 :=
  dif_neg (by push_neg <;> exact h)
#align ideal.ramification_idx_eq_zero Ideal.ramification_idx_eq_zero

theorem ramification_idx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx f p P = n :=
  by
  have : ∀ k : ℕ, map f p ≤ P ^ k → k ≤ n := by
    intro k hk
    refine' le_of_not_lt fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  · refine' le_antisymm (Nat.find_min' _ this) (le_of_not_gt fun h : Nat.find _ < n => _)
    obtain this' := Nat.find_spec ⟨n, this⟩
    exact h.not_le (this' _ hle)
#align ideal.ramification_idx_spec Ideal.ramification_idx_spec

theorem ramification_idx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx f p P < n :=
  by
  cases n
  · simpa using hgt
  rw [Nat.lt_succ_iff]
  have : ∀ k, map f p ≤ P ^ k → k ≤ n :=
    by
    refine' fun k hk => le_of_not_lt fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  exact Nat.find_min' ⟨n, this⟩ this
#align ideal.ramification_idx_lt Ideal.ramification_idx_lt

@[simp]
theorem ramification_idx_bot : ramificationIdx f ⊥ P = 0 :=
  dif_neg <| not_exists.mpr fun n hn => n.lt_succ_self.not_le (hn _ (by simp))
#align ideal.ramification_idx_bot Ideal.ramification_idx_bot

@[simp]
theorem ramification_idx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx f p P = 0 :=
  ramification_idx_spec (by simp) (by simpa using h)
#align ideal.ramification_idx_of_not_le Ideal.ramification_idx_of_not_le

theorem ramification_idx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e)
    (hnle : ¬map f p ≤ P ^ (e + 1)) : ramificationIdx f p P ≠ 0 := by
  rwa [ramification_idx_spec hle hnle]
#align ideal.ramification_idx_ne_zero Ideal.ramification_idx_ne_zero

theorem le_pow_of_le_ramification_idx {n : ℕ} (hn : n ≤ ramificationIdx f p P) : map f p ≤ P ^ n :=
  by
  contrapose! hn
  exact ramification_idx_lt hn
#align ideal.le_pow_of_le_ramification_idx Ideal.le_pow_of_le_ramification_idx

theorem le_pow_ramification_idx : map f p ≤ P ^ ramificationIdx f p P :=
  le_pow_of_le_ramification_idx (le_refl _)
#align ideal.le_pow_ramification_idx Ideal.le_pow_ramification_idx

theorem le_comap_pow_ramification_idx : p ≤ comap f (P ^ ramificationIdx f p P) :=
  map_le_iff_le_comap.mp le_pow_ramification_idx
#align ideal.le_comap_pow_ramification_idx Ideal.le_comap_pow_ramification_idx

theorem le_comap_of_ramification_idx_ne_zero (h : ramificationIdx f p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramification_idx.trans <| Ideal.pow_le_self <| h
#align ideal.le_comap_of_ramification_idx_ne_zero Ideal.le_comap_of_ramification_idx_ne_zero

namespace IsDedekindDomain

variable [IsDomain S] [IsDedekindDomain S]

theorem ramification_idx_eq_normalized_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) : ramificationIdx f p P = (normalizedFactors (map f p)).count P :=
  by
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  refine' ramification_idx_spec (Ideal.le_of_dvd _) (mt ideal.dvd_iff_le.mpr _) <;>
    rw [dvd_iff_normalized_factors_le_normalized_factors (pow_ne_zero _ hP0) hp0,
      normalized_factors_pow, normalized_factors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_repeat_le]
  · exact (Nat.lt_succ_self _).not_le
#align
  ideal.is_dedekind_domain.ramification_idx_eq_normalized_factors_count Ideal.IsDedekindDomain.ramification_idx_eq_normalized_factors_count

theorem ramification_idx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (factors (map f p)).count P := by
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0,
    factors_eq_normalized_factors]
#align
  ideal.is_dedekind_domain.ramification_idx_eq_factors_count Ideal.IsDedekindDomain.ramification_idx_eq_factors_count

theorem ramification_idx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) :
    ramificationIdx f p P ≠ 0 :=
  by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := le_bot_iff.mp le
    contradiction
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ :=
    exists_mem_normalized_factors_of_dvd hp0 hPirr (ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]
#align
  ideal.is_dedekind_domain.ramification_idx_ne_zero Ideal.IsDedekindDomain.ramification_idx_ne_zero

end IsDedekindDomain

variable (f p P)

attribute [local instance] Ideal.Quotient.field

/-- The inertia degree of `P : ideal S` lying over `p : ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertia_deg_algebra_map` for the common case where `f = algebra_map R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertiaDeg [hp : p.IsMaximal] : ℕ :=
  if hPp : comap f P = p then
    @finrank (R ⧸ p) (S ⧸ P) _ _ <|
      @Algebra.toModule _ _ _ _ <|
        RingHom.toAlgebra <|
          (Ideal.Quotient.lift p (P f)) fun a ha =>
            Quotient.eq_zero_iff_mem.mpr <| mem_comap.mp <| hPp.symm ▸ ha
  else 0
#align ideal.inertia_deg Ideal.inertiaDeg

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertia_deg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] :
    inertiaDeg f p P = 0 :=
  by
  have := ideal.quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top
#align ideal.inertia_deg_of_subsingleton Ideal.inertia_deg_of_subsingleton

@[simp]
theorem inertia_deg_algebra_map [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] [hp : p.IsMaximal] :
    inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P) :=
  by
  nontriviality S ⧸ P using inertia_deg_of_subsingleton, finrank_zero_of_subsingleton
  have := comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P)).Injective
  rw [inertia_deg, dif_pos this]
  congr
  refine' Algebra.algebra_ext _ _ fun x' => (Quotient.inductionOn' x') fun x => _
  change Ideal.Quotient.lift p _ _ (Ideal.Quotient.mk p x) = algebraMap _ _ (Ideal.Quotient.mk p x)
  rw [Ideal.Quotient.lift_mk, ← Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_eq, ←
    Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_apply]
#align ideal.inertia_deg_algebra_map Ideal.inertia_deg_algebra_map

end DecEq

section FinrankQuotientMap

open BigOperators

open nonZeroDivisors

variable [Algebra R S]

variable {K : Type _} [Field K] [Algebra R K] [hRK : IsFractionRing R K]

variable {L : Type _} [Field L] [Algebra S L] [IsFractionRing S L]

variable {V V' V'' : Type _}

variable [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

variable [AddCommGroup V'] [Module R V'] [Module S V'] [IsScalarTower R S V']

variable [AddCommGroup V''] [Module R V'']

variable (K)

include hRK

/-- Let `V` be a vector space over `K = Frac(R)`, `S / R` a ring extension
and `V'` a module over `S`. If `b`, in the intersection `V''` of `V` and `V'`,
is linear independent over `S` in `V'`, then it is linear independent over `R` in `V`.

The statement we prove is actually slightly more general:
 * it suffices that the inclusion `algebra_map R S : R → S` is nontrivial
 * the function `f' : V'' → V'` doesn't need to be injective
-/
theorem FinrankQuotientMap.linear_independent_of_nontrivial [IsDomain R] [IsDedekindDomain R]
    (hRS : (algebraMap R S).ker ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f)
    (f' : V'' →ₗ[R] V') {ι : Type _} {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) :
    LinearIndependent K (f ∘ b) := by
  contrapose! hb' with hb
  -- Informally, if we have a nontrivial linear dependence with coefficients `g` in `K`,
  -- then we can find a linear dependence with coefficients `I.quotient.mk g'` in `R/I`,
  -- where `I = ker (algebra_map R S)`.
  -- We make use of the same principle but stay in `R` everywhere.
  simp only [linear_independent_iff', not_forall] at hb⊢
  obtain ⟨s, g, eq, j', hj's, hj'g⟩ := hb
  use s
  obtain ⟨a, hag, j, hjs, hgI⟩ := Ideal.exist_integer_multiples_not_mem hRS s g hj's hj'g
  choose g'' hg'' using hag
  letI := Classical.propDecidable
  let g' i := if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i :=
    by
    intro i hi
    exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
  have hgI : algebraMap R S (g' j) ≠ 0 :=
    by
    simp only [FractionalIdeal.mem_coe_ideal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine' ⟨fun i => algebraMap R S (g' i), _, j, hjs, hgI⟩
  have eq : f (∑ i in s, g' i • b i) = 0 :=
    by
    rw [LinearMap.map_sum, ← smul_zero a, ← Eq, Finset.smul_sum, Finset.sum_congr rfl]
    intro i hi
    rw [LinearMap.map_smul, ← IsScalarTower.algebra_map_smul K, hg' i hi, ← smul_assoc, smul_eq_mul]
    infer_instance
  simp only [IsScalarTower.algebra_map_smul, ← LinearMap.map_smul, ← LinearMap.map_sum,
    (f.map_eq_zero_iff hf).mp Eq, LinearMap.map_zero]
#align
  ideal.finrank_quotient_map.linear_independent_of_nontrivial Ideal.FinrankQuotientMap.linear_independent_of_nontrivial

open Matrix

variable {K}

omit hRK

/-- If `b` mod `p` spans `S/p` as `R/p`-space, then `b` itself spans `Frac(S)` as `K`-space.

Here,
 * `p` is an ideal of `R` such that `R / p` is nontrivial
 * `K` is a field that has an embedding of `R` (in particular we can take `K = Frac(R)`)
 * `L` is a field extension of `K`
 * `S` is the integral closure of `R` in `L`

More precisely, we avoid quotients in this statement and instead require that `b ∪ pS` spans `S`.
-/
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [IsNoetherian R S]
    [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [IsIntegralClosure S R L]
    [NoZeroSMulDivisors R K] (hp : p ≠ ⊤) (b : Set S)
    (hb' : Submodule.span R b ⊔ (p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ :=
  by
  have hRL : Function.Injective (algebraMap R L) :=
    by
    rw [IsScalarTower.algebra_map_eq R K L]
    exact (algebraMap K L).Injective.comp (NoZeroSMulDivisors.algebra_map_injective R K)
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  set M : Submodule R S := Submodule.span R b with hM
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  letI h : Module.Finite R (S ⧸ M) :=
    Module.Finite.ofSurjective (Submodule.mkq _) (Submodule.Quotient.mk_surjective _)
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin _ _ _ h
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkq (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkq]
      _ = ⊤ := by rw [Ideal.smul_top_eq_map, (Submodule.map_mkq_eq_top M _).mpr hb']
      
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Fin n → R, (∀ i, a' i ∈ p) ∧ (∑ i, a' i • a i) = x :=
    by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1 _
    · refine' ⟨fun i => a'' i, fun i => ha'' _, _⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
    · rw [ha, smul_top_eq]
      exact Submodule.mem_top
  choose A' hA'p hA' using fun i => exists_sum (a i)
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
  let A : Matrix (Fin n) (Fin n) R := A' - 1
  let B := A.adjugate
  have A_smul : ∀ i, (∑ j, A i j • a j) = 0 := by
    intros
    simp only [A, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hA', Matrix.one_apply, ite_smul,
      one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B ⬝ A) i j • a j := _
      _ = ∑ k, B i k • ∑ j, A k j • a j := _
      _ = 0 := Finset.sum_eq_zero fun k _ => _
      
    ·
      simp only [Matrix.adjugate_mul, Pi.smul_apply, Matrix.one_apply, mul_ite, ite_smul,
        smul_eq_mul, mul_one, mul_zero, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true]
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
    · rw [A_smul, smul_zero]
  -- In the rings of integers we have the desired inclusion.
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M :=
    by
    intro x hx
    rw [Submodule.restrict_scalars_mem] at hx
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    simp_rw [← quot_x_eq, Finset.smul_sum, smul_comm A.det, d_smul, smul_zero,
      Finset.sum_const_zero]
  -- So now we lift everything to the fraction field.
  refine'
    top_le_iff.mp
      (calc
        ⊤ = (Ideal.span {algebraMap R L A.det}).restrictScalars K := _
        _ ≤ Submodule.span K (algebraMap S L '' b) := _
        )
  -- Because `det A ≠ 0`, we have `span L {det A} = ⊤`.
  · rw [eq_comm, Submodule.restrict_scalars_eq_top_iff, Ideal.span_singleton_eq_top]
    refine'
      IsUnit.mk0 _
        ((map_ne_zero_iff (algebraMap R L) hRL).mpr
          (@ne_zero_of_map _ _ _ _ _ _ (Ideal.Quotient.mk p) _ _))
    haveI := Ideal.Quotient.nontrivial hp
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det, RingHom.map_matrix_apply]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (A' - 1)) := rfl
      _ =
          Matrix.det fun i j =>
            (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Fin n) (Fin n) (R ⧸ p)) i j :=
        _
      _ = Matrix.det (-1 : Matrix (Fin n) (Fin n) (R ⧸ p)) := _
      _ = (-1 : R ⧸ p) ^ n := by rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      _ ≠ 0 := IsUnit.ne_zero (is_unit_one.neg.pow _)
      
    · refine' congr_arg Matrix.det (Matrix.ext fun i j => _)
      rw [map_sub, RingHom.map_matrix_apply, map_one]
      rfl
    · refine' congr_arg Matrix.det (Matrix.ext fun i j => _)
      rw [ideal.quotient.eq_zero_iff_mem.mpr (hA'p i j), zero_sub]
      rfl
  -- And we conclude `L = span L {det A} ≤ span K b`, so `span K b` spans everything.
  · intro x hx
    rw [Submodule.restrict_scalars_mem, IsScalarTower.algebra_map_apply R S L] at hx
    refine' IsFractionRing.ideal_span_singleton_map_subset R _ hRL span_d hx
    haveI : NoZeroSMulDivisors R L := NoZeroSMulDivisors.of_algebra_map_injective hRL
    rw [← IsFractionRing.is_algebraic_iff' R S]
    intro x
    exact IsIntegral.is_algebraic _ (is_integral_of_noetherian inferInstance _)
#align ideal.finrank_quotient_map.span_eq_top Ideal.FinrankQuotientMap.span_eq_top

include hRK

variable (K L)

/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
theorem finrank_quotient_map [IsDomain R] [IsDomain S] [IsDedekindDomain R] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L]
    [hp : p.IsMaximal] [IsNoetherian R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L :=
  by
  -- Choose an arbitrary basis `b` for `[S/pS : R/p]`.
  -- We'll use the previous results to turn it into a basis on `[Frac(S) : Frac(R)]`.
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  let ι := Module.Free.ChooseBasisIndex (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  let b : Basis ι (R ⧸ p) (S ⧸ map (algebraMap R S) p) := Module.Free.chooseBasis _ _
  -- Namely, choose a representative `b' i : S` for each `b i : S / pS`.
  let b' : ι → S := fun i => (Ideal.Quotient.mk_surjective (b i)).some
  have b_eq_b' : ⇑b = (Submodule.mkq _).restrictScalars R ∘ b' :=
    funext fun i => (Ideal.Quotient.mk_surjective (b i)).some_spec.symm
  -- We claim `b'` is a basis for `Frac(S)` over `Frac(R)` because it is linear independent
  -- and spans the whole of `Frac(S)`.
  let b'' : ι → L := algebraMap S L ∘ b'
  have b''_li : LinearIndependent _ b'' := _
  have b''_sp : Submodule.span _ (Set.range b'') = ⊤ := _
  -- Since the two bases have the same index set, the spaces have the same dimension.
  let c : Basis ι K L := Basis.mk b''_li b''_sp.ge
  rw [finrank_eq_card_basis b, finrank_eq_card_basis c]
  -- It remains to show that the basis is indeed linear independent and spans the whole space.
  · rw [Set.range_comp]
    refine' finrank_quotient_map.span_eq_top p hp.ne_top _ (top_le_iff.mp _)
    -- The nicest way to show `S ≤ span b' ⊔ pS` is by reducing both sides modulo pS.
    -- However, this would imply distinguishing between `pS` as `S`-ideal,
    -- and `pS` as `R`-submodule, since they have different (non-defeq) quotients.
    -- Instead we'll lift `x mod pS ∈ span b` to `y ∈ span b'` for some `y - x ∈ pS`.
    intro x hx
    have mem_span_b :
      ((Submodule.mkq (map (algebraMap R S) p)) x : S ⧸ map (algebraMap R S) p) ∈
        Submodule.span (R ⧸ p) (Set.range b) :=
      b.mem_span _
    rw [← @Submodule.restrict_scalars_mem R,
      Algebra.span_restrict_scalars_eq_span_of_surjective
        (show Function.Surjective (algebraMap R (R ⧸ p)) from Ideal.Quotient.mk_surjective) _,
      b_eq_b', Set.range_comp, ← Submodule.map_span] at mem_span_b
    obtain ⟨y, y_mem, y_eq⟩ := submodule.mem_map.mp mem_span_b
    suffices y + -(y - x) ∈ _ by simpa
    rw [LinearMap.restrict_scalars_apply, Submodule.mkq_apply, Submodule.mkq_apply,
      Submodule.Quotient.eq] at y_eq
    exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
  · have := b.linear_independent
    rw [b_eq_b'] at this
    convert
      finrank_quotient_map.linear_independent_of_nontrivial K _
        ((Algebra.linearMap S L).restrictScalars R) _ ((Submodule.mkq _).restrictScalars R) this
    · rw [quotient.algebra_map_eq, Ideal.mk_ker]
      exact hp.ne_top
    · exact IsFractionRing.injective S L
#align ideal.finrank_quotient_map Ideal.finrank_quotient_map

end FinrankQuotientMap

section FactLeComap

-- mathport name: expre
local notation "e" => ramificationIdx f p P

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index\nof `P` over `p`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `Quotient.algebraQuotientPowRamificationIdx [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Algebra
         [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
          (Algebra.Quotient.«term_⧸_»
           `S
           " ⧸ "
           («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))])))
      (Command.declValSimple
       ":="
       (Term.app
        `Quotient.algebraQuotientOfLeComap
        [(Term.app (Term.proj `Ideal.map_le_iff_le_comap "." `mp) [`le_pow_ramification_idx])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.algebraQuotientOfLeComap
       [(Term.app (Term.proj `Ideal.map_le_iff_le_comap "." `mp) [`le_pow_ramification_idx])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `Ideal.map_le_iff_le_comap "." `mp) [`le_pow_ramification_idx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_pow_ramification_idx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Ideal.map_le_iff_le_comap "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Ideal.map_le_iff_le_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `Ideal.map_le_iff_le_comap "." `mp) [`le_pow_ramification_idx])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.algebraQuotientOfLeComap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `Algebra
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
        (Algebra.Quotient.«term_⧸_»
         `S
         " ⧸ "
         («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_»
       `S
       " ⧸ "
       («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
      of `P` over `p`. -/
    noncomputable
  instance
    Quotient.algebraQuotientPowRamificationIdx
    : Algebra R ⧸ p S ⧸ P ^ e
    := Quotient.algebraQuotientOfLeComap Ideal.map_le_iff_le_comap . mp le_pow_ramification_idx
#align
  ideal.quotient.algebra_quotient_pow_ramification_idx Ideal.Quotient.algebraQuotientPowRamificationIdx

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `Quotient.algebra_map_quotient_pow_ramification_idx [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `R] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `algebraMap
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Algebra.Quotient.«term_⧸_»
            `S
            " ⧸ "
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
           (Term.app `Ideal.Quotient.mk [`p `x])])
         "="
         (Term.app `Ideal.Quotient.mk [(Term.hole "_") (Term.app `f [`x])]))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `algebraMap
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
         (Algebra.Quotient.«term_⧸_»
          `S
          " ⧸ "
          («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
         (Term.app `Ideal.Quotient.mk [`p `x])])
       "="
       (Term.app `Ideal.Quotient.mk [(Term.hole "_") (Term.app `f [`x])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.Quotient.mk [(Term.hole "_") (Term.app `f [`x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `f [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`x]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `algebraMap
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
        (Algebra.Quotient.«term_⧸_»
         `S
         " ⧸ "
         («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
        (Term.app `Ideal.Quotient.mk [`p `x])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.Quotient.mk [`p `x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.Quotient.mk [`p `x])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Quotient.«term_⧸_»
       `S
       " ⧸ "
       («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    Quotient.algebra_map_quotient_pow_ramification_idx
    ( x : R ) : algebraMap R ⧸ p S ⧸ P ^ e Ideal.Quotient.mk p x = Ideal.Quotient.mk _ f x
    := rfl
#align
  ideal.quotient.algebra_map_quotient_pow_ramification_idx Ideal.Quotient.algebra_map_quotient_pow_ramification_idx

variable [hfp : NeZero (ramificationIdx f p P)]

include hfp

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferrable.
-/
def Quotient.algebraQuotientOfRamificationIdxNeZero : Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLeComap (le_comap_of_ramification_idx_ne_zero hfp.out)
#align
  ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

-- In this file, the value for `f` can be inferred.
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem Quotient.algebra_map_quotient_of_ramification_idx_ne_zero (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk _ (f x) :=
  rfl
#align
  ideal.quotient.algebra_map_quotient_of_ramification_idx_ne_zero Ideal.Quotient.algebra_map_quotient_of_ramification_idx_ne_zero

omit hfp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment "/--" "The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `powQuotSuccInclusion [])
      (Command.optDeclSig
       [(Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Module.LinearMap.«term_→ₗ[_]_»
          (Term.app
           `Ideal.map
           [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
            («term_^_» `P "^" («term_+_» `i "+" (num "1")))])
          " →ₗ["
          (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
          "] "
          (Term.app
           `Ideal.map
           [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
            («term_^_» `P "^" `i)])))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           [`x]
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [`x
             ","
             (Term.app
              `Ideal.map_mono
              [(Term.app `Ideal.pow_le_pow [(Term.proj `i "." `le_succ)])
               (Term.proj `x "." (fieldIdx "2"))])]
            "⟩"))))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `map_add' [`x `y] [] ":=" `rfl)))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `map_smul' [`c `x] [] ":=" `rfl)))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`x
        ","
        (Term.app
         `Ideal.map_mono
         [(Term.app `Ideal.pow_le_pow [(Term.proj `i "." `le_succ)])
          (Term.proj `x "." (fieldIdx "2"))])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.map_mono
       [(Term.app `Ideal.pow_le_pow [(Term.proj `i "." `le_succ)])
        (Term.proj `x "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `x "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ideal.pow_le_pow [(Term.proj `i "." `le_succ)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `i "." `le_succ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.pow_le_pow [(Term.proj `i "." `le_succ)])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.map_mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Module.LinearMap.«term_→ₗ[_]_»
       (Term.app
        `Ideal.map
        [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
         («term_^_» `P "^" («term_+_» `i "+" (num "1")))])
       " →ₗ["
       (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
       "] "
       (Term.app
        `Ideal.map
        [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
         («term_^_» `P "^" `i)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.map
       [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
        («term_^_» `P "^" `i)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" `i)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_^_» `P "^" `i) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/ @[ simps ]
  def
    powQuotSuccInclusion
    ( i : ℕ ) : Ideal.map P ^ e P ^ i + 1 →ₗ[ R ⧸ p ] Ideal.map P ^ e P ^ i
    where
      toFun x := ⟨ x , Ideal.map_mono Ideal.pow_le_pow i . le_succ x . 2 ⟩
        map_add' x y := rfl
        map_smul' c x := rfl
#align ideal.pow_quot_succ_inclusion Ideal.powQuotSuccInclusion

theorem pow_quot_succ_inclusion_injective (i : ℕ) :
    Function.Injective (powQuotSuccInclusion f p P i) :=
  by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ hx0
  rw [Subtype.ext_iff] at hx0⊢
  rwa [pow_quot_succ_inclusion_apply_coe] at hx0
#align ideal.pow_quot_succ_inclusion_injective Ideal.pow_quot_succ_inclusion_injective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.\nSee `quotient_to_quotient_range_pow_quot_succ` for this as a linear map,\nand `quotient_range_pow_quot_succ_inclusion_equiv` for this as a linear equivalence.\n-/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `quotientToQuotientRangePowQuotSuccAux [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder "{" [`a] [":" `S] "}")
        (Term.explicitBinder "(" [`a_mem] [":" («term_∈_» `a "∈" («term_^_» `P "^" `i))] [] ")")]
       [(Term.typeSpec
         ":"
         (Term.arrow
          (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
          "→"
          (Algebra.Quotient.«term_⧸_»
           (Term.app
            (Term.proj («term_^_» `P "^" `i) "." `map)
            [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
           " ⧸ "
           (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))))])
      (Command.declValSimple
       ":="
       (Term.app
        `Quotient.map'
        [(Term.fun
          "fun"
          (Term.basicFun
           [`x]
           [(Term.typeSpec ":" `S)]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.app
              `Ideal.mem_map_of_mem
              [(Term.hole "_") (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])])]
            "⟩")))
         (Term.fun
          "fun"
          (Term.basicFun
           [`x `y `h]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.quotient_rel_r_def)] "]")
                [(Tactic.location
                  "at"
                  (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `_root_.map_mul)
                  ","
                  (Tactic.simpLemma [] [] `LinearMap.mem_range)]
                 "]"]
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.anonymousCtor
                   "⟨"
                   [(Term.hole "_")
                    ","
                    (Term.app
                     `Ideal.mem_map_of_mem
                     [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
                   "⟩")
                  ","
                  (Term.hole "_")]
                 "⟩"))
               []
               (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                  ","
                  (Tactic.rwRule [] `Subtype.coe_mk)
                  ","
                  (Tactic.rwRule [] `Submodule.coe_sub)
                  ","
                  (Tactic.rwRule [] `Subtype.coe_mk)
                  ","
                  (Tactic.rwRule [] `Subtype.coe_mk)
                  ","
                  (Tactic.rwRule [] `_root_.map_mul)
                  ","
                  (Tactic.rwRule [] `map_sub)
                  ","
                  (Tactic.rwRule [] `sub_mul)]
                 "]")
                [])])))))])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.map'
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x]
          [(Term.typeSpec ":" `S)]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.hole "_")
            ","
            (Term.app
             `Ideal.mem_map_of_mem
             [(Term.hole "_") (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])])]
           "⟩")))
        (Term.fun
         "fun"
         (Term.basicFun
          [`x `y `h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.quotient_rel_r_def)] "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `_root_.map_mul)
                 ","
                 (Tactic.simpLemma [] [] `LinearMap.mem_range)]
                "]"]
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.anonymousCtor
                  "⟨"
                  [(Term.hole "_")
                   ","
                   (Term.app
                    `Ideal.mem_map_of_mem
                    [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
                  "⟩")
                 ","
                 (Term.hole "_")]
                "⟩"))
              []
              (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                 ","
                 (Tactic.rwRule [] `Subtype.coe_mk)
                 ","
                 (Tactic.rwRule [] `Submodule.coe_sub)
                 ","
                 (Tactic.rwRule [] `Subtype.coe_mk)
                 ","
                 (Tactic.rwRule [] `Subtype.coe_mk)
                 ","
                 (Tactic.rwRule [] `_root_.map_mul)
                 ","
                 (Tactic.rwRule [] `map_sub)
                 ","
                 (Tactic.rwRule [] `sub_mul)]
                "]")
               [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.quotient_rel_r_def)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `_root_.map_mul)
               ","
               (Tactic.simpLemma [] [] `LinearMap.mem_range)]
              "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.app
                  `Ideal.mem_map_of_mem
                  [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
                "⟩")
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `Submodule.coe_sub)
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `_root_.map_mul)
               ","
               (Tactic.rwRule [] `map_sub)
               ","
               (Tactic.rwRule [] `sub_mul)]
              "]")
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.quotient_rel_r_def)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `_root_.map_mul)
             ","
             (Tactic.simpLemma [] [] `LinearMap.mem_range)]
            "]"]
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.app
                `Ideal.mem_map_of_mem
                [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
              "⟩")
             ","
             (Term.hole "_")]
            "⟩"))
          []
          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
             ","
             (Tactic.rwRule [] `Subtype.coe_mk)
             ","
             (Tactic.rwRule [] `Submodule.coe_sub)
             ","
             (Tactic.rwRule [] `Subtype.coe_mk)
             ","
             (Tactic.rwRule [] `Subtype.coe_mk)
             ","
             (Tactic.rwRule [] `_root_.map_mul)
             ","
             (Tactic.rwRule [] `map_sub)
             ","
             (Tactic.rwRule [] `sub_mul)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)
         ","
         (Tactic.rwRule [] `Submodule.coe_sub)
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)
         ","
         (Tactic.rwRule [] `_root_.map_mul)
         ","
         (Tactic.rwRule [] `map_sub)
         ","
         (Tactic.rwRule [] `sub_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `_root_.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_quot_succ_inclusion_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.hole "_")
           ","
           (Term.app
            `Ideal.mem_map_of_mem
            [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
          "⟩")
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.app
           `Ideal.mem_map_of_mem
           [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
         "⟩")
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app
         `Ideal.mem_map_of_mem
         [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.mem_map_of_mem [(Term.hole "_") (Term.app `Ideal.mul_mem_mul [`h `a_mem])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.mul_mem_mul [`h `a_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.mul_mem_mul [`h `a_mem])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mem_map_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `_root_.map_mul) "," (Tactic.simpLemma [] [] `LinearMap.mem_range)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `_root_.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Submodule.quotient_rel_r_def)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.quotient_rel_r_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        [(Term.typeSpec ":" `S)]
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.app
           `Ideal.mem_map_of_mem
           [(Term.hole "_") (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])])]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app
         `Ideal.mem_map_of_mem
         [(Term.hole "_") (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mem_map_of_mem
       [(Term.hole "_") (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mul_mem_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mem_map_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun
      "fun"
      (Term.basicFun
       [`x]
       [(Term.typeSpec ":" `S)]
       "=>"
       (Term.anonymousCtor
        "⟨"
        [(Term.hole "_")
         ","
         (Term.app
          `Ideal.mem_map_of_mem
          [(Term.hole "_")
           (Term.paren "(" (Term.app `Ideal.mul_mem_left [(Term.hole "_") `x `a_mem]) ")")])]
        "⟩")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.map'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
       "→"
       (Algebra.Quotient.«term_⧸_»
        (Term.app
         (Term.proj («term_^_» `P "^" `i) "." `map)
         [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
        " ⧸ "
        (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_»
       (Term.app
        (Term.proj («term_^_» `P "^" `i) "." `map)
        [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
       " ⧸ "
       (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `powQuotSuccInclusion [`f `p `P `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `powQuotSuccInclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `powQuotSuccInclusion [`f `p `P `i])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app
       (Term.proj («term_^_» `P "^" `i) "." `map)
       [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
      See `quotient_to_quotient_range_pow_quot_succ` for this as a linear map,
      and `quotient_range_pow_quot_succ_inclusion_equiv` for this as a linear equivalence.
      -/
    noncomputable
  def
    quotientToQuotientRangePowQuotSuccAux
    { i : ℕ } { a : S } ( a_mem : a ∈ P ^ i )
      : S ⧸ P → P ^ i . map P ^ e ⧸ powQuotSuccInclusion f p P i . range
    :=
      Quotient.map'
        fun x : S => ⟨ _ , Ideal.mem_map_of_mem _ Ideal.mul_mem_left _ x a_mem ⟩
          fun
            x y h
              =>
              by
                rw [ Submodule.quotient_rel_r_def ] at h ⊢
                  simp only [ _root_.map_mul , LinearMap.mem_range ]
                  refine' ⟨ ⟨ _ , Ideal.mem_map_of_mem _ Ideal.mul_mem_mul h a_mem ⟩ , _ ⟩
                  ext
                  rw
                    [
                      pow_quot_succ_inclusion_apply_coe
                        ,
                        Subtype.coe_mk
                        ,
                        Submodule.coe_sub
                        ,
                        Subtype.coe_mk
                        ,
                        Subtype.coe_mk
                        ,
                        _root_.map_mul
                        ,
                        map_sub
                        ,
                        sub_mul
                      ]
#align
  ideal.quotient_to_quotient_range_pow_quot_succ_aux Ideal.quotientToQuotientRangePowQuotSuccAux

theorem quotient_to_quotient_range_pow_quot_succ_aux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i)
    (x : S) :
    quotientToQuotientRangePowQuotSuccAux f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  by apply Quotient.map'_mk'
#align
  ideal.quotient_to_quotient_range_pow_quot_succ_aux_mk Ideal.quotient_to_quotient_range_pow_quot_succ_aux_mk

include hfp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "`S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `quotientToQuotientRangePowQuotSucc [])
      (Command.optDeclSig
       [(Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.implicitBinder "{" [`a] [":" `S] "}")
        (Term.explicitBinder "(" [`a_mem] [":" («term_∈_» `a "∈" («term_^_» `P "^" `i))] [] ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Module.LinearMap.«term_→ₗ[_]_»
          (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
          " →ₗ["
          (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
          "] "
          (Algebra.Quotient.«term_⧸_»
           (Term.app
            (Term.proj («term_^_» `P "^" `i) "." `map)
            [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
           " ⧸ "
           (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toFun
           []
           []
           ":="
           (Term.app `quotientToQuotientRangePowQuotSuccAux [`f `p `P `a_mem]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_add'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`x `y])
               ";"
               (Tactic.refine'
                "refine'"
                (Term.app
                 `Quotient.inductionOn'
                 [`x
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.app
                     `Quotient.inductionOn'
                     [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                  ","
                  (Tactic.simpLemma
                   []
                   [(patternIgnore (token.«← » "←"))]
                   `Submodule.Quotient.mk_add)
                  ","
                  (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
                  ","
                  (Tactic.simpLemma [] [] `add_mul)]
                 "]"]
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
               []
               (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.tacticRfl "rfl")]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_smul'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.intro "intro" [`x `y])
               ";"
               (Tactic.refine'
                "refine'"
                (Term.app
                 `Quotient.inductionOn'
                 [`x
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`x]
                    []
                    "=>"
                    (Term.app
                     `Quotient.inductionOn'
                     [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                  ","
                  (Tactic.simpLemma
                   []
                   [(patternIgnore (token.«← » "←"))]
                   `Submodule.Quotient.mk_add)
                  ","
                  (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
                  ","
                  (Tactic.simpLemma [] [] `RingHom.id_apply)]
                 "]"]
                [])
               []
               (Tactic.refine'
                "refine'"
                (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
               []
               (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
               []
               (Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Subtype.coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `_root_.map_mul)
                  ","
                  (Tactic.simpLemma [] [] `Algebra.smul_def)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.coe_mk)
                  ","
                  (Tactic.simpLemma [] [] `mul_assoc)
                  ","
                  (Tactic.simpLemma [] [] `Ideal.Quotient.mk_eq_mk)
                  ","
                  (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
                  ","
                  (Tactic.simpLemma
                   []
                   []
                   `Ideal.Quotient.algebra_map_quotient_pow_ramification_idx)]
                 "]"]
                [])]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `y])
          ";"
          (Tactic.refine'
           "refine'"
           (Term.app
            `Quotient.inductionOn'
            [`x
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                `Quotient.inductionOn'
                [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Submodule.Quotient.mk_add)
             ","
             (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
             ","
             (Tactic.simpLemma [] [] `RingHom.id_apply)]
            "]"]
           [])
          []
          (Tactic.refine' "refine'" (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
          []
          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Subtype.coe_mk)
             ","
             (Tactic.simpLemma [] [] `_root_.map_mul)
             ","
             (Tactic.simpLemma [] [] `Algebra.smul_def)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_mk)
             ","
             (Tactic.simpLemma [] [] `mul_assoc)
             ","
             (Tactic.simpLemma [] [] `Ideal.Quotient.mk_eq_mk)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
             ","
             (Tactic.simpLemma [] [] `Ideal.Quotient.algebra_map_quotient_pow_ramification_idx)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `_root_.map_mul)
         ","
         (Tactic.simpLemma [] [] `Algebra.smul_def)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_mk)
         ","
         (Tactic.simpLemma [] [] `mul_assoc)
         ","
         (Tactic.simpLemma [] [] `Ideal.Quotient.mk_eq_mk)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_smul_of_tower)
         ","
         (Tactic.simpLemma [] [] `Ideal.Quotient.algebra_map_quotient_pow_ramification_idx)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.algebra_map_quotient_pow_ramification_idx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_smul_of_tower
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Algebra.smul_def
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `_root_.map_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `Submodule.Quotient.mk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Submodule.Quotient.mk_add)
         ","
         (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
         ","
         (Tactic.simpLemma [] [] `RingHom.id_apply)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `RingHom.id_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `quotient_to_quotient_range_pow_quot_succ_aux_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.mk_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.mk'_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Quotient.inductionOn'
        [`x
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            `Quotient.inductionOn'
            [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.inductionOn'
       [`x
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `Quotient.inductionOn'
           [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         `Quotient.inductionOn'
         [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.inductionOn'
       [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.inductionOn'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.inductionOn'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `y])
          ";"
          (Tactic.refine'
           "refine'"
           (Term.app
            `Quotient.inductionOn'
            [`x
             (Term.fun
              "fun"
              (Term.basicFun
               [`x]
               []
               "=>"
               (Term.app
                `Quotient.inductionOn'
                [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
             ","
             (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Submodule.Quotient.mk_add)
             ","
             (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
             ","
             (Tactic.simpLemma [] [] `add_mul)]
            "]"]
           [])
          []
          (Tactic.refine' "refine'" (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
          []
          (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
          []
          (Tactic.tacticRfl "rfl")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `congr_arg [`Submodule.Quotient.mk (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `Submodule.Quotient.mk
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `congr_arg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
         ","
         (Tactic.simpLemma [] [(patternIgnore (token.«← » "←"))] `Submodule.Quotient.mk_add)
         ","
         (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_aux_mk)
         ","
         (Tactic.simpLemma [] [] `add_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `add_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `quotient_to_quotient_range_pow_quot_succ_aux_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.mk_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.mk'_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `Quotient.inductionOn'
        [`x
         (Term.fun
          "fun"
          (Term.basicFun
           [`x]
           []
           "=>"
           (Term.app
            `Quotient.inductionOn'
            [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.inductionOn'
       [`x
        (Term.fun
         "fun"
         (Term.basicFun
          [`x]
          []
          "=>"
          (Term.app
           `Quotient.inductionOn'
           [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         `Quotient.inductionOn'
         [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Quotient.inductionOn'
       [`y (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`y] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.inductionOn'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Quotient.inductionOn'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `quotientToQuotientRangePowQuotSuccAux [`f `p `P `a_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotientToQuotientRangePowQuotSuccAux
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Module.LinearMap.«term_→ₗ[_]_»
       (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
       " →ₗ["
       (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
       "] "
       (Algebra.Quotient.«term_⧸_»
        (Term.app
         (Term.proj («term_^_» `P "^" `i) "." `map)
         [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
        " ⧸ "
        (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_»
       (Term.app
        (Term.proj («term_^_» `P "^" `i) "." `map)
        [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
       " ⧸ "
       (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `powQuotSuccInclusion [`f `p `P `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `powQuotSuccInclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `powQuotSuccInclusion [`f `p `P `i])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app
       (Term.proj («term_^_» `P "^" `i) "." `map)
       [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
    noncomputable
  def
    quotientToQuotientRangePowQuotSucc
    { i : ℕ } { a : S } ( a_mem : a ∈ P ^ i )
      : S ⧸ P →ₗ[ R ⧸ p ] P ^ i . map P ^ e ⧸ powQuotSuccInclusion f p P i . range
    where
      toFun := quotientToQuotientRangePowQuotSuccAux f p P a_mem
        map_add'
          :=
          by
            intro x y
              ;
              refine' Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => _
              simp
                only
                [
                  Submodule.Quotient.mk'_eq_mk
                    ,
                    ← Submodule.Quotient.mk_add
                    ,
                    quotient_to_quotient_range_pow_quot_succ_aux_mk
                    ,
                    add_mul
                  ]
              refine' congr_arg Submodule.Quotient.mk _
              ext
              rfl
        map_smul'
          :=
          by
            intro x y
              ;
              refine' Quotient.inductionOn' x fun x => Quotient.inductionOn' y fun y => _
              simp
                only
                [
                  Submodule.Quotient.mk'_eq_mk
                    ,
                    ← Submodule.Quotient.mk_add
                    ,
                    quotient_to_quotient_range_pow_quot_succ_aux_mk
                    ,
                    RingHom.id_apply
                  ]
              refine' congr_arg Submodule.Quotient.mk _
              ext
              simp
                only
                [
                  Subtype.coe_mk
                    ,
                    _root_.map_mul
                    ,
                    Algebra.smul_def
                    ,
                    Submodule.coe_mk
                    ,
                    mul_assoc
                    ,
                    Ideal.Quotient.mk_eq_mk
                    ,
                    Submodule.coe_smul_of_tower
                    ,
                    Ideal.Quotient.algebra_map_quotient_pow_ramification_idx
                  ]
#align ideal.quotient_to_quotient_range_pow_quot_succ Ideal.quotientToQuotientRangePowQuotSucc

theorem quotient_to_quotient_range_pow_quot_succ_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  quotient_to_quotient_range_pow_quot_succ_aux_mk f p P a_mem x
#align
  ideal.quotient_to_quotient_range_pow_quot_succ_mk Ideal.quotient_to_quotient_range_pow_quot_succ_mk

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `quotient_to_quotient_range_pow_quot_succ_injective [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`hi]
         [":" («term_<_» `i "<" (Ideal.NumberTheory.RamificationInertia.terme "e"))]
         []
         ")")
        (Term.implicitBinder "{" [`a] [":" `S] "}")
        (Term.explicitBinder "(" [`a_mem] [":" («term_∈_» `a "∈" («term_^_» `P "^" `i))] [] ")")
        (Term.explicitBinder
         "("
         [`a_not_mem]
         [":" («term_∉_» `a "∉" («term_^_» `P "^" («term_+_» `i "+" (num "1"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Function.Injective
         [(Term.app `quotientToQuotientRangePowQuotSucc [`f `p `P `a_mem])])))
      (Command.declValSimple
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [`x]
         []
         "=>"
         (Term.app
          (Term.app `Quotient.inductionOn' [`x])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x `y]
             []
             "=>"
             (Term.app
              (Term.app `Quotient.inductionOn' [`y])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`y `h]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`Pe_le_Pi1 []]
                        [(Term.typeSpec
                          ":"
                          («term_≤_»
                           («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                           "≤"
                           («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
                        ":="
                        (Term.app `Ideal.pow_le_pow [`hi]))))
                     []
                     (Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                        ","
                        (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                        ","
                        (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                        ","
                        (Tactic.simpLemma [] [] `LinearMap.mem_range)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.ext_iff)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.coe_mk)
                        ","
                        (Tactic.simpLemma [] [] `Submodule.coe_sub)]
                       "]"]
                      [(Tactic.location
                        "at"
                        (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
                     []
                     (Std.Tactic.rcases
                      "rcases"
                      [(Tactic.casesTarget [] `h)]
                      ["with"
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.tuple
                                     "⟨"
                                     [(Std.Tactic.RCases.rcasesPatLo
                                       (Std.Tactic.RCases.rcasesPatMed
                                        [(Std.Tactic.RCases.rcasesPat.one `z)])
                                       [])]
                                     "⟩")])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                  [])]
                                "⟩")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                             [])]
                           "⟩")])
                        [])])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                        ","
                        (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                        ","
                        (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
                        ","
                        (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                        ","
                        (Tactic.rwRule [] `Subtype.coe_mk)
                        ","
                        (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                        ","
                        (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
                        ","
                        (Tactic.rwRule [] `Ideal.Quotient.eq)
                        ","
                        (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj
                        (Term.app
                         `Ideal.IsPrime.mul_mem_pow
                         [(Term.hole "_")
                          (Term.app
                           (Term.proj
                            (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
                            "."
                            `mp)
                           [(Term.app `Pe_le_Pi1 [`h])])])
                        "."
                        `resolve_right)
                       [`a_not_mem]))])))))])))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x]
        []
        "=>"
        (Term.app
         (Term.app `Quotient.inductionOn' [`x])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`x `y]
            []
            "=>"
            (Term.app
             (Term.app `Quotient.inductionOn' [`y])
             [(Term.fun
               "fun"
               (Term.basicFun
                [`y `h]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`Pe_le_Pi1 []]
                       [(Term.typeSpec
                         ":"
                         («term_≤_»
                          («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                          "≤"
                          («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
                       ":="
                       (Term.app `Ideal.pow_le_pow [`hi]))))
                    []
                    (Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                       ","
                       (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                       ","
                       (Tactic.simpLemma [] [] `LinearMap.mem_range)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.ext_iff)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.coe_mk)
                       ","
                       (Tactic.simpLemma [] [] `Submodule.coe_sub)]
                      "]"]
                     [(Tactic.location
                       "at"
                       (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
                    []
                    (Std.Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] `h)]
                     ["with"
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.tuple
                                    "⟨"
                                    [(Std.Tactic.RCases.rcasesPatLo
                                      (Std.Tactic.RCases.rcasesPatMed
                                       [(Std.Tactic.RCases.rcasesPat.one `z)])
                                      [])]
                                    "⟩")])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hz)])
                                 [])]
                               "⟩")])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                            [])]
                          "⟩")])
                       [])])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                       ","
                       (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                       ","
                       (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
                       ","
                       (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                       ","
                       (Tactic.rwRule [] `Subtype.coe_mk)
                       ","
                       (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                       ","
                       (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
                       ","
                       (Tactic.rwRule [] `Ideal.Quotient.eq)
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj
                       (Term.app
                        `Ideal.IsPrime.mul_mem_pow
                        [(Term.hole "_")
                         (Term.app
                          (Term.proj
                           (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
                           "."
                           `mp)
                          [(Term.app `Pe_le_Pi1 [`h])])])
                       "."
                       `resolve_right)
                      [`a_not_mem]))])))))])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Quotient.inductionOn' [`x])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x `y]
          []
          "=>"
          (Term.app
           (Term.app `Quotient.inductionOn' [`y])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`y `h]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`Pe_le_Pi1 []]
                     [(Term.typeSpec
                       ":"
                       («term_≤_»
                        («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                        "≤"
                        («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
                     ":="
                     (Term.app `Ideal.pow_le_pow [`hi]))))
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                     ","
                     (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                     ","
                     (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                     ","
                     (Tactic.simpLemma [] [] `LinearMap.mem_range)
                     ","
                     (Tactic.simpLemma [] [] `Subtype.ext_iff)
                     ","
                     (Tactic.simpLemma [] [] `Subtype.coe_mk)
                     ","
                     (Tactic.simpLemma [] [] `Submodule.coe_sub)]
                    "]"]
                   [(Tactic.location
                     "at"
                     (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
                  []
                  (Std.Tactic.rcases
                   "rcases"
                   [(Tactic.casesTarget [] `h)]
                   ["with"
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed
                           [(Std.Tactic.RCases.rcasesPat.tuple
                             "⟨"
                             [(Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.tuple
                                  "⟨"
                                  [(Std.Tactic.RCases.rcasesPatLo
                                    (Std.Tactic.RCases.rcasesPatMed
                                     [(Std.Tactic.RCases.rcasesPat.one `z)])
                                    [])]
                                  "⟩")])
                               [])
                              ","
                              (Std.Tactic.RCases.rcasesPatLo
                               (Std.Tactic.RCases.rcasesPatMed
                                [(Std.Tactic.RCases.rcasesPat.one `hz)])
                               [])]
                             "⟩")])
                          [])
                         ","
                         (Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                          [])]
                        "⟩")])
                     [])])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                     ","
                     (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                     ","
                     (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
                     ","
                     (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                     ","
                     (Tactic.rwRule [] `Subtype.coe_mk)
                     ","
                     (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                     ","
                     (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
                     ","
                     (Tactic.rwRule [] `Ideal.Quotient.eq)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj
                     (Term.app
                      `Ideal.IsPrime.mul_mem_pow
                      [(Term.hole "_")
                       (Term.app
                        (Term.proj
                         (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
                         "."
                         `mp)
                        [(Term.app `Pe_le_Pi1 [`h])])])
                     "."
                     `resolve_right)
                    [`a_not_mem]))])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        (Term.app
         (Term.app `Quotient.inductionOn' [`y])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`y `h]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`Pe_le_Pi1 []]
                   [(Term.typeSpec
                     ":"
                     («term_≤_»
                      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                      "≤"
                      («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
                   ":="
                   (Term.app `Ideal.pow_le_pow [`hi]))))
                []
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                   ","
                   (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                   ","
                   (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                   ","
                   (Tactic.simpLemma [] [] `LinearMap.mem_range)
                   ","
                   (Tactic.simpLemma [] [] `Subtype.ext_iff)
                   ","
                   (Tactic.simpLemma [] [] `Subtype.coe_mk)
                   ","
                   (Tactic.simpLemma [] [] `Submodule.coe_sub)]
                  "]"]
                 [(Tactic.location
                   "at"
                   (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
                []
                (Std.Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] `h)]
                 ["with"
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `z)])
                                  [])]
                                "⟩")])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hz)])
                             [])]
                           "⟩")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                        [])]
                      "⟩")])
                   [])])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                   ","
                   (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                   ","
                   (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
                   ","
                   (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                   ","
                   (Tactic.rwRule [] `Subtype.coe_mk)
                   ","
                   (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                   ","
                   (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
                   ","
                   (Tactic.rwRule [] `Ideal.Quotient.eq)
                   ","
                   (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
                  "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj
                   (Term.app
                    `Ideal.IsPrime.mul_mem_pow
                    [(Term.hole "_")
                     (Term.app
                      (Term.proj
                       (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
                       "."
                       `mp)
                      [(Term.app `Pe_le_Pi1 [`h])])])
                   "."
                   `resolve_right)
                  [`a_not_mem]))])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Quotient.inductionOn' [`y])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`y `h]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.tacticHave_
               "have"
               (Term.haveDecl
                (Term.haveIdDecl
                 [`Pe_le_Pi1 []]
                 [(Term.typeSpec
                   ":"
                   («term_≤_»
                    («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                    "≤"
                    («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
                 ":="
                 (Term.app `Ideal.pow_le_pow [`hi]))))
              []
              (Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
                 ","
                 (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                 ","
                 (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                 ","
                 (Tactic.simpLemma [] [] `LinearMap.mem_range)
                 ","
                 (Tactic.simpLemma [] [] `Subtype.ext_iff)
                 ","
                 (Tactic.simpLemma [] [] `Subtype.coe_mk)
                 ","
                 (Tactic.simpLemma [] [] `Submodule.coe_sub)]
                "]"]
               [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
              []
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `h)]
               ["with"
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.tuple
                              "⟨"
                              [(Std.Tactic.RCases.rcasesPatLo
                                (Std.Tactic.RCases.rcasesPatMed
                                 [(Std.Tactic.RCases.rcasesPat.one `z)])
                                [])]
                              "⟩")])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                      [])]
                    "⟩")])
                 [])])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                 ","
                 (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                 ","
                 (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
                 ","
                 (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                 ","
                 (Tactic.rwRule [] `Subtype.coe_mk)
                 ","
                 (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
                 ","
                 (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
                 ","
                 (Tactic.rwRule [] `Ideal.Quotient.eq)
                 ","
                 (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
                "]")
               [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
              []
              (Tactic.exact
               "exact"
               (Term.app
                (Term.proj
                 (Term.app
                  `Ideal.IsPrime.mul_mem_pow
                  [(Term.hole "_")
                   (Term.app
                    (Term.proj
                     (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
                     "."
                     `mp)
                    [(Term.app `Pe_le_Pi1 [`h])])])
                 "."
                 `resolve_right)
                [`a_not_mem]))])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`y `h]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`Pe_le_Pi1 []]
               [(Term.typeSpec
                 ":"
                 («term_≤_»
                  («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                  "≤"
                  («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
               ":="
               (Term.app `Ideal.pow_le_pow [`hi]))))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
               ","
               (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
               ","
               (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
               ","
               (Tactic.simpLemma [] [] `LinearMap.mem_range)
               ","
               (Tactic.simpLemma [] [] `Subtype.ext_iff)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_mk)
               ","
               (Tactic.simpLemma [] [] `Submodule.coe_sub)]
              "]"]
             [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `h)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.tuple
                            "⟨"
                            [(Std.Tactic.RCases.rcasesPatLo
                              (Std.Tactic.RCases.rcasesPatMed
                               [(Std.Tactic.RCases.rcasesPat.one `z)])
                              [])]
                            "⟩")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
               ","
               (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
               ","
               (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.eq)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               (Term.app
                `Ideal.IsPrime.mul_mem_pow
                [(Term.hole "_")
                 (Term.app
                  (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
                  [(Term.app `Pe_le_Pi1 [`h])])])
               "."
               `resolve_right)
              [`a_not_mem]))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Pe_le_Pi1 []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                "≤"
                («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
             ":="
             (Term.app `Ideal.pow_le_pow [`hi]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
             ","
             (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
             ","
             (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
             ","
             (Tactic.simpLemma [] [] `LinearMap.mem_range)
             ","
             (Tactic.simpLemma [] [] `Subtype.ext_iff)
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_mk)
             ","
             (Tactic.simpLemma [] [] `Submodule.coe_sub)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] `h)]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                            [])]
                          "⟩")])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                       [])]
                     "⟩")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
             ","
             (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
             ","
             (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
             ","
             (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
             ","
             (Tactic.rwRule [] `Subtype.coe_mk)
             ","
             (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
             ","
             (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
             ","
             (Tactic.rwRule [] `Ideal.Quotient.eq)
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (Term.app
              `Ideal.IsPrime.mul_mem_pow
              [(Term.hole "_")
               (Term.app
                (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
                [(Term.app `Pe_le_Pi1 [`h])])])
             "."
             `resolve_right)
            [`a_not_mem]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.app
          `Ideal.IsPrime.mul_mem_pow
          [(Term.hole "_")
           (Term.app
            (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
            [(Term.app `Pe_le_Pi1 [`h])])])
         "."
         `resolve_right)
        [`a_not_mem]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         `Ideal.IsPrime.mul_mem_pow
         [(Term.hole "_")
          (Term.app
           (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
           [(Term.app `Pe_le_Pi1 [`h])])])
        "."
        `resolve_right)
       [`a_not_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        `Ideal.IsPrime.mul_mem_pow
        [(Term.hole "_")
         (Term.app
          (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
          [(Term.app `Pe_le_Pi1 [`h])])])
       "."
       `resolve_right)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `Ideal.IsPrime.mul_mem_pow
       [(Term.hole "_")
        (Term.app
         (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
         [(Term.app `Pe_le_Pi1 [`h])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
       [(Term.app `Pe_le_Pi1 [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Pe_le_Pi1 [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pe_le_Pi1
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Pe_le_Pi1 [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.sub_mem_iff_right
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) ")")
       "."
       `mp)
      [(Term.paren "(" (Term.app `Pe_le_Pi1 [`h]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.IsPrime.mul_mem_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Ideal.IsPrime.mul_mem_pow
      [(Term.hole "_")
       (Term.paren
        "("
        (Term.app
         (Term.proj
          (Term.paren "(" (Term.app `Submodule.sub_mem_iff_right [(Term.hole "_") `hz]) ")")
          "."
          `mp)
         [(Term.paren "(" (Term.app `Pe_le_Pi1 [`h]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)
         ","
         (Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `map_sub)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.eq)
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `sub_mul)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`h] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.quot_mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_quot_succ_inclusion_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
         ","
         (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
         ","
         (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi1]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hz] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sup_eq_left.mpr [`Pe_le_Pi1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pe_le_Pi1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sup_eq_left.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.mem_quotient_iff_mem_sup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.quot_mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] `h)]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                   [])]
                 "⟩")])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Submodule.Quotient.mk'_eq_mk)
         ","
         (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
         ","
         (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
         ","
         (Tactic.simpLemma [] [] `LinearMap.mem_range)
         ","
         (Tactic.simpLemma [] [] `Subtype.ext_iff)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_sub)]
        "]"]
       [(Tactic.location "at" (Tactic.locationHyp [`h] [(patternIgnore (token.«⊢» "⊢"))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `quotient_to_quotient_range_pow_quot_succ_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.mk'_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Pe_le_Pi1 []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
            "≤"
            («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
         ":="
         (Term.app `Ideal.pow_le_pow [`hi]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.pow_le_pow [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
       "≤"
       («term_^_» `P "^" («term_+_» `i "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `i "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  quotient_to_quotient_range_pow_quot_succ_injective
  [ IsDomain S ]
      [ IsDedekindDomain S ]
      [ P . IsPrime ]
      { i : ℕ }
      ( hi : i < e )
      { a : S }
      ( a_mem : a ∈ P ^ i )
      ( a_not_mem : a ∉ P ^ i + 1 )
    : Function.Injective quotientToQuotientRangePowQuotSucc f p P a_mem
  :=
    fun
      x
        =>
        Quotient.inductionOn' x
          fun
            x y
              =>
              Quotient.inductionOn' y
                fun
                  y h
                    =>
                    by
                      have Pe_le_Pi1 : P ^ e ≤ P ^ i + 1 := Ideal.pow_le_pow hi
                        simp
                          only
                          [
                            Submodule.Quotient.mk'_eq_mk
                              ,
                              quotient_to_quotient_range_pow_quot_succ_mk
                              ,
                              Submodule.Quotient.eq
                              ,
                              LinearMap.mem_range
                              ,
                              Subtype.ext_iff
                              ,
                              Subtype.coe_mk
                              ,
                              Submodule.coe_sub
                            ]
                          at h ⊢
                        rcases h with ⟨ ⟨ ⟨ z ⟩ , hz ⟩ , h ⟩
                        rw
                          [
                            Submodule.Quotient.quot_mk_eq_mk
                              ,
                              Ideal.Quotient.mk_eq_mk
                              ,
                              Ideal.mem_quotient_iff_mem_sup
                              ,
                              sup_eq_left.mpr Pe_le_Pi1
                            ]
                          at hz
                        rw
                          [
                            pow_quot_succ_inclusion_apply_coe
                              ,
                              Subtype.coe_mk
                              ,
                              Submodule.Quotient.quot_mk_eq_mk
                              ,
                              Ideal.Quotient.mk_eq_mk
                              ,
                              ← map_sub
                              ,
                              Ideal.Quotient.eq
                              ,
                              ← sub_mul
                            ]
                          at h
                        exact
                          Ideal.IsPrime.mul_mem_pow
                                _ Submodule.sub_mem_iff_right _ hz . mp Pe_le_Pi1 h
                              .
                              resolve_right
                            a_not_mem
#align
  ideal.quotient_to_quotient_range_pow_quot_succ_injective Ideal.quotient_to_quotient_range_pow_quot_succ_injective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `quotient_to_quotient_range_pow_quot_succ_surjective [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.explicitBinder
         "("
         [`hP0]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.instBinder "[" [`hP ":"] (Term.proj `P "." `IsPrime) "]")
        (Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`hi]
         [":" («term_<_» `i "<" (Ideal.NumberTheory.RamificationInertia.terme "e"))]
         []
         ")")
        (Term.implicitBinder "{" [`a] [":" `S] "}")
        (Term.explicitBinder "(" [`a_mem] [":" («term_∈_» `a "∈" («term_^_» `P "^" `i))] [] ")")
        (Term.explicitBinder
         "("
         [`a_not_mem]
         [":" («term_∉_» `a "∉" («term_^_» `P "^" («term_+_» `i "+" (num "1"))))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Function.Surjective
         [(Term.app `quotientToQuotientRangePowQuotSucc [`f `p `P `a_mem])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.rintro
            "rintro"
            [(Std.Tactic.RCases.rintroPat.one
              (Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.tuple
                    "⟨"
                    [(Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                           [])]
                         "⟩")])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                      [])]
                    "⟩")])
                 [])]
               "⟩"))]
            [])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Pe_le_Pi []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                 "≤"
                 («term_^_» `P "^" `i)))]
              ":="
              (Term.app `Ideal.pow_le_pow [`hi.le]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Pe_le_Pi1 []]
              [(Term.typeSpec
                ":"
                («term_≤_»
                 («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                 "≤"
                 («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
              ":="
              (Term.app `Ideal.pow_le_pow [`hi]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
              ","
              (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
              ","
              (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
              ","
              (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi]))]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
           []
           (Mathlib.Tactic.tacticSuffices_
            "suffices"
            [`hx' []]
            [(Term.typeSpec
              ":"
              («term_∈_»
               `x
               "∈"
               (Order.Basic.«term_⊔_»
                (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
                " ⊔ "
                («term_^_» `P "^" («term_+_» `i "+" (num "1"))))))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `submodule.mem_sup.mp [`hx'])]])
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `ideal.mem_span_singleton.mp [`hy'])]])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `Submodule.Quotient.mk [`y]) "," (Term.hole "_")]
               "⟩"))
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Submodule.Quotient.quot_mk_eq_mk)
                ","
                (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
                ","
                (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
                ","
                (Tactic.simpLemma [] [] `LinearMap.mem_range)
                ","
                (Tactic.simpLemma [] [] `Subtype.ext_iff)
                ","
                (Tactic.simpLemma [] [] `Subtype.coe_mk)
                ","
                (Tactic.simpLemma [] [] `Submodule.coe_sub)]
               "]"]
              [])
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.app
                   `Ideal.mem_map_of_mem
                   [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
                 "⟩")
                ","
                (Term.hole "_")]
               "⟩"))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
                ","
                (Tactic.rwRule [] `Subtype.coe_mk)
                ","
                (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
                ","
                (Tactic.rwRule [] `map_add)
                ","
                (Tactic.rwRule [] (Term.app `mul_comm [`y `a]))
                ","
                (Tactic.rwRule [] `sub_add_cancel')
                ","
                (Tactic.rwRule [] `map_neg)]
               "]")
              [])])
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [(Term.app `Ideal [`S])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `sup_eq_prod_inf_factors
                [(Term.hole "_") (Term.app `pow_ne_zero [(Term.hole "_") `hP0])]))
              ","
              (Tactic.rwRule [] `normalized_factors_pow)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `normalized_factors_irreducible
                [(Term.proj
                  (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
                  "."
                  `Irreducible)]))
              ","
              (Tactic.rwRule [] `normalize_eq)
              ","
              (Tactic.rwRule [] `Multiset.nsmul_singleton)
              ","
              (Tactic.rwRule [] `Multiset.inter_repeat)
              ","
              (Tactic.rwRule [] `Multiset.prod_repeat)]
             "]")
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               `Submodule.span_singleton_le_iff_mem)
              ","
              (Tactic.rwRule [] `Ideal.submodule_span_eq)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`a_mem `a_not_mem] []))])
           []
           (Std.Tactic.tacticRwa__
            "rwa"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `Ideal.count_normalized_factors_eq [`a_mem `a_not_mem]))
              ","
              (Tactic.rwRule [] (Term.app `min_eq_left [`i.le_succ]))]
             "]")
            [])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.intro "intro" [`ha])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `ideal.span_singleton_eq_bot.mp [`ha]))]
               "]")
              [(Tactic.location "at" (Tactic.locationHyp [`a_not_mem] []))])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.proj («term_^_» `P "^" («term_+_» `i "+" (num "1"))) "." `zero_mem))))
             []
             (Tactic.contradiction "contradiction")])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.rintro
           "rintro"
           [(Std.Tactic.RCases.rintroPat.one
             (Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.tuple
                        "⟨"
                        [(Std.Tactic.RCases.rcasesPatLo
                          (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x)])
                          [])]
                        "⟩")])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                     [])]
                   "⟩")])
                [])]
              "⟩"))]
           [])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Pe_le_Pi []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                "≤"
                («term_^_» `P "^" `i)))]
             ":="
             (Term.app `Ideal.pow_le_pow [`hi.le]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Pe_le_Pi1 []]
             [(Term.typeSpec
               ":"
               («term_≤_»
                («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
                "≤"
                («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
             ":="
             (Term.app `Ideal.pow_le_pow [`hi]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
             ","
             (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
             ","
             (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
             ","
             (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi]))]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
          []
          (Mathlib.Tactic.tacticSuffices_
           "suffices"
           [`hx' []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              `x
              "∈"
              (Order.Basic.«term_⊔_»
               (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
               " ⊔ "
               («term_^_» `P "^" («term_+_» `i "+" (num "1"))))))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy')])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `submodule.mem_sup.mp [`hx'])]])
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `ideal.mem_span_singleton.mp [`hy'])]])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Submodule.Quotient.mk [`y]) "," (Term.hole "_")]
              "⟩"))
            []
            (Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Submodule.Quotient.quot_mk_eq_mk)
               ","
               (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
               ","
               (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
               ","
               (Tactic.simpLemma [] [] `LinearMap.mem_range)
               ","
               (Tactic.simpLemma [] [] `Subtype.ext_iff)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_mk)
               ","
               (Tactic.simpLemma [] [] `Submodule.coe_sub)]
              "]"]
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.app
                  `Ideal.mem_map_of_mem
                  [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
                "⟩")
               ","
               (Term.hole "_")]
              "⟩"))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
               ","
               (Tactic.rwRule [] `Subtype.coe_mk)
               ","
               (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
               ","
               (Tactic.rwRule [] `map_add)
               ","
               (Tactic.rwRule [] (Term.app `mul_comm [`y `a]))
               ","
               (Tactic.rwRule [] `sub_add_cancel')
               ","
               (Tactic.rwRule [] `map_neg)]
              "]")
             [])])
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [(Term.app `Ideal [`S])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `sup_eq_prod_inf_factors
               [(Term.hole "_") (Term.app `pow_ne_zero [(Term.hole "_") `hP0])]))
             ","
             (Tactic.rwRule [] `normalized_factors_pow)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `normalized_factors_irreducible
               [(Term.proj
                 (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
                 "."
                 `Irreducible)]))
             ","
             (Tactic.rwRule [] `normalize_eq)
             ","
             (Tactic.rwRule [] `Multiset.nsmul_singleton)
             ","
             (Tactic.rwRule [] `Multiset.inter_repeat)
             ","
             (Tactic.rwRule [] `Multiset.prod_repeat)]
            "]")
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Submodule.span_singleton_le_iff_mem)
             ","
             (Tactic.rwRule [] `Ideal.submodule_span_eq)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`a_mem `a_not_mem] []))])
          []
          (Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `Ideal.count_normalized_factors_eq [`a_mem `a_not_mem]))
             ","
             (Tactic.rwRule [] (Term.app `min_eq_left [`i.le_succ]))]
            "]")
           [])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`ha])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `ideal.span_singleton_eq_bot.mp [`ha]))]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`a_not_mem] []))])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.proj («term_^_» `P "^" («term_+_» `i "+" (num "1"))) "." `zero_mem))))
            []
            (Tactic.contradiction "contradiction")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`ha])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `ideal.span_singleton_eq_bot.mp [`ha]))]
          "]")
         [(Tactic.location "at" (Tactic.locationHyp [`a_not_mem] []))])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.proj («term_^_» `P "^" («term_+_» `i "+" (num "1"))) "." `zero_mem))))
        []
        (Tactic.contradiction "contradiction")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.contradiction "contradiction")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.proj («term_^_» `P "^" («term_+_» `i "+" (num "1"))) "." `zero_mem))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj («term_^_» `P "^" («term_+_» `i "+" (num "1"))) "." `zero_mem)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `P "^" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `i "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» `P "^" (Term.paren "(" («term_+_» `i "+" (num "1")) ")"))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `ideal.span_singleton_eq_bot.mp [`ha]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`a_not_mem] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ideal.span_singleton_eq_bot.mp [`ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ideal.span_singleton_eq_bot.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`ha])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] (Term.app `Ideal.count_normalized_factors_eq [`a_mem `a_not_mem]))
         ","
         (Tactic.rwRule [] (Term.app `min_eq_left [`i.le_succ]))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `min_eq_left [`i.le_succ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i.le_succ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `min_eq_left
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.count_normalized_factors_eq [`a_mem `a_not_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.count_normalized_factors_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Submodule.span_singleton_le_iff_mem)
         ","
         (Tactic.rwRule [] `Ideal.submodule_span_eq)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`a_mem `a_not_mem] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.submodule_span_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.span_singleton_le_iff_mem
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `sup_eq_prod_inf_factors
           [(Term.hole "_") (Term.app `pow_ne_zero [(Term.hole "_") `hP0])]))
         ","
         (Tactic.rwRule [] `normalized_factors_pow)
         ","
         (Tactic.rwRule
          []
          (Term.app
           `normalized_factors_irreducible
           [(Term.proj
             (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
             "."
             `Irreducible)]))
         ","
         (Tactic.rwRule [] `normalize_eq)
         ","
         (Tactic.rwRule [] `Multiset.nsmul_singleton)
         ","
         (Tactic.rwRule [] `Multiset.inter_repeat)
         ","
         (Tactic.rwRule [] `Multiset.prod_repeat)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.prod_repeat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.inter_repeat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Multiset.nsmul_singleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `normalize_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `normalized_factors_irreducible
       [(Term.proj
         (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
         "."
         `Irreducible)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
       "."
       `Irreducible)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr) [`hP])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Ideal.prime_iff_is_prime [`hP0]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ideal.prime_iff_is_prime [`hP0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.prime_iff_is_prime
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.prime_iff_is_prime [`hP0])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `Ideal.prime_iff_is_prime [`hP0]) ")") "." `mpr)
      [`hP])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `normalized_factors_irreducible
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `normalized_factors_pow
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `sup_eq_prod_inf_factors
       [(Term.hole "_") (Term.app `pow_ne_zero [(Term.hole "_") `hP0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_ne_zero [(Term.hole "_") `hP0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_ne_zero [(Term.hole "_") `hP0])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sup_eq_prod_inf_factors
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl [] [] ":=" (Term.app `Classical.decEq [(Term.app `Ideal [`S])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.decEq [(Term.app `Ideal [`S])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal [`S])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `S
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Ideal [`S]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.decEq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy')])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `submodule.mem_sup.mp [`hx'])]])
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `ideal.mem_span_singleton.mp [`hy'])]])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor "⟨" [(Term.app `Submodule.Quotient.mk [`y]) "," (Term.hole "_")] "⟩"))
        []
        (Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `Submodule.Quotient.quot_mk_eq_mk)
           ","
           (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
           ","
           (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
           ","
           (Tactic.simpLemma [] [] `LinearMap.mem_range)
           ","
           (Tactic.simpLemma [] [] `Subtype.ext_iff)
           ","
           (Tactic.simpLemma [] [] `Subtype.coe_mk)
           ","
           (Tactic.simpLemma [] [] `Submodule.coe_sub)]
          "]"]
         [])
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor
            "⟨"
            [(Term.hole "_")
             ","
             (Term.app
              `Ideal.mem_map_of_mem
              [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
            "⟩")
           ","
           (Term.hole "_")]
          "⟩"))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
           ","
           (Tactic.rwRule [] `Subtype.coe_mk)
           ","
           (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
           ","
           (Tactic.rwRule [] `map_add)
           ","
           (Tactic.rwRule [] (Term.app `mul_comm [`y `a]))
           ","
           (Tactic.rwRule [] `sub_add_cancel')
           ","
           (Tactic.rwRule [] `map_neg)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_quot_succ_inclusion_apply_coe)
         ","
         (Tactic.rwRule [] `Subtype.coe_mk)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
         ","
         (Tactic.rwRule [] `map_add)
         ","
         (Tactic.rwRule [] (Term.app `mul_comm [`y `a]))
         ","
         (Tactic.rwRule [] `sub_add_cancel')
         ","
         (Tactic.rwRule [] `map_neg)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_neg
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `sub_add_cancel'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [`y `a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `map_add
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_quot_succ_inclusion_apply_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor
          "⟨"
          [(Term.hole "_")
           ","
           (Term.app
            `Ideal.mem_map_of_mem
            [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
          "⟩")
         ","
         (Term.hole "_")]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor
         "⟨"
         [(Term.hole "_")
          ","
          (Term.app
           `Ideal.mem_map_of_mem
           [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
         "⟩")
        ","
        (Term.hole "_")]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.hole "_")
        ","
        (Term.app
         `Ideal.mem_map_of_mem
         [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.mem_map_of_mem
       [(Term.hole "_") (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.neg_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Submodule.neg_mem [(Term.hole "_") `hz])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.mem_map_of_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Submodule.Quotient.quot_mk_eq_mk)
         ","
         (Tactic.simpLemma [] [] `quotient_to_quotient_range_pow_quot_succ_mk)
         ","
         (Tactic.simpLemma [] [] `Submodule.Quotient.eq)
         ","
         (Tactic.simpLemma [] [] `LinearMap.mem_range)
         ","
         (Tactic.simpLemma [] [] `Subtype.ext_iff)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_mk)
         ","
         (Tactic.simpLemma [] [] `Submodule.coe_sub)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.coe_sub
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.ext_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `LinearMap.mem_range
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `quotient_to_quotient_range_pow_quot_succ_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.quot_mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor "⟨" [(Term.app `Submodule.Quotient.mk [`y]) "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `Submodule.Quotient.mk [`y]) "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Submodule.Quotient.mk [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Submodule.Quotient.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `ideal.mem_span_singleton.mp [`hy'])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `ideal.mem_span_singleton.mp [`hy'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ideal.mem_span_singleton.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy')])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `submodule.mem_sup.mp [`hx'])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `submodule.mem_sup.mp [`hx'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `submodule.mem_sup.mp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSuffices_
       "suffices"
       [`hx' []]
       [(Term.typeSpec
         ":"
         («term_∈_»
          `x
          "∈"
          (Order.Basic.«term_⊔_»
           (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
           " ⊔ "
           («term_^_» `P "^" («term_+_» `i "+" (num "1"))))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       `x
       "∈"
       (Order.Basic.«term_⊔_»
        (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
        " ⊔ "
        («term_^_» `P "^" («term_+_» `i "+" (num "1")))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Order.Basic.«term_⊔_»
       (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
       " ⊔ "
       («term_^_» `P "^" («term_+_» `i "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `i "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 69 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 68, term))
      (Term.app `Ideal.span [(«term{_}» "{" [`a] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [`a] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.span
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 68 >? 1022, (some 1023, term) <=? (some 68, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 68, (some 69, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Submodule.Quotient.quot_mk_eq_mk)
         ","
         (Tactic.rwRule [] `Ideal.Quotient.mk_eq_mk)
         ","
         (Tactic.rwRule [] `Ideal.mem_quotient_iff_mem_sup)
         ","
         (Tactic.rwRule [] (Term.app `sup_eq_left.mpr [`Pe_le_Pi]))]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `sup_eq_left.mpr [`Pe_le_Pi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Pe_le_Pi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `sup_eq_left.mpr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.mem_quotient_iff_mem_sup
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.Quotient.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Submodule.Quotient.quot_mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`Pe_le_Pi1 []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
            "≤"
            («term_^_» `P "^" («term_+_» `i "+" (num "1")))))]
         ":="
         (Term.app `Ideal.pow_le_pow [`hi]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.pow_le_pow [`hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.pow_le_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_»
       («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
       "≤"
       («term_^_» `P "^" («term_+_» `i "+" (num "1"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `i "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  quotient_to_quotient_range_pow_quot_succ_surjective
  [ IsDomain S ]
      [ IsDedekindDomain S ]
      ( hP0 : P ≠ ⊥ )
      [ hP : P . IsPrime ]
      { i : ℕ }
      ( hi : i < e )
      { a : S }
      ( a_mem : a ∈ P ^ i )
      ( a_not_mem : a ∉ P ^ i + 1 )
    : Function.Surjective quotientToQuotientRangePowQuotSucc f p P a_mem
  :=
    by
      rintro ⟨ ⟨ ⟨ x ⟩ , hx ⟩ ⟩
        have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow hi.le
        have Pe_le_Pi1 : P ^ e ≤ P ^ i + 1 := Ideal.pow_le_pow hi
        rw
          [
            Submodule.Quotient.quot_mk_eq_mk
              ,
              Ideal.Quotient.mk_eq_mk
              ,
              Ideal.mem_quotient_iff_mem_sup
              ,
              sup_eq_left.mpr Pe_le_Pi
            ]
          at hx
        suffices hx' : x ∈ Ideal.span { a } ⊔ P ^ i + 1
        ·
          obtain ⟨ y' , hy' , z , hz , rfl ⟩ := submodule.mem_sup.mp hx'
            obtain ⟨ y , rfl ⟩ := ideal.mem_span_singleton.mp hy'
            refine' ⟨ Submodule.Quotient.mk y , _ ⟩
            simp
              only
              [
                Submodule.Quotient.quot_mk_eq_mk
                  ,
                  quotient_to_quotient_range_pow_quot_succ_mk
                  ,
                  Submodule.Quotient.eq
                  ,
                  LinearMap.mem_range
                  ,
                  Subtype.ext_iff
                  ,
                  Subtype.coe_mk
                  ,
                  Submodule.coe_sub
                ]
            refine' ⟨ ⟨ _ , Ideal.mem_map_of_mem _ Submodule.neg_mem _ hz ⟩ , _ ⟩
            rw
              [
                pow_quot_succ_inclusion_apply_coe
                  ,
                  Subtype.coe_mk
                  ,
                  Ideal.Quotient.mk_eq_mk
                  ,
                  map_add
                  ,
                  mul_comm y a
                  ,
                  sub_add_cancel'
                  ,
                  map_neg
                ]
        letI := Classical.decEq Ideal S
        rw
          [
            sup_eq_prod_inf_factors _ pow_ne_zero _ hP0
              ,
              normalized_factors_pow
              ,
              normalized_factors_irreducible Ideal.prime_iff_is_prime hP0 . mpr hP . Irreducible
              ,
              normalize_eq
              ,
              Multiset.nsmul_singleton
              ,
              Multiset.inter_repeat
              ,
              Multiset.prod_repeat
            ]
        rw [ ← Submodule.span_singleton_le_iff_mem , Ideal.submodule_span_eq ] at a_mem a_not_mem
        rwa [ Ideal.count_normalized_factors_eq a_mem a_not_mem , min_eq_left i.le_succ ]
        ·
          intro ha
            rw [ ideal.span_singleton_eq_bot.mp ha ] at a_not_mem
            have := P ^ i + 1 . zero_mem
            contradiction
#align
  ideal.quotient_to_quotient_range_pow_quot_succ_surjective Ideal.quotient_to_quotient_range_pow_quot_succ_surjective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is\n`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `quotientRangePowQuotSuccInclusionEquiv [])
      (Command.optDeclSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.explicitBinder
         "("
         [`hP]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`hi]
         [":" («term_<_» `i "<" (Ideal.NumberTheory.RamificationInertia.terme "e"))]
         []
         ")")]
       [(Term.typeSpec
         ":"
         (Algebra.Module.Equiv.«term_≃ₗ[_]_»
          (Algebra.Quotient.«term_⧸_»
           (Term.app
            (Term.proj («term_^_» `P "^" `i) "." `map)
            [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
           " ⧸ "
           (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))
          " ≃ₗ["
          (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
          "] "
          (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Mathlib.Tactic.Choose.choose
            "choose"
            []
            [(Lean.binderIdent `a) (Lean.binderIdent `a_mem) (Lean.binderIdent `a_not_mem)]
            ["using"
             (Term.app
              `SetLike.exists_of_lt
              [(Term.app
                `Ideal.strict_anti_pow
                [`P
                 `hP
                 (Term.app `Ideal.IsPrime.ne_top [`inferInstance])
                 (Term.app `le_refl [`i.succ])])])])
           []
           (Tactic.refine'
            "refine'"
            (Term.proj
             (Term.app
              `LinearEquiv.ofBijective
              [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
             "."
             `symm))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app `quotient_to_quotient_range_pow_quot_succ [`f `p `P `a_mem]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               `quotient_to_quotient_range_pow_quot_succ_injective
               [`f `p `P `hi `a_mem `a_not_mem]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.exact
              "exact"
              (Term.app
               `quotient_to_quotient_range_pow_quot_succ_surjective
               [`f `p `P `hP `hi `a_mem `a_not_mem]))])])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Mathlib.Tactic.Choose.choose
           "choose"
           []
           [(Lean.binderIdent `a) (Lean.binderIdent `a_mem) (Lean.binderIdent `a_not_mem)]
           ["using"
            (Term.app
             `SetLike.exists_of_lt
             [(Term.app
               `Ideal.strict_anti_pow
               [`P
                `hP
                (Term.app `Ideal.IsPrime.ne_top [`inferInstance])
                (Term.app `le_refl [`i.succ])])])])
          []
          (Tactic.refine'
           "refine'"
           (Term.proj
            (Term.app
             `LinearEquiv.ofBijective
             [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
            "."
            `symm))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app `quotient_to_quotient_range_pow_quot_succ [`f `p `P `a_mem]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `quotient_to_quotient_range_pow_quot_succ_injective
              [`f `p `P `hi `a_mem `a_not_mem]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.exact
             "exact"
             (Term.app
              `quotient_to_quotient_range_pow_quot_succ_surjective
              [`f `p `P `hP `hi `a_mem `a_not_mem]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `quotient_to_quotient_range_pow_quot_succ_surjective
          [`f `p `P `hP `hi `a_mem `a_not_mem]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `quotient_to_quotient_range_pow_quot_succ_surjective
        [`f `p `P `hP `hi `a_mem `a_not_mem]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `quotient_to_quotient_range_pow_quot_succ_surjective
       [`f `p `P `hP `hi `a_mem `a_not_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotient_to_quotient_range_pow_quot_succ_surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app
          `quotient_to_quotient_range_pow_quot_succ_injective
          [`f `p `P `hi `a_mem `a_not_mem]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `quotient_to_quotient_range_pow_quot_succ_injective
        [`f `p `P `hi `a_mem `a_not_mem]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `quotient_to_quotient_range_pow_quot_succ_injective
       [`f `p `P `hi `a_mem `a_not_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_not_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotient_to_quotient_range_pow_quot_succ_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact
         "exact"
         (Term.app `quotient_to_quotient_range_pow_quot_succ [`f `p `P `a_mem]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `quotient_to_quotient_range_pow_quot_succ [`f `p `P `a_mem]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `quotient_to_quotient_range_pow_quot_succ [`f `p `P `a_mem])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a_mem
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotient_to_quotient_range_pow_quot_succ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.proj
        (Term.app
         `LinearEquiv.ofBijective
         [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `LinearEquiv.ofBijective
        [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `LinearEquiv.ofBijective
       [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearEquiv.ofBijective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `LinearEquiv.ofBijective
      [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," (Term.hole "_")] "⟩")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.Choose.choose
       "choose"
       []
       [(Lean.binderIdent `a) (Lean.binderIdent `a_mem) (Lean.binderIdent `a_not_mem)]
       ["using"
        (Term.app
         `SetLike.exists_of_lt
         [(Term.app
           `Ideal.strict_anti_pow
           [`P
            `hP
            (Term.app `Ideal.IsPrime.ne_top [`inferInstance])
            (Term.app `le_refl [`i.succ])])])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `SetLike.exists_of_lt
       [(Term.app
         `Ideal.strict_anti_pow
         [`P `hP (Term.app `Ideal.IsPrime.ne_top [`inferInstance]) (Term.app `le_refl [`i.succ])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.strict_anti_pow
       [`P `hP (Term.app `Ideal.IsPrime.ne_top [`inferInstance]) (Term.app `le_refl [`i.succ])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `le_refl [`i.succ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i.succ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `le_refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `le_refl [`i.succ]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Ideal.IsPrime.ne_top [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.IsPrime.ne_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Ideal.IsPrime.ne_top [`inferInstance])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.strict_anti_pow
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `Ideal.strict_anti_pow
      [`P
       `hP
       (Term.paren "(" (Term.app `Ideal.IsPrime.ne_top [`inferInstance]) ")")
       (Term.paren "(" (Term.app `le_refl [`i.succ]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `SetLike.exists_of_lt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Algebra.Module.Equiv.«term_≃ₗ[_]_»
       (Algebra.Quotient.«term_⧸_»
        (Term.app
         (Term.proj («term_^_» `P "^" `i) "." `map)
         [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
        " ⧸ "
        (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))
       " ≃ₗ["
       (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
       "] "
       (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Algebra.Quotient.«term_⧸_»
       (Term.app
        (Term.proj («term_^_» `P "^" `i) "." `map)
        [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
       " ⧸ "
       (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `powQuotSuccInclusion [`f `p `P `i]) "." `range)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `powQuotSuccInclusion [`f `p `P `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `powQuotSuccInclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `powQuotSuccInclusion [`f `p `P `i])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      (Term.app
       (Term.proj («term_^_» `P "^" `i) "." `map)
       [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
      `R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
    noncomputable
  def
    quotientRangePowQuotSuccInclusionEquiv
    [ IsDomain S ] [ IsDedekindDomain S ] [ P . IsPrime ] ( hP : P ≠ ⊥ ) { i : ℕ } ( hi : i < e )
      : P ^ i . map P ^ e ⧸ powQuotSuccInclusion f p P i . range ≃ₗ[ R ⧸ p ] S ⧸ P
    :=
      by
        choose
            a a_mem a_not_mem
            using
              SetLike.exists_of_lt
                Ideal.strict_anti_pow P hP Ideal.IsPrime.ne_top inferInstance le_refl i.succ
          refine' LinearEquiv.ofBijective _ ⟨ _ , _ ⟩ . symm
          · exact quotient_to_quotient_range_pow_quot_succ f p P a_mem
          · exact quotient_to_quotient_range_pow_quot_succ_injective f p P hi a_mem a_not_mem
          · exact quotient_to_quotient_range_pow_quot_succ_surjective f p P hP hi a_mem a_not_mem
#align
  ideal.quotient_range_pow_quot_succ_inclusion_equiv Ideal.quotientRangePowQuotSuccInclusionEquiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,\n`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `dim_pow_quot_aux [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.proj `p "." `IsMaximal) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.explicitBinder
         "("
         [`hP0]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.implicitBinder "{" [`i] [":" (termℕ "ℕ")] "}")
        (Term.explicitBinder
         "("
         [`hi]
         [":" («term_<_» `i "<" (Ideal.NumberTheory.RamificationInertia.terme "e"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `Module.rank
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Term.app
            `Ideal.map
            [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
             («term_^_» `P "^" `i)])])
         "="
         («term_+_»
          (Term.app
           `Module.rank
           [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])
          "+"
          (Term.app
           `Module.rank
           [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
            (Term.app
             `Ideal.map
             [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
              («term_^_» `P "^" («term_+_» `i "+" (num "1")))])])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec ":" (Term.app `Field [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)]))]
              ":="
              (Term.app `Ideal.Quotient.field [(Term.hole "_")]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `dim_eq_of_injective
                [(Term.hole "_") (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])]))
              ","
              (Tactic.rwRule
               []
               (Term.proj
                (Term.proj
                 (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
                 "."
                 `symm)
                "."
                `dim_eq))]
             "]")
            [])
           []
           (Tactic.exact
            "exact"
            (Term.proj
             (Term.app
              `dim_quotient_add_dim
              [(Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])])
             "."
             `symm))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec ":" (Term.app `Field [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)]))]
             ":="
             (Term.app `Ideal.Quotient.field [(Term.hole "_")]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `dim_eq_of_injective
               [(Term.hole "_") (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])]))
             ","
             (Tactic.rwRule
              []
              (Term.proj
               (Term.proj
                (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
                "."
                `symm)
               "."
               `dim_eq))]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.proj
            (Term.app
             `dim_quotient_add_dim
             [(Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])])
            "."
            `symm))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.proj
        (Term.app
         `dim_quotient_add_dim
         [(Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])])
        "."
        `symm))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        `dim_quotient_add_dim
        [(Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       `dim_quotient_add_dim
       [(Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearMap.range [(Term.app `pow_quot_succ_inclusion [`f `p `P `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_quot_succ_inclusion [`f `p `P `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_quot_succ_inclusion
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_quot_succ_inclusion [`f `p `P `i])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearMap.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `LinearMap.range
      [(Term.paren "(" (Term.app `pow_quot_succ_inclusion [`f `p `P `i]) ")")])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dim_quotient_add_dim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `dim_quotient_add_dim
      [(Term.paren
        "("
        (Term.app
         `LinearMap.range
         [(Term.paren "(" (Term.app `pow_quot_succ_inclusion [`f `p `P `i]) ")")])
        ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          []
          (Term.app
           `dim_eq_of_injective
           [(Term.hole "_") (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])]))
         ","
         (Tactic.rwRule
          []
          (Term.proj
           (Term.proj
            (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
            "."
            `symm)
           "."
           `dim_eq))]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.proj
        (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
        "."
        `symm)
       "."
       `dim_eq)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hi
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hP0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotient_range_pow_quot_succ_inclusion_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `quotient_range_pow_quot_succ_inclusion_equiv [`f `p `P `hP0 `hi])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dim_eq_of_injective
       [(Term.hole "_") (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `i
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `pow_quot_succ_inclusion_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `pow_quot_succ_inclusion_injective [`f `p `P `i])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dim_eq_of_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Term.app `Field [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)]))]
         ":="
         (Term.app `Ideal.Quotient.field [(Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.Quotient.field [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.field
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Field [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Field
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `Module.rank
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
         (Term.app
          `Ideal.map
          [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
           («term_^_» `P "^" `i)])])
       "="
       («term_+_»
        (Term.app
         `Module.rank
         [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])
        "+"
        (Term.app
         `Module.rank
         [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
          (Term.app
           `Ideal.map
           [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
            («term_^_» `P "^" («term_+_» `i "+" (num "1")))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_»
       (Term.app
        `Module.rank
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])
       "+"
       (Term.app
        `Module.rank
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
         (Term.app
          `Ideal.map
          [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
           («term_^_» `P "^" («term_+_» `i "+" (num "1")))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Module.rank
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
        (Term.app
         `Ideal.map
         [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
          («term_^_» `P "^" («term_+_» `i "+" (num "1")))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Ideal.map
       [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
        («term_^_» `P "^" («term_+_» `i "+" (num "1")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" («term_+_» `i "+" (num "1")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_+_» `i "+" (num "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "1")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      `i
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" («term_+_» `i "+" (num "1")) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `P
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_^_» `P "^" (Term.paren "(" («term_+_» `i "+" (num "1")) ")"))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
    `[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
  theorem
    dim_pow_quot_aux
    [ IsDomain S ]
        [ IsDedekindDomain S ]
        [ p . IsMaximal ]
        [ P . IsPrime ]
        ( hP0 : P ≠ ⊥ )
        { i : ℕ }
        ( hi : i < e )
      :
        Module.rank R ⧸ p Ideal.map P ^ e P ^ i
          =
          Module.rank R ⧸ p S ⧸ P + Module.rank R ⧸ p Ideal.map P ^ e P ^ i + 1
    :=
      by
        letI : Field R ⧸ p := Ideal.Quotient.field _
          rw
            [
              dim_eq_of_injective _ pow_quot_succ_inclusion_injective f p P i
                ,
                quotient_range_pow_quot_succ_inclusion_equiv f p P hP0 hi . symm . dim_eq
              ]
          exact dim_quotient_add_dim LinearMap.range pow_quot_succ_inclusion f p P i . symm
#align ideal.dim_pow_quot_aux Ideal.dim_pow_quot_aux

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `dim_pow_quot [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.proj `p "." `IsMaximal) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.explicitBinder
         "("
         [`hP0]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.explicitBinder "(" [`i] [":" (termℕ "ℕ")] [] ")")
        (Term.explicitBinder
         "("
         [`hi]
         [":" («term_≤_» `i "≤" (Ideal.NumberTheory.RamificationInertia.terme "e"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `Module.rank
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Term.app
            `Ideal.map
            [(«term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
             («term_^_» `P "^" `i)])])
         "="
         (Algebra.Group.Defs.«term_•_»
          («term_-_» (Ideal.NumberTheory.RamificationInertia.terme "e") "-" `i)
          " • "
          (Term.app
           `Module.rank
           [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.explicit "@" `Nat.decreasingInduction')
             [(Term.hole "_")
              `i
              (Ideal.NumberTheory.RamificationInertia.terme "e")
              (Term.fun "fun" (Term.basicFun [`j `lt_e `le_j `ih] [] "=>" (Term.hole "_")))
              `hi
              (Term.hole "_")]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] (Term.app `dim_pow_quot_aux [`f `p `P (Term.hole "_") `lt_e]))
                ","
                (Tactic.rwRule [] `ih)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_nsmul)
                ","
                (Tactic.rwRule [] `Nat.sub_succ)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.succ_eq_add_one)
                ","
                (Tactic.rwRule
                 []
                 (Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`lt_e])]))]
               "]")
              [])
             []
             (Tactic.assumption "assumption")])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Nat.sub_self)
                ","
                (Tactic.rwRule [] `zero_nsmul)
                ","
                (Tactic.rwRule [] `map_quotient_self)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `dim_bot
               [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
                (Algebra.Quotient.«term_⧸_»
                 `S
                 " ⧸ "
                 («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))]))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.explicit "@" `Nat.decreasingInduction')
            [(Term.hole "_")
             `i
             (Ideal.NumberTheory.RamificationInertia.terme "e")
             (Term.fun "fun" (Term.basicFun [`j `lt_e `le_j `ih] [] "=>" (Term.hole "_")))
             `hi
             (Term.hole "_")]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `dim_pow_quot_aux [`f `p `P (Term.hole "_") `lt_e]))
               ","
               (Tactic.rwRule [] `ih)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `succ_nsmul)
               ","
               (Tactic.rwRule [] `Nat.sub_succ)
               ","
               (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `Nat.succ_eq_add_one)
               ","
               (Tactic.rwRule
                []
                (Term.app `Nat.succ_pred_eq_of_pos [(Term.app `Nat.sub_pos_of_lt [`lt_e])]))]
              "]")
             [])
            []
            (Tactic.assumption "assumption")])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Nat.sub_self)
               ","
               (Tactic.rwRule [] `zero_nsmul)
               ","
               (Tactic.rwRule [] `map_quotient_self)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `dim_bot
              [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
               (Algebra.Quotient.«term_⧸_»
                `S
                " ⧸ "
                («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `Nat.sub_self)
           ","
           (Tactic.rwRule [] `zero_nsmul)
           ","
           (Tactic.rwRule [] `map_quotient_self)]
          "]")
         [])
        []
        (Tactic.exact
         "exact"
         (Term.app
          `dim_bot
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Algebra.Quotient.«term_⧸_»
            `S
            " ⧸ "
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `dim_bot
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
         (Algebra.Quotient.«term_⧸_»
          `S
          " ⧸ "
          («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dim_bot
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
        (Algebra.Quotient.«term_⧸_»
         `S
         " ⧸ "
         («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_»
       `S
       " ⧸ "
       («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  dim_pow_quot
  [ IsDomain S ]
      [ IsDedekindDomain S ]
      [ p . IsMaximal ]
      [ P . IsPrime ]
      ( hP0 : P ≠ ⊥ )
      ( i : ℕ )
      ( hi : i ≤ e )
    : Module.rank R ⧸ p Ideal.map P ^ e P ^ i = e - i • Module.rank R ⧸ p S ⧸ P
  :=
    by
      refine' @ Nat.decreasingInduction' _ i e fun j lt_e le_j ih => _ hi _
        ·
          rw
              [
                dim_pow_quot_aux f p P _ lt_e
                  ,
                  ih
                  ,
                  ← succ_nsmul
                  ,
                  Nat.sub_succ
                  ,
                  ← Nat.succ_eq_add_one
                  ,
                  Nat.succ_pred_eq_of_pos Nat.sub_pos_of_lt lt_e
                ]
            assumption
        · rw [ Nat.sub_self , zero_nsmul , map_quotient_self ] exact dim_bot R ⧸ p S ⧸ P ^ e
#align ideal.dim_pow_quot Ideal.dim_pow_quot

omit hfp

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,\nthen the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `dim_prime_pow_ramification_idx [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.proj `p "." `IsMaximal) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.explicitBinder
         "("
         [`hP0]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.explicitBinder
         "("
         [`he]
         [":" («term_≠_» (Ideal.NumberTheory.RamificationInertia.terme "e") "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `Module.rank
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Algebra.Quotient.«term_⧸_»
            `S
            " ⧸ "
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))])
         "="
         (Algebra.Group.Defs.«term_•_»
          (Ideal.NumberTheory.RamificationInertia.terme "e")
          " • "
          (Term.app
           (Term.explicit "@" `Module.rank)
           [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
            (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
            (Term.hole "_")
            (Term.hole "_")
            («term_<|_»
             (Term.app
              (Term.explicit "@" `Algebra.toModule)
              [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "<|"
             (Term.app
              (Term.explicit "@" `Quotient.algebraQuotientOfRamificationIdxNeZero)
              [(Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.anonymousCtor "⟨" [`he] "⟩")]))])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")]))]
              ":="
              (Term.anonymousCtor "⟨" [`he] "⟩"))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              []
              ":="
              (Term.app
               `dim_pow_quot
               [`f
                `p
                `P
                `hP0
                (num "0")
                (Term.app `Nat.zero_le [(Ideal.NumberTheory.RamificationInertia.terme "e")])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `pow_zero)
              ","
              (Tactic.rwRule [] `Nat.sub_zero)
              ","
              (Tactic.rwRule [] `Ideal.one_eq_top)
              ","
              (Tactic.rwRule [] `Ideal.map_top)]
             "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           []
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj
              (Term.proj
               (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
               "."
               `symm)
              "."
              `trans)
             [`this]))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")]))]
             ":="
             (Term.anonymousCtor "⟨" [`he] "⟩"))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             []
             ":="
             (Term.app
              `dim_pow_quot
              [`f
               `p
               `P
               `hP0
               (num "0")
               (Term.app `Nat.zero_le [(Ideal.NumberTheory.RamificationInertia.terme "e")])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `pow_zero)
             ","
             (Tactic.rwRule [] `Nat.sub_zero)
             ","
             (Tactic.rwRule [] `Ideal.one_eq_top)
             ","
             (Tactic.rwRule [] `Ideal.map_top)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
              "."
              `symm)
             "."
             `trans)
            [`this]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         (Term.proj
          (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
          "."
          `symm)
         "."
         `trans)
        [`this]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.proj
         (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
         "."
         `symm)
        "."
        `trans)
       [`this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.proj
        (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
        "."
        `symm)
       "."
       `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj
       (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
       "."
       `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `dim_top [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dim_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `dim_top
      [(Term.paren "(" (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) ")") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `pow_zero)
         ","
         (Tactic.rwRule [] `Nat.sub_zero)
         ","
         (Tactic.rwRule [] `Ideal.one_eq_top)
         ","
         (Tactic.rwRule [] `Ideal.map_top)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.map_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Ideal.one_eq_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.sub_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pow_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          `dim_pow_quot
          [`f
           `p
           `P
           `hP0
           (num "0")
           (Term.app `Nat.zero_le [(Ideal.NumberTheory.RamificationInertia.terme "e")])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dim_pow_quot
       [`f
        `p
        `P
        `hP0
        (num "0")
        (Term.app `Nat.zero_le [(Ideal.NumberTheory.RamificationInertia.terme "e")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nat.zero_le [(Ideal.NumberTheory.RamificationInertia.terme "e")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
    then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
  theorem
    dim_prime_pow_ramification_idx
    [ IsDomain S ]
        [ IsDedekindDomain S ]
        [ p . IsMaximal ]
        [ P . IsPrime ]
        ( hP0 : P ≠ ⊥ )
        ( he : e ≠ 0 )
      :
        Module.rank R ⧸ p S ⧸ P ^ e
          =
          e
            •
            @ Module.rank
              R ⧸ p
                S ⧸ P
                _
                _
                @ Algebra.toModule _ _ _ _
                  <|
                  @ Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ ⟨ he ⟩
    :=
      by
        letI : NeZero e := ⟨ he ⟩
          have := dim_pow_quot f p P hP0 0 Nat.zero_le e
          rw [ pow_zero , Nat.sub_zero , Ideal.one_eq_top , Ideal.map_top ] at this
          exact dim_top R ⧸ p _ . symm . trans this
#align ideal.dim_prime_pow_ramification_idx Ideal.dim_prime_pow_ramification_idx

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,\nthen the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `finrank_prime_pow_ramification_idx [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `IsDomain [`S]) "]")
        (Term.instBinder "[" [] (Term.app `IsDedekindDomain [`S]) "]")
        (Term.explicitBinder
         "("
         [`hP0]
         [":" («term_≠_» `P "≠" (Order.BoundedOrder.«term⊥» "⊥"))]
         []
         ")")
        (Term.instBinder "[" [] (Term.proj `p "." `IsMaximal) "]")
        (Term.instBinder "[" [] (Term.proj `P "." `IsPrime) "]")
        (Term.explicitBinder
         "("
         [`he]
         [":" («term_≠_» (Ideal.NumberTheory.RamificationInertia.terme "e") "≠" (num "0"))]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `finrank
          [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
           (Algebra.Quotient.«term_⧸_»
            `S
            " ⧸ "
            («term_^_» `P "^" (Ideal.NumberTheory.RamificationInertia.terme "e")))])
         "="
         («term_*_»
          (Ideal.NumberTheory.RamificationInertia.terme "e")
          "*"
          (Term.app
           (Term.explicit "@" `finrank)
           [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
            (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
            (Term.hole "_")
            (Term.hole "_")
            («term_<|_»
             (Term.app
              (Term.explicit "@" `Algebra.toModule)
              [(Term.hole "_") (Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "<|"
             (Term.app
              (Term.explicit "@" `Quotient.algebraQuotientOfRamificationIdxNeZero)
              [(Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.hole "_")
               (Term.anonymousCtor "⟨" [`he] "⟩")]))])))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")]))]
              ":="
              (Term.anonymousCtor "⟨" [`he] "⟩"))))
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                (Term.app
                 `Algebra
                 [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
                  (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))]
              ":="
              (Term.app `quotient.algebra_quotient_of_ramification_idx_ne_zero [`f `p `P]))))
           []
           (Std.Tactic.tacticLetI_
            "letI"
            (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Ideal.Quotient.field [`p]))))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hdim []]
              []
              ":="
              (Term.app
               `dim_prime_pow_ramification_idx
               [(Term.hole "_") (Term.hole "_") (Term.hole "_") `hP0 `he]))))
           []
           (Classical.«tacticBy_cases_:_»
            "by_cases"
            [`hP ":"]
            (Term.app
             `FiniteDimensional
             [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hP)))
             []
             (Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                []
                ":="
                (Term.app
                 (Term.proj
                  (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim])
                  "."
                  `mpr)
                 [`hP]))))
             []
             (Tactic.refine' "refine'" (Term.app `Cardinal.nat_cast_injective [(Term.hole "_")]))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `finrank_eq_dim)
                ","
                (Tactic.rwRule [] `Nat.cast_mul)
                ","
                (Tactic.rwRule [] `finrank_eq_dim)
                ","
                (Tactic.rwRule [] `hdim)
                ","
                (Tactic.rwRule [] `nsmul_eq_mul)]
               "]")
              [])])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hPe []]
              []
              ":="
              (Term.app
               `mt
               [(Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mp)
                `hP]))))
           []
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hP]))
              ","
              (Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hPe]))
              ","
              (Tactic.simpLemma [] [] `mul_zero)]
             "]"]
            [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")]))]
             ":="
             (Term.anonymousCtor "⟨" [`he] "⟩"))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               (Term.app
                `Algebra
                [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
                 (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))]
             ":="
             (Term.app `quotient.algebra_quotient_of_ramification_idx_ne_zero [`f `p `P]))))
          []
          (Std.Tactic.tacticLetI_
           "letI"
           (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Ideal.Quotient.field [`p]))))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hdim []]
             []
             ":="
             (Term.app
              `dim_prime_pow_ramification_idx
              [(Term.hole "_") (Term.hole "_") (Term.hole "_") `hP0 `he]))))
          []
          (Classical.«tacticBy_cases_:_»
           "by_cases"
           [`hP ":"]
           (Term.app
            `FiniteDimensional
            [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hP)))
            []
            (Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               []
               ":="
               (Term.app
                (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mpr)
                [`hP]))))
            []
            (Tactic.refine' "refine'" (Term.app `Cardinal.nat_cast_injective [(Term.hole "_")]))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `finrank_eq_dim)
               ","
               (Tactic.rwRule [] `Nat.cast_mul)
               ","
               (Tactic.rwRule [] `finrank_eq_dim)
               ","
               (Tactic.rwRule [] `hdim)
               ","
               (Tactic.rwRule [] `nsmul_eq_mul)]
              "]")
             [])])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hPe []]
             []
             ":="
             (Term.app
              `mt
              [(Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mp)
               `hP]))))
          []
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hP]))
             ","
             (Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hPe]))
             ","
             (Tactic.simpLemma [] [] `mul_zero)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hP]))
         ","
         (Tactic.simpLemma [] [] (Term.app `finrank_of_infinite_dimensional [`hPe]))
         ","
         (Tactic.simpLemma [] [] `mul_zero)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `finrank_of_infinite_dimensional [`hPe])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hPe
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finrank_of_infinite_dimensional
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `finrank_of_infinite_dimensional [`hP])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finrank_of_infinite_dimensional
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hPe []]
         []
         ":="
         (Term.app
          `mt
          [(Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mp)
           `hP]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `mt
       [(Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mp) `hP])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hdim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `he
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finite_dimensional_iff_of_rank_eq_nsmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mt
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hP)))
        []
        (Std.Tactic.tacticHaveI_
         "haveI"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app
            (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mpr)
            [`hP]))))
        []
        (Tactic.refine' "refine'" (Term.app `Cardinal.nat_cast_injective [(Term.hole "_")]))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `finrank_eq_dim)
           ","
           (Tactic.rwRule [] `Nat.cast_mul)
           ","
           (Tactic.rwRule [] `finrank_eq_dim)
           ","
           (Tactic.rwRule [] `hdim)
           ","
           (Tactic.rwRule [] `nsmul_eq_mul)]
          "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `finrank_eq_dim)
         ","
         (Tactic.rwRule [] `Nat.cast_mul)
         ","
         (Tactic.rwRule [] `finrank_eq_dim)
         ","
         (Tactic.rwRule [] `hdim)
         ","
         (Tactic.rwRule [] `nsmul_eq_mul)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `nsmul_eq_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hdim
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `finrank_eq_dim
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nat.cast_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `finrank_eq_dim
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `Cardinal.nat_cast_injective [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Cardinal.nat_cast_injective [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Cardinal.nat_cast_injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         []
         ":="
         (Term.app
          (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mpr)
          [`hP]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mpr)
       [`hP])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hdim
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `he
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `finite_dimensional_iff_of_rank_eq_nsmul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `finite_dimensional_iff_of_rank_eq_nsmul [`he `hdim])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_ "haveI" (Term.haveDecl (Term.haveIdDecl [] [] ":=" `hP)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hP
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Classical.«tacticBy_cases_:_»
       "by_cases"
       [`hP ":"]
       (Term.app
        `FiniteDimensional
        [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `FiniteDimensional
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `FiniteDimensional
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hdim []]
         []
         ":="
         (Term.app
          `dim_prime_pow_ramification_idx
          [(Term.hole "_") (Term.hole "_") (Term.hole "_") `hP0 `he]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `dim_prime_pow_ramification_idx
       [(Term.hole "_") (Term.hole "_") (Term.hole "_") `hP0 `he])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `he
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hP0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dim_prime_pow_ramification_idx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `Ideal.Quotient.field [`p]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Ideal.Quotient.field [`p])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Ideal.Quotient.field
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app
            `Algebra
            [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)]))]
         ":="
         (Term.app `quotient.algebra_quotient_of_ramification_idx_ne_zero [`f `p `P]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `quotient.algebra_quotient_of_ramification_idx_ne_zero [`f `p `P])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `p
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `quotient.algebra_quotient_of_ramification_idx_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Algebra
       [(Algebra.Quotient.«term_⧸_» `R " ⧸ " `p) (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `P
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `S
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `S " ⧸ " `P)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Quotient.«term_⧸_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `p
[PrettyPrinter.parenthesize] ...precedences are 34 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 35, (some 34, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Algebra.Quotient.«term_⧸_» `R " ⧸ " `p)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Algebra
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticLetI_
       "letI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")]))]
         ":="
         (Term.anonymousCtor "⟨" [`he] "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`he] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `he
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `NeZero [(Ideal.NumberTheory.RamificationInertia.terme "e")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Ideal.NumberTheory.RamificationInertia.terme "e")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Ideal.NumberTheory.RamificationInertia.terme', expected 'Ideal.NumberTheory.RamificationInertia.terme._@.NumberTheory.RamificationInertia._hyg.15'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
    then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
  theorem
    finrank_prime_pow_ramification_idx
    [ IsDomain S ]
        [ IsDedekindDomain S ]
        ( hP0 : P ≠ ⊥ )
        [ p . IsMaximal ]
        [ P . IsPrime ]
        ( he : e ≠ 0 )
      :
        finrank R ⧸ p S ⧸ P ^ e
          =
          e
            *
            @ finrank
              R ⧸ p
                S ⧸ P
                _
                _
                @ Algebra.toModule _ _ _ _
                  <|
                  @ Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ ⟨ he ⟩
    :=
      by
        letI : NeZero e := ⟨ he ⟩
          letI : Algebra R ⧸ p S ⧸ P := quotient.algebra_quotient_of_ramification_idx_ne_zero f p P
          letI := Ideal.Quotient.field p
          have hdim := dim_prime_pow_ramification_idx _ _ _ hP0 he
          by_cases hP : FiniteDimensional R ⧸ p S ⧸ P
          ·
            haveI := hP
              haveI := finite_dimensional_iff_of_rank_eq_nsmul he hdim . mpr hP
              refine' Cardinal.nat_cast_injective _
              rw [ finrank_eq_dim , Nat.cast_mul , finrank_eq_dim , hdim , nsmul_eq_mul ]
          have hPe := mt finite_dimensional_iff_of_rank_eq_nsmul he hdim . mp hP
          simp
            only
            [ finrank_of_infinite_dimensional hP , finrank_of_infinite_dimensional hPe , mul_zero ]
#align ideal.finrank_prime_pow_ramification_idx Ideal.finrank_prime_pow_ramification_idx

end FactLeComap

section FactorsMap

open Classical

/-! ## Properties of the factors of `p.map (algebra_map R S)` -/


variable [IsDomain S] [IsDedekindDomain S] [Algebra R S]

theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_to_finset.mp P.2)).NeZero
#align ideal.factors.ne_bot Ideal.Factors.ne_bot

instance Factors.isPrime (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsPrime (P : Ideal S) :=
  Ideal.isPrimeOfPrime (prime_of_factor _ (Multiset.mem_to_finset.mp P.2))
#align ideal.factors.is_prime Ideal.Factors.isPrime

theorem Factors.ramification_idx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx (algebraMap R S) p P ≠ 0 :=
  IsDedekindDomain.ramification_idx_ne_zero (ne_zero_of_mem_factors (Multiset.mem_to_finset.mp P.2))
    (Factors.isPrime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_to_finset.mp P.2)))
#align ideal.factors.ramification_idx_ne_zero Ideal.Factors.ramification_idx_ne_zero

instance Factors.fact_ramification_idx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    NeZero (ramificationIdx (algebraMap R S) p P) :=
  ⟨Factors.ramification_idx_ne_zero p P⟩
#align ideal.factors.fact_ramification_idx_ne_zero Ideal.Factors.fact_ramification_idx_ne_zero

attribute [local instance] quotient.algebra_quotient_of_ramification_idx_ne_zero

instance Factors.is_scalar_tower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebra_map_eq fun x => by simp
#align ideal.factors.is_scalar_tower Ideal.Factors.is_scalar_tower

attribute [local instance] Ideal.Quotient.field

theorem Factors.finrank_pow_ramification_idx [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) =
      ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P :=
  by
  rw [finrank_prime_pow_ramification_idx, inertia_deg_algebra_map]
  exact factors.ne_bot p P
#align ideal.factors.finrank_pow_ramification_idx Ideal.Factors.finrank_pow_ramification_idx

instance Factors.finite_dimensional_quotient [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsNoetherian.iff_fg.mp <|
    isNoetherianOfTower R <|
      isNoetherianOfSurjective S (Ideal.Quotient.mkₐ _ _).toLinearMap <|
        LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective
#align ideal.factors.finite_dimensional_quotient Ideal.Factors.finite_dimensional_quotient

theorem Factors.inertia_deg_ne_zero [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) : inertiaDeg (algebraMap R S) p P ≠ 0 :=
  by
  rw [inertia_deg_algebra_map]
  exact (finite_dimensional.finrank_pos_iff.mpr inferInstance).ne'
#align ideal.factors.inertia_deg_ne_zero Ideal.Factors.inertia_deg_ne_zero

instance Factors.finite_dimensional_quotient_pow [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) :=
  by
  refine' FiniteDimensional.finite_dimensional_of_finrank _
  rw [pos_iff_ne_zero, factors.finrank_pow_ramification_idx]
  exact mul_ne_zero (factors.ramification_idx_ne_zero p P) (factors.inertia_deg_ne_zero p P)
#align ideal.factors.finite_dimensional_quotient_pow Ideal.Factors.finite_dimensional_quotient_pow

universe w

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count P)
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [is_dedekind_domain.ramification_idx_eq_factors_count hp (factors.is_prime p P)
            (factors.ne_bot p P)]
#align ideal.factors.pi_quotient_equiv Ideal.Factors.piQuotientEquiv

@[simp]
theorem Factors.pi_quotient_equiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun P => Ideal.Quotient.mk _ x :=
  rfl
#align ideal.factors.pi_quotient_equiv_mk Ideal.Factors.pi_quotient_equiv_mk

@[simp]
theorem Factors.pi_quotient_equiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun P =>
      Ideal.Quotient.mk _ (algebraMap _ _ x) :=
  rfl
#align ideal.factors.pi_quotient_equiv_map Ideal.Factors.pi_quotient_equiv_map

variable (S)

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset,
        S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩; ext P
      simp only [Ideal.Quotient.mk_algebra_map, factors.pi_quotient_equiv_mk,
        factors.pi_quotient_equiv_map, Submodule.Quotient.quot_mk_eq_mk, Pi.algebra_map_apply,
        [anonymous], Pi.mul_apply, Ideal.Quotient.algebra_map_quotient_map_quotient,
        Ideal.Quotient.mk_eq_mk, Algebra.smul_def, _root_.map_mul, RingHomCompTriple.comp_apply]
      congr }
#align ideal.factors.pi_quotient_linear_equiv Ideal.Factors.piQuotientLinearEquiv

variable {S}

open BigOperators

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal.
-/
theorem sum_ramification_inertia (K L : Type _) [Field K] [Field L] [IsDomain R]
    [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] [Algebra S L] [IsFractionRing S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L] [IsNoetherian R S]
    [IsIntegralClosure S R L] [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (∑ P in (factors (map (algebraMap R S) p)).toFinset,
        ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P) =
      finrank K L :=
  by
  set e := ramification_idx (algebraMap R S) p
  set f := inertia_deg (algebraMap R S) p
  have inj_RL : Function.Injective (algebraMap R L) :=
    by
    rw [IsScalarTower.algebra_map_eq R K L, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective R K)
  have inj_RS : Function.Injective (algebraMap R S) :=
    by
    refine' Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ _) from _)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebra_map_eq]
    exact inj_RL
  calc
    (∑ P in (factors (map (algebraMap R S) p)).toFinset, e P * f P) =
        ∑ P in (factors (map (algebraMap R S) p)).toFinset.attach,
          finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) :=
      _
    _ =
        finrank (R ⧸ p)
          (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (Module.Free.finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := _
    _ = finrank K L := _
    
  · rw [← Finset.sum_attach]
    refine' Finset.sum_congr rfl fun P _ => _
    rw [factors.finrank_pow_ramification_idx]
  · refine' LinearEquiv.finrank_eq (factors.pi_quotient_linear_equiv S p _).symm
    rwa [Ne.def, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp inj_RS,
      le_bot_iff]
  · exact finrank_quotient_map p K L
#align ideal.sum_ramification_inertia Ideal.sum_ramification_inertia

end FactorsMap

end Ideal

