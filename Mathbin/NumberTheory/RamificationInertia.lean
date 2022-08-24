/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.FieldTheory.Separable
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.LinearAlgebra.FreeModule.Pid
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.RingTheory.DedekindDomain.Ideal
import Mathbin.RingTheory.Localization.Module

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

variable {R : Type u} [CommRingₓ R]

variable {S : Type v} [CommRingₓ S] (f : R →+* S)

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
  sup { n | map f p ≤ P ^ n }

variable {f p P}

theorem ramification_idx_eq_find (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) : ramificationIdx f p P = Nat.findₓ h :=
  Nat.Sup_def h

theorem ramification_idx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) : ramificationIdx f p P = 0 :=
  dif_neg
    (by
      push_neg <;> exact h)

theorem ramification_idx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx f p P = n := by
  have : ∀ k : ℕ, map f p ≤ P ^ k → k ≤ n := by
    intro k hk
    refine' le_of_not_ltₓ fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  · refine' le_antisymmₓ (Nat.find_min'ₓ _ this) (le_of_not_gtₓ fun h : Nat.findₓ _ < n => _)
    obtain this' := Nat.find_specₓ ⟨n, this⟩
    exact h.not_le (this' _ hle)
    

theorem ramification_idx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx f p P < n := by
  cases n
  · simpa using hgt
    
  rw [Nat.lt_succ_iffₓ]
  have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
    refine' fun k hk => le_of_not_ltₓ fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  exact Nat.find_min'ₓ ⟨n, this⟩ this

@[simp]
theorem ramification_idx_bot : ramificationIdx f ⊥ P = 0 :=
  dif_neg <|
    not_exists.mpr fun n hn =>
      n.lt_succ_self.not_le
        (hn _
          (by
            simp ))

@[simp]
theorem ramification_idx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx f p P = 0 :=
  ramification_idx_spec
    (by
      simp )
    (by
      simpa using h)

theorem ramification_idx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e) (hnle : ¬map f p ≤ P ^ (e + 1)) :
    ramificationIdx f p P ≠ 0 := by
  rwa [ramification_idx_spec hle hnle]

theorem le_pow_of_le_ramification_idx {n : ℕ} (hn : n ≤ ramificationIdx f p P) : map f p ≤ P ^ n := by
  contrapose! hn
  exact ramification_idx_lt hn

theorem le_pow_ramification_idx : map f p ≤ P ^ ramificationIdx f p P :=
  le_pow_of_le_ramification_idx (le_reflₓ _)

theorem le_comap_pow_ramification_idx : p ≤ comap f (P ^ ramificationIdx f p P) :=
  map_le_iff_le_comap.mp le_pow_ramification_idx

theorem le_comap_of_ramification_idx_ne_zero (h : ramificationIdx f p P ≠ 0) : p ≤ comap f P :=
  Ideal.map_le_iff_le_comap.mp <| le_pow_ramification_idx.trans <| Ideal.pow_le_self <| h

namespace IsDedekindDomain

variable [IsDomain S] [IsDedekindDomain S]

theorem ramification_idx_eq_normalized_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  refine' ramification_idx_spec (Ideal.le_of_dvd _) (mt ideal.dvd_iff_le.mpr _) <;>
    rw [dvd_iff_normalized_factors_le_normalized_factors (pow_ne_zero _ hP0) hp0, normalized_factors_pow,
      normalized_factors_irreducible hPirr, normalize_eq, Multiset.nsmul_singleton, ← Multiset.le_count_iff_repeat_le]
  · exact (Nat.lt_succ_selfₓ _).not_le
    

theorem ramification_idx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (factors (map f p)).count P := by
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0, factors_eq_normalized_factors]

theorem ramification_idx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) : ramificationIdx f p P ≠ 0 :=
  by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := le_bot_iff.mp le
    contradiction
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ := exists_mem_normalized_factors_of_dvd hp0 hPirr (ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

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
          (Ideal.Quotient.lift p (P f)) fun a ha => Quotient.eq_zero_iff_mem.mpr <| mem_comap.mp <| hPp.symm ▸ ha
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertia_deg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] : inertiaDeg f p P = 0 := by
  have := ideal.quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[simp]
theorem inertia_deg_algebra_map [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)] [IsScalarTower R (R ⧸ p) (S ⧸ P)]
    [hp : p.IsMaximal] : inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P) := by
  nontriviality S ⧸ P using inertia_deg_of_subsingleton, finrank_zero_of_subsingleton
  have := comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P)).Injective
  rw [inertia_deg, dif_pos this]
  congr
  refine' Algebra.algebra_ext _ _ fun x' => (Quotientₓ.induction_on' x') fun x => _
  change Ideal.Quotient.lift p _ _ (Ideal.Quotient.mk p x) = algebraMap _ _ (Ideal.Quotient.mk p x)
  rw [Ideal.Quotient.lift_mk, ← Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_eq, ←
    Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_apply]

end DecEq

section FinrankQuotientMap

open BigOperators

open nonZeroDivisors

variable [Algebra R S]

variable {K : Type _} [Field K] [Algebra R K] [hRK : IsFractionRing R K]

variable {L : Type _} [Field L] [Algebra S L] [IsFractionRing S L]

variable {V V' V'' : Type _}

variable [AddCommGroupₓ V] [Module R V] [Module K V] [IsScalarTower R K V]

variable [AddCommGroupₓ V'] [Module R V'] [Module S V'] [IsScalarTower R S V']

variable [AddCommGroupₓ V''] [Module R V'']

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
    (hRS : (algebraMap R S).ker ≠ ⊤) (f : V'' →ₗ[R] V) (hf : Function.Injective f) (f' : V'' →ₗ[R] V') {ι : Type _}
    {b : ι → V''} (hb' : LinearIndependent S (f' ∘ b)) : LinearIndependent K (f ∘ b) := by
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
  let g' := fun i => if h : i ∈ s then g'' i h else 0
  have hg' : ∀ i ∈ s, algebraMap _ _ (g' i) = a * g i := by
    intro i hi
    exact (congr_arg _ (dif_pos hi)).trans (hg'' i hi)
  -- Because `R/I` is nontrivial, we can lift `g` to a nontrivial linear dependence in `S`.
  have hgI : algebraMap R S (g' j) ≠ 0 := by
    simp only [FractionalIdeal.mem_coe_ideal, not_exists, not_and'] at hgI
    exact hgI _ (hg' j hjs)
  refine' ⟨fun i => algebraMap R S (g' i), _, j, hjs, hgI⟩
  have eq : f (∑ i in s, g' i • b i) = 0 := by
    rw [LinearMap.map_sum, ← smul_zero a, ← Eq, Finset.smul_sum, Finset.sum_congr rfl]
    intro i hi
    rw [LinearMap.map_smul, ← IsScalarTower.algebra_map_smul K, hg' i hi, ← smul_assoc, smul_eq_mul]
    infer_instance
  simp only [IsScalarTower.algebra_map_smul, ← LinearMap.map_smul, ← LinearMap.map_sum, (f.map_eq_zero_iff hf).mp Eq,
    LinearMap.map_zero]

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
theorem FinrankQuotientMap.span_eq_top [IsDomain R] [IsDomain S] [Algebra K L] [IsNoetherian R S] [Algebra R L]
    [IsScalarTower R S L] [IsScalarTower R K L] [IsIntegralClosure S R L] [NoZeroSmulDivisors R K] (hp : p ≠ ⊤)
    (b : Set S) (hb' : Submodule.span R b⊔(p.map (algebraMap R S)).restrictScalars R = ⊤) :
    Submodule.span K (algebraMap S L '' b) = ⊤ := by
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebra_map_eq R K L]
    exact (algebraMap K L).Injective.comp (NoZeroSmulDivisors.algebra_map_injective R K)
  -- Let `M` be the `R`-module spanned by the proposed basis elements.
  set M : Submodule R S := Submodule.span R b with hM
  -- Then `S / M` is generated by some finite set of `n` vectors `a`.
  letI h : Module.Finite R (S ⧸ M) := Module.Finite.of_surjective (Submodule.mkq _) (Submodule.Quotient.mk_surjective _)
  obtain ⟨n, a, ha⟩ := @Module.Finite.exists_fin _ _ _ h
  -- Because the image of `p` in `S / M` is `⊤`,
  have smul_top_eq : p • (⊤ : Submodule R (S ⧸ M)) = ⊤ := by
    calc
      p • ⊤ = Submodule.map M.mkq (p • ⊤) := by
        rw [Submodule.map_smul'', Submodule.map_top, M.range_mkq]
      _ = ⊤ := by
        rw [Ideal.smul_top_eq_map, (Submodule.map_mkq_eq_top M _).mpr hb']
      
  -- we can write the elements of `a` as `p`-linear combinations of other elements of `a`.
  have exists_sum : ∀ x : S ⧸ M, ∃ a' : Finₓ n → R, (∀ i, a' i ∈ p) ∧ (∑ i, a' i • a i) = x := by
    intro x
    obtain ⟨a'', ha'', hx⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum p a x).1 _
    · refine' ⟨fun i => a'' i, fun i => ha'' _, _⟩
      rw [← hx, Finsupp.sum_fintype]
      exact fun _ => zero_smul _ _
      
    · rw [ha, smul_top_eq]
      exact Submodule.mem_top
      
  choose A' hA'p hA' using fun i => exists_sum (a i)
  -- This gives us a(n invertible) matrix `A` such that `det A ∈ (M = span R b)`,
  let A : Matrix (Finₓ n) (Finₓ n) R := A' - 1
  let B := A.adjugate
  have A_smul : ∀ i, (∑ j, A i j • a j) = 0 := by
    intros
    simp only [A, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, hA', Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  -- since `span S {det A} / M = 0`.
  have d_smul : ∀ i, A.det • a i = 0 := by
    intro i
    calc
      A.det • a i = ∑ j, (B ⬝ A) i j • a j := _
      _ = ∑ k, B i k • ∑ j, A k j • a j := _
      _ = 0 := Finset.sum_eq_zero fun k _ => _
      
    · simp only [Matrix.adjugate_mul, Pi.smul_apply, Matrix.one_apply, mul_ite, ite_smul, smul_eq_mul, mul_oneₓ,
        mul_zero, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      
    · simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      rw [Finset.sum_comm]
      
    · rw [A_smul, smul_zero]
      
  -- In the rings of integers we have the desired inclusion.
  have span_d : (Submodule.span S ({algebraMap R S A.det} : Set S)).restrictScalars R ≤ M := by
    intro x hx
    rw [Submodule.restrict_scalars_mem] at hx
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hx
    rw [smul_eq_mul, mul_comm, ← Algebra.smul_def] at hx⊢
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    obtain ⟨a', _, quot_x_eq⟩ := exists_sum (Submodule.Quotient.mk x')
    simp_rw [← quot_x_eq, Finset.smul_sum, smul_comm A.det, d_smul, smul_zero, Finset.sum_const_zero]
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
      IsUnit.mk0 _ ((map_ne_zero_iff (algebraMap R L) hRL).mpr (@ne_zero_of_map _ _ _ _ _ _ (Ideal.Quotient.mk p) _ _))
    haveI := Ideal.Quotient.nontrivial hp
    calc
      Ideal.Quotient.mk p A.det = Matrix.det ((Ideal.Quotient.mk p).mapMatrix A) := by
        rw [RingHom.map_det, RingHom.map_matrix_apply]
      _ = Matrix.det ((Ideal.Quotient.mk p).mapMatrix (A' - 1)) := rfl
      _ = Matrix.det fun i j => (Ideal.Quotient.mk p) (A' i j) - (1 : Matrix (Finₓ n) (Finₓ n) (R ⧸ p)) i j := _
      _ = Matrix.det (-1 : Matrix (Finₓ n) (Finₓ n) (R ⧸ p)) := _
      _ = (-1 : R ⧸ p) ^ n := by
        rw [Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_oneₓ]
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
    haveI : NoZeroSmulDivisors R L := NoZeroSmulDivisors.of_algebra_map_injective hRL
    rw [← IsFractionRing.is_algebraic_iff' R S]
    intro x
    exact IsIntegral.is_algebraic _ (is_integral_of_noetherian inferInstance _)
    

include hRK

variable (K L)

/-- If `p` is a maximal ideal of `R`, and `S` is the integral closure of `R` in `L`,
then the dimension `[S/pS : R/p]` is equal to `[Frac(S) : Frac(R)]`. -/
theorem finrank_quotient_map [IsDomain R] [IsDomain S] [IsDedekindDomain R] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L] [IsIntegralClosure S R L] [hp : p.IsMaximal] [IsNoetherian R S] :
    finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) = finrank K L := by
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
  have b''_sp : Submodule.span _ (Set.Range b'') = ⊤ := _
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
        Submodule.span (R ⧸ p) (Set.Range b) :=
      b.mem_span _
    rw [← @Submodule.restrict_scalars_mem R,
      Algebra.span_restrict_scalars_eq_span_of_surjective
        (show Function.Surjective (algebraMap R (R ⧸ p)) from Ideal.Quotient.mk_surjective) _,
      b_eq_b', Set.range_comp, ← Submodule.map_span] at mem_span_b
    obtain ⟨y, y_mem, y_eq⟩ := submodule.mem_map.mp mem_span_b
    suffices y + -(y - x) ∈ _ by
      simpa
    rw [LinearMap.restrict_scalars_apply, Submodule.mkq_apply, Submodule.mkq_apply, Submodule.Quotient.eq] at y_eq
    exact add_mem (Submodule.mem_sup_left y_mem) (neg_mem <| Submodule.mem_sup_right y_eq)
    
  · have := b.linear_independent
    rw [b_eq_b'] at this
    convert
      finrank_quotient_map.linear_independent_of_nontrivial K _ ((Algebra.linearMap S L).restrictScalars R) _
        ((Submodule.mkq _).restrictScalars R) this
    · rw [quotient.algebra_map_eq, Ideal.mk_ker]
      exact hp.ne_top
      
    · exact IsFractionRing.injective S L
      
    

end FinrankQuotientMap

section FactLeComap

-- mathport name: «expre»
local notation "e" => ramificationIdx f p P

/-- `R / p` has a canonical map to `S / (P ^ e)`, where `e` is the ramification index
of `P` over `p`. -/
noncomputable instance Quotient.algebraQuotientPowRamificationIdx : Algebra (R ⧸ p) (S ⧸ P ^ e) :=
  Quotient.algebraQuotientOfLeComap (Ideal.map_le_iff_le_comap.mp le_pow_ramification_idx)

@[simp]
theorem Quotient.algebra_map_quotient_pow_ramification_idx (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P ^ e) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk _ (f x) :=
  rfl

variable [hfp : Fact (ramificationIdx f p P ≠ 0)]

include hfp

/-- If `P` lies over `p`, then `R / p` has a canonical map to `S / P`.

This can't be an instance since the map `f : R → S` is generally not inferrable.
-/
def Quotient.algebraQuotientOfRamificationIdxNeZero : Algebra (R ⧸ p) (S ⧸ P) :=
  Quotient.algebraQuotientOfLeComap (le_comap_of_ramification_idx_ne_zero hfp.out)

-- In this file, the value for `f` can be inferred.
attribute [local instance] Ideal.Quotient.algebraQuotientOfRamificationIdxNeZero

@[simp]
theorem Quotient.algebra_map_quotient_of_ramification_idx_ne_zero (x : R) :
    algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk _ (f x) :=
  rfl

omit hfp

/-- The inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)`. -/
@[simps]
def powQuotSuccInclusion (i : ℕ) : Ideal.map (P ^ e) (P ^ (i + 1)) →ₗ[R ⧸ p] Ideal.map (P ^ e) (P ^ i) where
  toFun := fun x => ⟨x, Ideal.map_mono (Ideal.pow_le_pow i.le_succ) x.2⟩
  map_add' := fun x y => rfl
  map_smul' := fun c x => rfl

theorem pow_quot_succ_inclusion_injective (i : ℕ) : Function.Injective (powQuotSuccInclusion f p P i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨x, hx⟩ hx0
  rw [Subtype.ext_iff] at hx0⊢
  rwa [pow_quot_succ_inclusion_apply_coe] at hx0

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`.
See `quotient_to_quotient_range_pow_quot_succ` for this as a linear map,
and `quotient_range_pow_quot_succ_inclusion_equiv` for this as a linear equivalence.
-/
noncomputable def quotientToQuotientRangePowQuotSuccAux {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P → (P ^ i).map (P ^ e) ⧸ (powQuotSuccInclusion f p P i).range :=
  Quotientₓ.map' (fun x : S => ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩) fun x y h => by
    rw [Submodule.quotient_rel_r_def] at h⊢
    simp only [_root_.map_mul, LinearMap.mem_range]
    refine' ⟨⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul h a_mem)⟩, _⟩
    ext
    rw [pow_quot_succ_inclusion_apply_coe, Subtype.coe_mk, Submodule.coe_sub, Subtype.coe_mk, Subtype.coe_mk,
      _root_.map_mul, map_sub, sub_mul]

theorem quotient_to_quotient_range_pow_quot_succ_aux_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSuccAux f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  by
  apply Quotientₓ.map'_mk'

include hfp

/-- `S ⧸ P` embeds into the quotient by `P^(i+1) ⧸ P^e` as a subspace of `P^i ⧸ P^e`. -/
noncomputable def quotientToQuotientRangePowQuotSucc {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) :
    S ⧸ P →ₗ[R ⧸ p] (P ^ i).map (P ^ e) ⧸ (powQuotSuccInclusion f p P i).range where
  toFun := quotientToQuotientRangePowQuotSuccAux f p P a_mem
  map_add' := by
    intro x y
    refine' Quotientₓ.induction_on' x fun x => Quotientₓ.induction_on' y fun y => _
    simp only [Submodule.Quotient.mk'_eq_mk, ← Submodule.Quotient.mk_add,
      quotient_to_quotient_range_pow_quot_succ_aux_mk, add_mulₓ]
    refine' congr_arg Submodule.Quotient.mk _
    ext
    rfl
  map_smul' := by
    intro x y
    refine' Quotientₓ.induction_on' x fun x => Quotientₓ.induction_on' y fun y => _
    simp only [Submodule.Quotient.mk'_eq_mk, ← Submodule.Quotient.mk_add,
      quotient_to_quotient_range_pow_quot_succ_aux_mk, RingHom.id_apply]
    refine' congr_arg Submodule.Quotient.mk _
    ext
    simp only [Subtype.coe_mk, _root_.map_mul, Algebra.smul_def, Submodule.coe_mk, mul_assoc, Ideal.Quotient.mk_eq_mk,
      Submodule.coe_smul_of_tower, Ideal.Quotient.algebra_map_quotient_pow_ramification_idx]

theorem quotient_to_quotient_range_pow_quot_succ_mk {i : ℕ} {a : S} (a_mem : a ∈ P ^ i) (x : S) :
    quotientToQuotientRangePowQuotSucc f p P a_mem (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨_, Ideal.mem_map_of_mem _ (Ideal.mul_mem_left _ x a_mem)⟩ :=
  quotient_to_quotient_range_pow_quot_succ_aux_mk f p P a_mem x

theorem quotient_to_quotient_range_pow_quot_succ_injective [IsDomain S] [IsDedekindDomain S] [P.IsPrime] {i : ℕ}
    (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) :
    Function.Injective (quotientToQuotientRangePowQuotSucc f p P a_mem) := fun x =>
  (Quotientₓ.induction_on' x) fun x y =>
    (Quotientₓ.induction_on' y) fun y h => by
      have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow hi
      simp only [Submodule.Quotient.mk'_eq_mk, quotient_to_quotient_range_pow_quot_succ_mk, Submodule.Quotient.eq,
        LinearMap.mem_range, Subtype.ext_iff, Subtype.coe_mk, Submodule.coe_sub] at h⊢
      rcases h with ⟨⟨⟨z⟩, hz⟩, h⟩
      rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
        sup_eq_left.mpr Pe_le_Pi1] at hz
      rw [pow_quot_succ_inclusion_apply_coe, Subtype.coe_mk, Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk,
        ← map_sub, Ideal.Quotient.eq, ← sub_mul] at h
      exact (Ideal.IsPrime.mul_mem_pow _ ((Submodule.sub_mem_iff_right _ hz).mp (Pe_le_Pi1 h))).resolve_right a_not_mem

theorem quotient_to_quotient_range_pow_quot_succ_surjective [IsDomain S] [IsDedekindDomain S] (hP0 : P ≠ ⊥)
    [hP : P.IsPrime] {i : ℕ} (hi : i < e) {a : S} (a_mem : a ∈ P ^ i) (a_not_mem : a ∉ P ^ (i + 1)) :
    Function.Surjective (quotientToQuotientRangePowQuotSucc f p P a_mem) := by
  rintro ⟨⟨⟨x⟩, hx⟩⟩
  have Pe_le_Pi : P ^ e ≤ P ^ i := Ideal.pow_le_pow hi.le
  have Pe_le_Pi1 : P ^ e ≤ P ^ (i + 1) := Ideal.pow_le_pow hi
  rw [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.mem_quotient_iff_mem_sup,
    sup_eq_left.mpr Pe_le_Pi] at hx
  suffices hx' : x ∈ Ideal.span {a}⊔P ^ (i + 1)
  · obtain ⟨y', hy', z, hz, rfl⟩ := submodule.mem_sup.mp hx'
    obtain ⟨y, rfl⟩ := ideal.mem_span_singleton.mp hy'
    refine' ⟨Submodule.Quotient.mk y, _⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, quotient_to_quotient_range_pow_quot_succ_mk, Submodule.Quotient.eq,
      LinearMap.mem_range, Subtype.ext_iff, Subtype.coe_mk, Submodule.coe_sub]
    refine' ⟨⟨_, Ideal.mem_map_of_mem _ (Submodule.neg_mem _ hz)⟩, _⟩
    rw [pow_quot_succ_inclusion_apply_coe, Subtype.coe_mk, Ideal.Quotient.mk_eq_mk, map_add, mul_comm y a,
      sub_add_cancel', map_neg]
    
  letI := Classical.decEq (Ideal S)
  rw [sup_eq_prod_inf_factors _ (pow_ne_zero _ hP0), normalized_factors_pow,
    normalized_factors_irreducible ((Ideal.prime_iff_is_prime hP0).mpr hP).Irreducible, normalize_eq,
    Multiset.nsmul_singleton, Multiset.inter_repeat, Multiset.prod_repeat]
  rw [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq] at a_mem a_not_mem
  rwa [Ideal.count_normalized_factors_eq a_mem a_not_mem, min_eq_leftₓ i.le_succ]
  · intro ha
    rw [ideal.span_singleton_eq_bot.mp ha] at a_not_mem
    have := (P ^ (i + 1)).zero_mem
    contradiction
    

/-- Quotienting `P^i / P^e` by its subspace `P^(i+1) ⧸ P^e` is
`R ⧸ p`-linearly isomorphic to `S ⧸ P`. -/
noncomputable def quotientRangePowQuotSuccInclusionEquiv [IsDomain S] [IsDedekindDomain S] [P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hi : i < e) : ((P ^ i).map (P ^ e) ⧸ (powQuotSuccInclusion f p P i).range) ≃ₗ[R ⧸ p] S ⧸ P := by
  choose a a_mem a_not_mem using
    SetLike.exists_of_lt (Ideal.strict_anti_pow P hP (Ideal.IsPrime.ne_top inferInstance) (le_reflₓ i.succ))
  refine' (LinearEquiv.ofBijective _ _ _).symm
  · exact quotient_to_quotient_range_pow_quot_succ f p P a_mem
    
  · exact quotient_to_quotient_range_pow_quot_succ_injective f p P hi a_mem a_not_mem
    
  · exact quotient_to_quotient_range_pow_quot_succ_surjective f p P hP hi a_mem a_not_mem
    

/-- Since the inclusion `(P^(i + 1) / P^e) ⊂ (P^i / P^e)` has a kernel isomorphic to `P / S`,
`[P^i / P^e : R / p] = [P^(i+1) / P^e : R / p] + [P / S : R / p]` -/
theorem dim_pow_quot_aux [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥) {i : ℕ}
    (hi : i < e) :
    Module.rank (R ⧸ p) (Ideal.map (P ^ e) (P ^ i)) =
      Module.rank (R ⧸ p) (S ⧸ P) + Module.rank (R ⧸ p) (Ideal.map (P ^ e) (P ^ (i + 1))) :=
  by
  letI : Field (R ⧸ p) := Ideal.Quotient.field _
  rw [dim_eq_of_injective _ (pow_quot_succ_inclusion_injective f p P i),
    (quotient_range_pow_quot_succ_inclusion_equiv f p P hP0 hi).symm.dim_eq]
  exact (dim_quotient_add_dim (LinearMap.range (pow_quot_succ_inclusion f p P i))).symm

theorem dim_pow_quot [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥) (i : ℕ) (hi : i ≤ e) :
    Module.rank (R ⧸ p) (Ideal.map (P ^ e) (P ^ i)) = (e - i) • Module.rank (R ⧸ p) (S ⧸ P) := by
  refine' @Nat.decreasingInduction' _ i e (fun j lt_e le_j ih => _) hi _
  · rw [dim_pow_quot_aux f p P _ lt_e, ih, ← succ_nsmul, Nat.sub_succ, ← Nat.succ_eq_add_one,
      Nat.succ_pred_eq_of_posₓ (Nat.sub_pos_of_ltₓ lt_e)]
    assumption
    
  · rw [Nat.sub_self, zero_nsmul, map_quotient_self]
    exact dim_bot (R ⧸ p) (S ⧸ P ^ e)
    

omit hfp

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]` is equal to `e * [S/P : R/p]`. -/
theorem dim_prime_pow_ramification_idx [IsDomain S] [IsDedekindDomain S] [p.IsMaximal] [P.IsPrime] (hP0 : P ≠ ⊥)
    (he : e ≠ 0) :
    Module.rank (R ⧸ p) (S ⧸ P ^ e) =
      e •
        @Module.rank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <| @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ ⟨he⟩) :=
  by
  letI : Fact (e ≠ 0) := ⟨he⟩
  have := dim_pow_quot f p P hP0 0 (Nat.zero_leₓ e)
  rw [pow_zeroₓ, Nat.sub_zero, Ideal.one_eq_top, Ideal.map_top] at this
  exact (dim_top (R ⧸ p) _).symm.trans this

/-- If `p` is a maximal ideal of `R`, `S` extends `R` and `P^e` lies over `p`,
then the dimension `[S/(P^e) : R/p]`, as a natural number, is equal to `e * [S/P : R/p]`. -/
theorem finrank_prime_pow_ramification_idx [IsDomain S] [IsDedekindDomain S] (hP0 : P ≠ ⊥) [p.IsMaximal] [P.IsPrime]
    (he : e ≠ 0) :
    finrank (R ⧸ p) (S ⧸ P ^ e) =
      e *
        @finrank (R ⧸ p) (S ⧸ P) _ _
          (@Algebra.toModule _ _ _ _ <| @Quotient.algebraQuotientOfRamificationIdxNeZero _ _ _ _ _ ⟨he⟩) :=
  by
  letI : Fact (e ≠ 0) := ⟨he⟩
  letI : Algebra (R ⧸ p) (S ⧸ P) := quotient.algebra_quotient_of_ramification_idx_ne_zero f p P
  letI := Ideal.Quotient.field p
  have hdim := dim_prime_pow_ramification_idx _ _ _ hP0 he
  by_cases' hP : FiniteDimensional (R ⧸ p) (S ⧸ P)
  · haveI := hP
    haveI := (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mpr hP
    refine' Cardinal.nat_cast_injective _
    rw [finrank_eq_dim, Nat.cast_mulₓ, finrank_eq_dim, hdim, nsmul_eq_mul]
    
  have hPe := mt (finite_dimensional_iff_of_rank_eq_nsmul he hdim).mp hP
  simp only [finrank_of_infinite_dimensional hP, finrank_of_infinite_dimensional hPe, mul_zero]

end FactLeComap

section FactorsMap

open Classical

/-! ## Properties of the factors of `p.map (algebra_map R S)` -/


variable [IsDomain S] [IsDedekindDomain S] [Algebra R S]

theorem Factors.ne_bot (P : (factors (map (algebraMap R S) p)).toFinset) : (P : Ideal S) ≠ ⊥ :=
  (prime_of_factor _ (Multiset.mem_to_finset.mp P.2)).ne_zero

instance Factors.is_prime (P : (factors (map (algebraMap R S) p)).toFinset) : IsPrime (P : Ideal S) :=
  Ideal.is_prime_of_prime (prime_of_factor _ (Multiset.mem_to_finset.mp P.2))

theorem Factors.ramification_idx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    ramificationIdx (algebraMap R S) p P ≠ 0 :=
  IsDedekindDomain.ramification_idx_ne_zero (ne_zero_of_mem_factors (Multiset.mem_to_finset.mp P.2))
    (Factors.is_prime p P) (Ideal.le_of_dvd (dvd_of_mem_factors (Multiset.mem_to_finset.mp P.2)))

instance Factors.fact_ramification_idx_ne_zero (P : (factors (map (algebraMap R S) p)).toFinset) :
    Fact (ramificationIdx (algebraMap R S) p P ≠ 0) :=
  ⟨Factors.ramification_idx_ne_zero p P⟩

attribute [local instance] quotient.algebra_quotient_of_ramification_idx_ne_zero

instance Factors.is_scalar_tower (P : (factors (map (algebraMap R S) p)).toFinset) :
    IsScalarTower R (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsScalarTower.of_algebra_map_eq fun x => by
    simp

attribute [local instance] Ideal.Quotient.field

theorem Factors.finrank_pow_ramification_idx [p.IsMaximal] (P : (factors (map (algebraMap R S) p)).toFinset) :
    finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) =
      ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P :=
  by
  rw [finrank_prime_pow_ramification_idx, inertia_deg_algebra_map]
  exact factors.ne_bot p P

instance Factors.finite_dimensional_quotient [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) : FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S)) :=
  IsNoetherian.iff_fg.mp <|
    is_noetherian_of_tower R <|
      is_noetherian_of_surjective S (Ideal.Quotient.mkₐ _ _).toLinearMap <|
        LinearMap.range_eq_top.mpr Ideal.Quotient.mk_surjective

theorem Factors.inertia_deg_ne_zero [IsNoetherian R S] [p.IsMaximal] (P : (factors (map (algebraMap R S) p)).toFinset) :
    inertiaDeg (algebraMap R S) p P ≠ 0 := by
  rw [inertia_deg_algebra_map]
  exact (finite_dimensional.finrank_pos_iff.mpr inferInstance).ne'

instance Factors.finite_dimensional_quotient_pow [IsNoetherian R S] [p.IsMaximal]
    (P : (factors (map (algebraMap R S) p)).toFinset) :
    FiniteDimensional (R ⧸ p) (S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) := by
  refine' FiniteDimensional.finite_dimensional_of_finrank _
  rw [pos_iff_ne_zero, factors.finrank_pow_ramification_idx]
  exact mul_ne_zero (factors.ramification_idx_ne_zero p P) (factors.inertia_deg_ne_zero p P)

universe w

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`, then `S ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    S ⧸ map (algebraMap R S) p ≃+*
      ∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
    @RingEquiv.piCongrRight (factors (map (algebraMap R S) p)).toFinset
      (fun P => S ⧸ (P : Ideal S) ^ (factors (map (algebraMap R S) p)).count P)
      (fun P => S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P) _ _
      fun P : (factors (map (algebraMap R S) p)).toFinset =>
      Ideal.quotEquivOfEq <| by
        rw [is_dedekind_domain.ramification_idx_eq_factors_count hp (factors.is_prime p P) (factors.ne_bot p P)]

@[simp]
theorem Factors.pi_quotient_equiv_mk (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : S) :
    Factors.piQuotientEquiv p hp (Ideal.Quotient.mk _ x) = fun P => Ideal.Quotient.mk _ x :=
  rfl

@[simp]
theorem Factors.pi_quotient_equiv_map (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) (x : R) :
    Factors.piQuotientEquiv p hp (algebraMap _ _ x) = fun P => Ideal.Quotient.mk _ (algebraMap _ _ x) :=
  rfl

/-- **Chinese remainder theorem** for a ring of integers: if the prime ideal `p : ideal R`
factors in `S` as `∏ i, P i ^ e i`,
then `S ⧸ I` factors `R ⧸ I`-linearly as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def Factors.piQuotientLinearEquiv (p : Ideal R) (hp : map (algebraMap R S) p ≠ ⊥) :
    (S ⧸ map (algebraMap R S) p) ≃ₗ[R ⧸ p]
      ∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ ramificationIdx (algebraMap R S) p P :=
  { Factors.piQuotientEquiv p hp with
    map_smul' := by
      rintro ⟨c⟩ ⟨x⟩
      ext P
      simp only [Ideal.Quotient.mk_algebra_map, factors.pi_quotient_equiv_mk, factors.pi_quotient_equiv_map,
        Submodule.Quotient.quot_mk_eq_mk, Pi.algebra_map_apply, RingEquiv.to_fun_eq_coe, Pi.mul_apply,
        Ideal.Quotient.algebra_map_quotient_map_quotient, Ideal.Quotient.mk_eq_mk, Algebra.smul_def, _root_.map_mul,
        RingHomCompTriple.comp_apply]
      congr }

open BigOperators

/-- The **fundamental identity** of ramification index `e` and inertia degree `f`:
for `P` ranging over the primes lying over `p`, `∑ P, e P * f P = [Frac(S) : Frac(R)]`;
here `S` is a finite `R`-module (and thus `Frac(S) : Frac(R)` is a finite extension) and `p`
is maximal.
-/
theorem sum_ramification_inertia (K L : Type _) [Field K] [Field L] [IsDomain R] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R S L]
    [IsScalarTower R K L] [IsNoetherian R S] [IsIntegralClosure S R L] [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (∑ P in (factors (map (algebraMap R S) p)).toFinset,
        ramificationIdx (algebraMap R S) p P * inertiaDeg (algebraMap R S) p P) =
      finrank K L :=
  by
  set e := ramification_idx (algebraMap R S) p
  set f := inertia_deg (algebraMap R S) p
  have inj_RL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebra_map_eq R K L, RingHom.coe_comp]
    exact (RingHom.injective _).comp (IsFractionRing.injective R K)
  have inj_RS : Function.Injective (algebraMap R S) := by
    refine' Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ _) from _)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebra_map_eq]
    exact inj_RL
  calc
    (∑ P in (factors (map (algebraMap R S) p)).toFinset, e P * f P) =
        ∑ P in (factors (map (algebraMap R S) p)).toFinset.attach, finrank (R ⧸ p) (S ⧸ (P : Ideal S) ^ e P) :=
      _
    _ = finrank (R ⧸ p) (∀ P : (factors (map (algebraMap R S) p)).toFinset, S ⧸ (P : Ideal S) ^ e P) :=
      (Module.Free.finrank_pi_fintype (R ⧸ p)).symm
    _ = finrank (R ⧸ p) (S ⧸ map (algebraMap R S) p) := _
    _ = finrank K L := _
    
  · rw [← Finset.sum_attach]
    refine' Finset.sum_congr rfl fun P _ => _
    rw [factors.finrank_pow_ramification_idx]
    
  · refine' LinearEquiv.finrank_eq (factors.pi_quotient_linear_equiv p _).symm
    rwa [Ne.def, Ideal.map_eq_bot_iff_le_ker, (RingHom.injective_iff_ker_eq_bot _).mp inj_RS, le_bot_iff]
    
  · exact finrank_quotient_map p K L
    

end FactorsMap

end Ideal

