/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.RingTheory.UniqueFactorizationDomain
import Mathbin.RingTheory.Int.Basic
import Mathbin.NumberTheory.Divisors
import Mathbin.Algebra.IsPrimePow

/-!
# Squarefree elements of monoids
An element of a monoid is squarefree when it is not divisible by any squares
except the squares of units.

## Main Definitions
 - `squarefree r` indicates that `r` is only divisible by `x * x` if `x` is a unit.

## Main Results
 - `multiplicity.squarefree_iff_multiplicity_le_one`: `x` is `squarefree` iff for every `y`, either
  `multiplicity y x ≤ 1` or `is_unit y`.
 - `unique_factorization_monoid.squarefree_iff_nodup_factors`: A nonzero element `x` of a unique
 factorization monoid is squarefree iff `factors x` has no duplicate factors.
 - `nat.squarefree_iff_nodup_factors`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.
## Tags
squarefree, multiplicity

-/


variable {R : Type _}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoidₓ R] (r : R) : Prop :=
  ∀ x : R, x * x ∣ r → IsUnit x

@[simp]
theorem IsUnit.squarefree [CommMonoidₓ R] {x : R} (h : IsUnit x) : Squarefree x := fun y hdvd =>
  is_unit_of_mul_is_unit_left (is_unit_of_dvd_unit hdvd h)

@[simp]
theorem squarefree_one [CommMonoidₓ R] : Squarefree (1 : R) :=
  is_unit_one.Squarefree

@[simp]
theorem not_squarefree_zero [MonoidWithZeroₓ R] [Nontrivial R] : ¬Squarefree (0 : R) := by
  erw [not_forall]
  exact
    ⟨0, by
      simp ⟩

theorem Squarefree.ne_zero [MonoidWithZeroₓ R] [Nontrivial R] {m : R} (hm : Squarefree (m : R)) : m ≠ 0 := by
  rintro rfl
  exact not_squarefree_zero hm

@[simp]
theorem Irreducible.squarefree [CommMonoidₓ R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assoc] at hz
  rcases h.is_unit_or_is_unit hz with (hu | hu)
  · exact hu
    
  · apply is_unit_of_mul_is_unit_left hu
    

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.Irreducible.Squarefree

theorem Squarefree.of_mul_left [CommMonoidₓ R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree m := fun p hp =>
  hmn p (dvd_mul_of_dvd_left hp n)

theorem Squarefree.of_mul_right [CommMonoidₓ R] {m n : R} (hmn : Squarefree (m * n)) : Squarefree n := fun p hp =>
  hmn p (dvd_mul_of_dvd_right hp m)

theorem squarefree_of_dvd_of_squarefree [CommMonoidₓ R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x :=
  fun a h => hsq _ (h.trans hdvd)

namespace multiplicity

section CommMonoidₓ

variable [CommMonoidₓ R] [DecidableRel (Dvd.Dvd : R → R → Prop)]

theorem squarefree_iff_multiplicity_le_one (r : R) : Squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ IsUnit x := by
  refine' forall_congrₓ fun a => _
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_leₓ, imp_congr]
  swap
  · rfl
    
  convert Enat.add_one_le_iff_lt (Enat.coe_ne_top 1)
  norm_cast

end CommMonoidₓ

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero R] [WfDvdMonoid R]

theorem finite_prime_left {a b : R} (ha : Prime a) (hb : b ≠ 0) : multiplicity.Finite a b := by
  classical
  revert hb
  refine'
    WfDvdMonoid.induction_on_irreducible b
      (by
        contradiction)
      (fun u hu hu' => _) fun b p hb hp ih hpb => _
  · rw [multiplicity.finite_iff_dom, multiplicity.is_unit_right ha.not_unit hu]
    exact Enat.dom_coe 0
    
  · refine'
      multiplicity.finite_mul ha
        (multiplicity.finite_iff_dom.mpr (Enat.dom_of_le_coe (show multiplicity a p ≤ ↑1 from _))) (ih hb)
    norm_cast
    exact ((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a).resolve_right ha.not_unit
    

end CancelCommMonoidWithZero

end multiplicity

section Irreducible

variable [CommMonoidWithZero R] [WfDvdMonoid R]

theorem irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree (r : R) :
    (∀ x : R, Irreducible x → ¬x * x ∣ r) ↔ (r = 0 ∧ ∀ x : R, ¬Irreducible x) ∨ Squarefree r := by
  symm
  constructor
  · rintro (⟨rfl, h⟩ | h)
    · simpa using h
      
    intro x hx t
    exact hx.not_unit (h x t)
    
  intro h
  rcases eq_or_ne r 0 with (rfl | hr)
  · exact
      Or.inl
        (by
          simpa using h)
    
  right
  intro x hx
  by_contra i
  have : x ≠ 0 := by
    rintro rfl
    apply hr
    simpa only [zero_dvd_iff, mul_zero] using hx
  obtain ⟨j, hj₁, hj₂⟩ := WfDvdMonoid.exists_irreducible_factor i this
  exact h _ hj₁ ((mul_dvd_mul hj₂ hj₂).trans hx)

theorem squarefree_iff_irreducible_sq_not_dvd_of_ne_zero {r : R} (hr : r ≠ 0) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  simpa [hr] using (irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree r).symm

theorem squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R} (hr : ∃ x : R, Irreducible x) :
    Squarefree r ↔ ∀ x : R, Irreducible x → ¬x * x ∣ r := by
  rw [irreducible_sq_not_dvd_iff_eq_zero_and_no_irreducibles_or_squarefree, ← not_exists]
  simp only [hr, not_true, false_orₓ, and_falseₓ]

end Irreducible

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [Nontrivial R] [UniqueFactorizationMonoid R]

variable [NormalizationMonoid R]

theorem squarefree_iff_nodup_normalized_factors [DecidableEq R] {x : R} (x0 : x ≠ 0) :
    Squarefree x ↔ Multiset.Nodup (normalizedFactors x) := by
  have drel : DecidableRel (Dvd.Dvd : R → R → Prop) := by
    classical
    infer_instance
  have := drel
  rw [multiplicity.squarefree_iff_multiplicity_le_one, Multiset.nodup_iff_count_le_one]
  constructor <;> intro h a
  · by_cases' hmem : a ∈ normalized_factors x
    · have ha := irreducible_of_normalized_factor _ hmem
      rcases h a with (h | h)
      · rw [← normalize_normalized_factor _ hmem]
        rw [multiplicity_eq_count_normalized_factors ha x0] at h
        assumption_mod_cast
        
      · have := ha.1
        contradiction
        
      
    · simp [Multiset.count_eq_zero_of_not_mem hmem]
      
    
  · rw [or_iff_not_imp_right]
    intro hu
    by_cases' h0 : a = 0
    · simp [h0, x0]
      
    rcases WfDvdMonoid.exists_irreducible_factor hu h0 with ⟨b, hib, hdvd⟩
    apply le_transₓ (multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd)
    rw [multiplicity_eq_count_normalized_factors hib x0]
    specialize h (normalize b)
    assumption_mod_cast
    

theorem dvd_pow_iff_dvd_of_squarefree {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) : x ∣ y ^ n ↔ x ∣ y := by
  classical
  by_cases' hx : x = 0
  · simp [hx, pow_eq_zero_iff (Nat.pos_of_ne_zeroₓ h0)]
    
  by_cases' hy : y = 0
  · simp [hy, zero_pow (Nat.pos_of_ne_zeroₓ h0)]
    
  refine' ⟨fun h => _, fun h => h.pow h0⟩
  rw [dvd_iff_normalized_factors_le_normalized_factors hx (pow_ne_zero n hy), normalized_factors_pow,
    ((squarefree_iff_nodup_normalized_factors hx).1 hsq).le_nsmul_iff_le h0] at h
  rwa [dvd_iff_normalized_factors_le_normalized_factors hx hy]

end UniqueFactorizationMonoid

namespace Nat

theorem squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) : Squarefree n ↔ n.factors.Nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors h0, Nat.factors_eq]
  simp

theorem squarefree_iff_prime_squarefree {n : ℕ} : Squarefree n ↔ ∀ x, Prime x → ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

/-- Assuming that `n` has no factors less than `k`, returns the smallest prime `p` such that
  `p^2 ∣ n`. -/
def minSqFacAux : ℕ → ℕ → Option ℕ
  | n, k =>
    if h : n < k * k then none
    else
      have : Nat.sqrt n + 2 - (k + 2) < Nat.sqrt n + 2 - k := by
        rw [Nat.add_sub_add_right]
        exact Nat.min_fac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' + 2 - (k + 2) < Nat.sqrt n + 2 - k :=
          lt_of_le_of_ltₓ (Nat.sub_le_sub_rightₓ (Nat.add_le_add_rightₓ (Nat.sqrt_le_sqrt <| Nat.div_le_selfₓ _ _) _) _)
            this
        if k ∣ n' then some k else min_sq_fac_aux n' (k + 2)
      else min_sq_fac_aux n (k + 2)

/-- Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if there is no
  such `p` (that is, `n` is squarefree). See also `squarefree_iff_min_sq_fac`. -/
def minSqFac (n : ℕ) : Option ℕ :=
  if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

/-- The correctness property of the return value of `min_sq_fac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n` -/
def MinSqFacProp (n : ℕ) : Option ℕ → Prop
  | none => Squarefree n
  | some d => Prime d ∧ d * d ∣ n ∧ ∀ p, Prime p → p * p ∣ n → d ≤ p

theorem min_sq_fac_prop_div n {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o} (H : MinSqFacProp (n / k) o) :
    MinSqFacProp n o := by
  have : ∀ p, Prime p → p * p ∣ n → k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  cases' o with d
  · rw [min_sq_fac_prop, squarefree_iff_prime_squarefree] at H⊢
    exact fun p pp dp => H p pp ((dvd_div_iff dk).2 (this _ pp dp))
    
  · obtain ⟨H1, H2, H3⟩ := H
    simp only [dvd_div_iff dk] at H2 H3
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, fun p pp dp => H3 _ pp (this _ pp dp)⟩
    

theorem min_sq_fac_aux_has_prop :
    ∀ {n : ℕ} k, 0 < n → ∀ i, k = 2 * i + 3 → (∀ m, Prime m → m ∣ n → k ≤ m) → MinSqFacProp n (minSqFacAux n k)
  | n, k => fun n0 i e ih => by
    rw [min_sq_fac_aux]
    by_cases' h : n < k * k <;> simp [h]
    · refine' squarefree_iff_prime_squarefree.2 fun p pp d => _
      have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
      have := Nat.mul_le_mulₓ this this
      exact not_le_of_lt h (le_transₓ this (le_of_dvd n0 d))
      
    have k2 : 2 ≤ k := by
      subst e
      exact by
        decide
    have k0 : 0 < k :=
      lt_of_lt_of_leₓ
        (by
          decide)
        k2
    have IH : ∀ n', n' ∣ n → ¬k ∣ n' → min_sq_fac_prop n' (n'.minSqFacAux (k + 2)) := by
      intro n' nd' nk
      have hn' := le_of_dvd n0 nd'
      refine'
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
          lt_of_le_of_ltₓ (Nat.sub_le_sub_rightₓ (Nat.sqrt_le_sqrt hn') _) (Nat.min_fac_lemma n k h)
        @min_sq_fac_aux_has_prop n' (k + 2) (pos_of_dvd_of_pos nd' n0) (i + 1)
          (by
            simp [e, left_distrib])
          fun m m2 d => _
      cases' Nat.eq_or_lt_of_leₓ (ih m m2 (dvd_trans d nd')) with me ml
      · subst me
        contradiction
        
      apply (Nat.eq_or_lt_of_leₓ ml).resolve_left
      intro me
      rw [← me, e] at d
      change 2 * (i + 2) ∣ n' at d
      have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd')
      rw [e] at this
      exact
        absurd this
          (by
            decide)
    have pk : k ∣ n → Prime k := by
      refine' fun dk => prime_def_min_fac.2 ⟨k2, le_antisymmₓ (min_fac_le k0) _⟩
      exact ih _ (min_fac_prime (ne_of_gtₓ k2)) (dvd_trans (min_fac_dvd _) dk)
    split_ifs with dk dkk
    · exact ⟨pk dk, (Nat.dvd_div_iff dk).1 dkk, fun p pp d => ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩
      
    · specialize IH (n / k) (div_dvd_of_dvd dk) dkk
      exact min_sq_fac_prop_div _ (pk dk) dk (mt (Nat.dvd_div_iff dk).2 dkk) IH
      
    · exact IH n (dvd_refl _) dk
      

theorem min_sq_fac_has_prop (n : ℕ) : MinSqFacProp n (minSqFac n) := by
  dunfold min_sq_fac
  split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff d2).1 d4, fun p pp _ => pp.two_le⟩
    
  · cases' Nat.eq_zero_or_posₓ n with n0 n0
    · subst n0
      cases
        d4
          (by
            decide)
      
    refine' min_sq_fac_prop_div _ prime_two d2 (mt (dvd_div_iff d2).2 d4) _
    refine'
      min_sq_fac_aux_has_prop 3
        (Nat.div_pos (le_of_dvd n0 d2)
          (by
            decide))
        0 rfl _
    refine' fun p pp dp => succ_le_of_lt (lt_of_le_of_neₓ pp.two_le _)
    rintro rfl
    contradiction
    
  · cases' Nat.eq_zero_or_posₓ n with n0 n0
    · subst n0
      cases
        d2
          (by
            decide)
      
    refine' min_sq_fac_aux_has_prop _ n0 0 rfl _
    refine' fun p pp dp => succ_le_of_lt (lt_of_le_of_neₓ pp.two_le _)
    rintro rfl
    contradiction
    

theorem min_sq_fac_prime {n d : ℕ} (h : n.minSqFac = some d) : Prime d := by
  have := min_sq_fac_has_prop n
  rw [h] at this
  exact this.1

theorem min_sq_fac_dvd {n d : ℕ} (h : n.minSqFac = some d) : d * d ∣ n := by
  have := min_sq_fac_has_prop n
  rw [h] at this
  exact this.2.1

theorem min_sq_fac_le_of_dvd {n d : ℕ} (h : n.minSqFac = some d) {m} (m2 : 2 ≤ m) (md : m * m ∣ n) : d ≤ m := by
  have := min_sq_fac_has_prop n
  rw [h] at this
  have fd := min_fac_dvd m
  exact
    le_transₓ (this.2.2 _ (min_fac_prime <| ne_of_gtₓ m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (min_fac_le <|
        lt_of_lt_of_leₓ
          (by
            decide)
          m2)

theorem squarefree_iff_min_sq_fac {n : ℕ} : Squarefree n ↔ n.minSqFac = none := by
  have := min_sq_fac_has_prop n
  constructor <;> intro H
  · cases' n.min_sq_fac with d
    · rfl
      
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
    
  · rwa [H] at this
    

instance : DecidablePred (Squarefree : ℕ → Prop) := fun n => decidableOfIff' _ squarefree_iff_min_sq_fac

theorem squarefree_two : Squarefree 2 := by
  rw [squarefree_iff_nodup_factors] <;> norm_num

open UniqueFactorizationMonoid

theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    (n.divisors.filter Squarefree).val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.Powerset.val.map fun x => x.val.Prod :=
  by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, id.def, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def, mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      simp only [id.def, Finset.mem_powerset]
      rcases an with ⟨b, rfl⟩
      rw [mul_ne_zero_iff] at h0
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors h0.1] at hsq
      rw [Multiset.to_finset_subset, Multiset.to_finset_val, hsq.dedup, ← associated_iff_eq,
        normalized_factors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), normalized_factors_prod h0.1⟩
      
    · rintro ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset, ← Finset.val_le_iff, Multiset.to_finset_val] at hs
      have hs0 : s.val.prod ≠ 0 := by
        rw [Ne.def, Multiset.prod_eq_zero_iff]
        simp only [exists_prop, id.def, exists_eq_right]
        intro con
        apply
          not_irreducible_zero (irreducible_of_normalized_factor 0 (Multiset.mem_dedup.1 (Multiset.mem_of_le hs Con)))
      rw [(normalized_factors_prod h0).symm.dvd_iff_dvd_right]
      refine' ⟨⟨Multiset.prod_dvd_prod_of_le (le_transₓ hs (Multiset.dedup_le _)), h0⟩, _⟩
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx => irreducible_of_normalized_factor x (Multiset.mem_of_le (le_transₓ hs (Multiset.dedup_le _)) hx))
          (normalized_factors_prod hs0)
      rw [associated_eq_eq, Multiset.rel_eq] at h
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors hs0, h]
      apply s.nodup
      
    
  · intro x hx y hy h
    rw [← Finset.val_inj, ← Multiset.rel_eq, ← associated_eq_eq]
    rw [← Finset.mem_def, Finset.mem_powerset] at hx hy
    apply UniqueFactorizationMonoid.factors_unique _ _ (associated_iff_eq.2 h)
    · intro z hz
      apply irreducible_of_normalized_factor z
      rw [← Multiset.mem_to_finset]
      apply hx hz
      
    · intro z hz
      apply irreducible_of_normalized_factor z
      rw [← Multiset.mem_to_finset]
      apply hy hz
      
    

open BigOperators

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type _} [AddCommMonoidₓ α] {f : ℕ → α} :
    (∑ i in n.divisors.filter Squarefree, f i) =
      ∑ i in (UniqueFactorizationMonoid.normalizedFactors n).toFinset.Powerset, f i.val.Prod :=
  by
  rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map, Finset.sum_eq_multiset_sum]

theorem sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a := by
  let S := { s ∈ Finset.range (n + 1) | s ∣ n ∧ ∃ x, s = x ^ 2 }
  have hSne : S.nonempty := by
    use 1
    have h1 : 0 < n ∧ ∃ x : ℕ, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simpa [S]
  let s := Finset.max' S hSne
  have hs : s ∈ S := Finset.max'_mem S hSne
  simp only [Finset.sep_def, S, Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨hsn1, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs
  rw [hsa] at hn
  obtain ⟨hlts, hlta⟩ := canonically_ordered_comm_semiring.mul_pos.mp hn
  rw [hsb] at hsa hn hlts
  refine' ⟨a, b, hlta, (pow_pos_iff zero_lt_two).mp hlts, hsa.symm, _⟩
  rintro x ⟨y, hy⟩
  rw [Nat.is_unit_iff]
  by_contra hx
  refine' lt_le_antisymm _ (Finset.le_max' S ((b * x) ^ 2) _)
  · simp_rw [S, hsa, Finset.sep_def, Finset.mem_filter, Finset.mem_range]
    refine' ⟨lt_succ_iff.mpr (le_of_dvd hn _), _, ⟨b * x, rfl⟩⟩ <;> use y <;> rw [hy] <;> ring
    
  · convert
      lt_mul_of_one_lt_right hlts
        (one_lt_pow 2 x zero_lt_two
          (one_lt_iff_ne_zero_and_ne_one.mpr
            ⟨fun h => by
              simp_all , hx⟩))
    rw [mul_powₓ]
    

theorem sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) : ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine' ⟨a₁.pred, b₁.pred, _, _⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

theorem sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ Squarefree a := by
  cases n
  · exact
      ⟨1, 0, by
        simp , squarefree_one⟩
    
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    exact ⟨a, b, h₁, h₂⟩
    

theorem squarefree_iff_prime_sq_not_dvd (n : ℕ) : Squarefree n ↔ ∀ x : ℕ, x.Prime → ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨2, (irreducible_iff_nat_prime _).2 prime_two⟩

/-- `squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `squarefree.of_mul_left` and
`squarefree.of_mul_right` above for auxiliary lemmas. -/
theorem squarefree_mul {m n : ℕ} (hmn : m.Coprime n) : Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp only [squarefree_iff_prime_squarefree, ← sq, ← forall_and_distrib]
  refine' ball_congr fun p hp => _
  simp only [hmn.is_prime_pow_dvd_mul (hp.is_prime_pow.pow two_ne_zero), not_or_distrib]

end Nat

/-! ### Square-free prover -/


open NormNum

namespace Tactic

namespace NormNum

/-- A predicate representing partial progress in a proof of `squarefree`. -/
def SquarefreeHelper (n k : ℕ) : Prop :=
  0 < k → (∀ m, Nat.Prime m → m ∣ bit1 n → bit1 k ≤ m) → Squarefree (bit1 n)

theorem squarefree_bit10 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit0 (bit1 n)) := by
  refine' @Nat.min_sq_fac_prop_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (@two_ne_zero ℕ _ _)]
    exact Nat.not_two_dvd_bit1 _
    
  · rw [bit0_eq_two_mul,
      Nat.mul_div_rightₓ _
        (by
          decide : 0 < 2)]
    refine'
      h
        (by
          decide)
        fun p pp dp => Nat.succ_le_of_ltₓ (lt_of_le_of_neₓ pp.two_le _)
    rintro rfl
    exact Nat.not_two_dvd_bit1 _ dp
    

theorem squarefree_bit1 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit1 n) := by
  refine'
    h
      (by
        decide)
      fun p pp dp => Nat.succ_le_of_ltₓ (lt_of_le_of_neₓ pp.two_le _)
  rintro rfl
  exact Nat.not_two_dvd_bit1 _ dp

theorem squarefree_helper_0 {k} (k0 : 0 < k) {p : ℕ} (pp : Nat.Prime p) (h : bit1 k ≤ p) :
    bit1 (k + 1) ≤ p ∨ bit1 k = p := by
  rcases lt_or_eq_of_leₓ h with ((hp : _ + 1 ≤ _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) ≤ _ at hp
    rw [bit1, bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_neₓ hp _)
    rintro rfl
    exact
      Nat.not_prime_mul
        (by
          decide)
        (lt_add_of_pos_left _ k0) pp
    
  · exact Or.inr hp
    

theorem squarefree_helper_1 (n k k' : ℕ) (e : k + 1 = k') (hk : Nat.Prime (bit1 k) → ¬bit1 k ∣ bit1 n)
    (H : SquarefreeHelper n k') : SquarefreeHelper n k := fun k0 ih => by
  subst e
  refine' H (Nat.succ_posₓ _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp
  cases hk pp dp

theorem squarefree_helper_2 (n k k' c : ℕ) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : SquarefreeHelper n k') : SquarefreeHelper n k := by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gtₓ c0)
  intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zeroₓ]

theorem squarefree_helper_3 (n n' k k' c : ℕ) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
    (hc : bit1 n' % bit1 k = c) (c0 : 0 < c) (H : SquarefreeHelper n' k') : SquarefreeHelper n k := fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_leₓ _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by
    rw [← hn', Nat.mul_div_cancelₓ _ k0']
  have k2 : 2 ≤ bit1 k := Nat.succ_le_succₓ (bit0_pos k0)
  have pk : (bit1 k).Prime := by
    refine' Nat.prime_def_min_fac.2 ⟨k2, le_antisymmₓ (Nat.min_fac_le k0') _⟩
    exact ih _ (Nat.min_fac_prime (ne_of_gtₓ k2)) (dvd_trans (Nat.min_fac_dvd _) dk)
  have dkk' : ¬bit1 k ∣ bit1 n' := by
    rw [Nat.dvd_iff_mod_eq_zeroₓ, hc]
    exact ne_of_gtₓ c0
  have dkk : ¬bit1 k * bit1 k ∣ bit1 n := by
    rwa [← Nat.dvd_div_iff dk, this]
  refine' @Nat.min_sq_fac_prop_div _ _ pk dk dkk none _
  rw [this]
  refine' H (Nat.succ_posₓ _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp <| dvd_trans dp dn')).resolve_right fun e => _
  subst e
  contradiction

theorem squarefree_helper_4 (n k k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') : SquarefreeHelper n k := by
  cases' Nat.eq_zero_or_posₓ n with h h
  · subst n
    exact fun _ _ => squarefree_one
    
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gtₓ m2)
  have :=
    (ih p pp (dvd_trans hp md)).trans
      (le_transₓ
        (Nat.le_of_dvdₓ
          (lt_of_lt_of_leₓ
            (by
              decide)
            m2)
          hp)
        hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_lt hd this

theorem not_squarefree_mul (a aa b n : ℕ) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a) : ¬Squarefree n := by
  rw [← hb, ← ha]
  exact fun H => ne_of_gtₓ h₁ (Nat.is_unit_iff.1 <| H _ ⟨_, rfl⟩)

/-- Given `e` a natural numeral and `a : nat` with `a^2 ∣ n`, return `⊢ ¬ squarefree e`. -/
unsafe def prove_non_squarefree (e : expr) (n a : ℕ) : tactic expr := do
  let ea := reflect a
  let eaa := reflect (a * a)
  let c ← mk_instance_cache (quote.1 Nat)
  let (c, p₁) ← prove_lt_nat c (quote.1 1) ea
  let b := n / (a * a)
  let eb := reflect b
  let (c, eaa, pa) ← prove_mul_nat c ea ea
  let (c, e', pb) ← prove_mul_nat c eaa eb
  guardₓ (expr.alpha_eqv e' e)
  return <| (quote.1 @not_squarefree_mul).mk_app [ea, eaa, eb, e, pa, pb, p₁]

/-- Given `en`,`en1 := bit1 en`, `n1` the value of `en1`, `ek`,
  returns `⊢ squarefree_helper en ek`. -/
unsafe def prove_squarefree_aux : ∀ ic : instance_cache en en1 : expr n1 : ℕ ek : expr k : ℕ, tactic expr
  | ic, en, en1, n1, ek, k => do
    let k1 := bit1 k
    let ek1 := (quote.1 (bit1 : ℕ → ℕ)).mk_app [ek]
    if n1 < k1 * k1 then do
        let (ic, ek', p₁) ← prove_mul_nat ic ek1 ek1
        let (ic, p₂) ← prove_lt_nat ic en1 ek'
        pure <| (quote.1 squarefree_helper_4).mk_app [en, ek, ek', p₁, p₂]
      else do
        let c := n1 % k1
        let k' := k + 1
        let ek' := reflect k'
        let (ic, p₁) ← prove_succ ic ek ek'
        if c = 0 then do
            let n1' := n1 / k1
            let n' := n1' / 2
            let en' := reflect n'
            let en1' := (quote.1 (bit1 : ℕ → ℕ)).mk_app [en']
            let (ic, _, pn') ← prove_mul_nat ic en1' ek1
            let c := n1' % k1
            guardₓ (c ≠ 0)
            let (ic, ec, pc) ← prove_div_mod ic en1' ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en' en1' n1' ek' k'
            pure <| (quote.1 squarefree_helper_3).mk_app [en, en', ek, ek', ec, p₁, pn', pc, p₀, p₂]
          else do
            let (ic, ec, pc) ← prove_div_mod ic en1 ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en en1 n1 ek' k'
            pure <| (quote.1 squarefree_helper_2).mk_app [en, ek, ek', ec, p₁, pc, p₀, p₂]

/-- Given `n > 0` a squarefree natural numeral, returns `⊢ squarefree n`. -/
unsafe def prove_squarefree (en : expr) (n : ℕ) : tactic expr :=
  match match_numeral en with
  | match_numeral_result.one => pure (quote.1 (@squarefree_one ℕ _))
  | match_numeral_result.bit0 en1 =>
    match match_numeral en1 with
    | match_numeral_result.one => pure (quote.1 Nat.squarefree_two)
    | match_numeral_result.bit1 en => do
      let ic ← mk_instance_cache (quote.1 ℕ)
      let p ← prove_squarefree_aux ic en en1 (n / 2) (quote.1 (1 : ℕ)) 1
      pure <| (quote.1 squarefree_bit10).mk_app [en, p]
    | _ => failed
  | match_numeral_result.bit1 en' => do
    let ic ← mk_instance_cache (quote.1 ℕ)
    let p ← prove_squarefree_aux ic en' en n (quote.1 (1 : ℕ)) 1
    pure <| (quote.1 squarefree_bit1).mk_app [en', p]
  | _ => failed

/-- Evaluates the `prime` and `min_fac` functions. -/
@[norm_num]
unsafe def eval_squarefree : expr → tactic (expr × expr)
  | quote.1 (Squarefree (%%ₓe : ℕ)) => do
    let n ← e.toNat
    match n with
      | 0 => false_intro (quote.1 (@not_squarefree_zero ℕ _ _))
      | 1 => true_intro (quote.1 (@squarefree_one ℕ _))
      | _ =>
        match n with
        | some d => prove_non_squarefree e n d >>= false_intro
        | none => prove_squarefree e n >>= true_intro
  | _ => failed

end NormNum

end Tactic

