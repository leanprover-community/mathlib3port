import Mathbin.RingTheory.UniqueFactorizationDomain
import Mathbin.RingTheory.Int.Basic
import Mathbin.NumberTheory.Divisors

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

@[simp]
theorem Irreducible.squarefree [CommMonoidₓ R] {x : R} (h : Irreducible x) : Squarefree x := by
  rintro y ⟨z, hz⟩
  rw [mul_assocₓ] at hz
  rcases h.is_unit_or_is_unit hz with (hu | hu)
  · exact hu
    
  · apply is_unit_of_mul_is_unit_left hu
    

@[simp]
theorem Prime.squarefree [CancelCommMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.irreducible.squarefree

theorem squarefree_of_dvd_of_squarefree [CommMonoidₓ R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x :=
  fun a h => hsq _ (h.trans hdvd)

namespace multiplicity

variable [CommMonoidₓ R] [DecidableRel (HasDvd.Dvd : R → R → Prop)]

theorem squarefree_iff_multiplicity_le_one (r : R) : Squarefree r ↔ ∀ x : R, multiplicity x r ≤ 1 ∨ IsUnit x := by
  refine' forall_congrₓ fun a => _
  rw [← sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_leₓ, imp_congr]
  swap
  · rfl
    
  convert Enat.add_one_le_iff_lt (Enat.coe_ne_top 1)
  norm_cast

end multiplicity

namespace UniqueFactorizationMonoid

variable [CancelCommMonoidWithZero R] [Nontrivial R] [UniqueFactorizationMonoid R]

variable [NormalizationMonoid R]

theorem squarefree_iff_nodup_normalized_factors [DecidableEq R] {x : R} (x0 : x ≠ 0) :
    Squarefree x ↔ Multiset.Nodup (normalized_factors x) := by
  have drel : DecidableRel (HasDvd.Dvd : R → R → Prop) := by
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

theorem squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) : Squarefree n ↔ n.factors.nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors h0, Nat.factors_eq]
  simp

instance : DecidablePred (Squarefree : ℕ → Prop)
  | 0 => is_false not_squarefree_zero
  | n + 1 => decidableOfIff _ (squarefree_iff_nodup_factors (Nat.succ_ne_zero n)).symm

open UniqueFactorizationMonoid

theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    (n.divisors.filter Squarefree).val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.Powerset.val.map fun x => x.val.prod :=
  by
  rw [Multiset.nodup_ext (Finset.nodup _) (Multiset.nodup_map_on _ (Finset.nodup _))]
  · intro a
    simp only [Multiset.mem_filter, id.def, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def, mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      simp only [id.def, Finset.mem_powerset]
      rcases an with ⟨b, rfl⟩
      rw [mul_ne_zero_iff] at h0
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors h0.1] at hsq
      rw [Multiset.to_finset_subset, Multiset.to_finset_val, hsq.erase_dup, ← associated_iff_eq,
        normalized_factors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), normalized_factors_prod h0.1⟩
      
    · rintro ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset, ← Finset.val_le_iff, Multiset.to_finset_val] at hs
      have hs0 : s.val.prod ≠ 0 := by
        rw [Ne.def, Multiset.prod_eq_zero_iff]
        simp only [exists_prop, id.def, exists_eq_right]
        intro con
        apply
          not_irreducible_zero
            (irreducible_of_normalized_factor 0 (Multiset.mem_erase_dup.1 (Multiset.mem_of_le hs Con)))
      rw [(normalized_factors_prod h0).symm.dvd_iff_dvd_right]
      refine' ⟨⟨Multiset.prod_dvd_prod (le_transₓ hs (Multiset.erase_dup_le _)), h0⟩, _⟩
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx =>
            irreducible_of_normalized_factor x (Multiset.mem_of_le (le_transₓ hs (Multiset.erase_dup_le _)) hx))
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
      
    

open_locale BigOperators

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type _} [AddCommMonoidₓ α] {f : ℕ → α} :
    (∑ i in n.divisors.filter Squarefree, f i) =
      ∑ i in (UniqueFactorizationMonoid.normalizedFactors n).toFinset.Powerset, f i.val.prod :=
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
    

end Nat

