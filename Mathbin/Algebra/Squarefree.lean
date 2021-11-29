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


variable{R : Type _}

/-- An element of a monoid is squarefree if the only squares that
  divide it are the squares of units. -/
def Squarefree [Monoidₓ R] (r : R) : Prop :=
  ∀ (x : R), (x*x) ∣ r → IsUnit x

@[simp]
theorem IsUnit.squarefree [CommMonoidₓ R] {x : R} (h : IsUnit x) : Squarefree x :=
  fun y hdvd => is_unit_of_mul_is_unit_left (is_unit_of_dvd_unit hdvd h)

@[simp]
theorem squarefree_one [CommMonoidₓ R] : Squarefree (1 : R) :=
  is_unit_one.Squarefree

@[simp]
theorem not_squarefree_zero [MonoidWithZeroₓ R] [Nontrivial R] : ¬Squarefree (0 : R) :=
  by 
    erw [not_forall]
    exact
      ⟨0,
        by 
          simp ⟩

@[simp]
theorem Irreducible.squarefree [CommMonoidₓ R] {x : R} (h : Irreducible x) : Squarefree x :=
  by 
    rintro y ⟨z, hz⟩
    rw [mul_assocₓ] at hz 
    rcases h.is_unit_or_is_unit hz with (hu | hu)
    ·
      exact hu
    ·
      apply is_unit_of_mul_is_unit_left hu

@[simp]
theorem Prime.squarefree [CommCancelMonoidWithZero R] {x : R} (h : Prime x) : Squarefree x :=
  h.irreducible.squarefree

theorem squarefree_of_dvd_of_squarefree [CommMonoidₓ R] {x y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x :=
  fun a h => hsq _ (h.trans hdvd)

namespace multiplicity

variable[CommMonoidₓ R][DecidableRel (HasDvd.Dvd : R → R → Prop)]

theorem squarefree_iff_multiplicity_le_one (r : R) : Squarefree r ↔ ∀ (x : R), multiplicity x r ≤ 1 ∨ IsUnit x :=
  by 
    refine' forall_congrₓ fun a => _ 
    rw [←sq, pow_dvd_iff_le_multiplicity, or_iff_not_imp_left, not_leₓ, imp_congr]
    swap
    ·
      rfl 
    convert Enat.add_one_le_iff_lt (Enat.coe_ne_top 1)
    normCast

end multiplicity

namespace UniqueFactorizationMonoid

variable[CommCancelMonoidWithZero R][Nontrivial R][UniqueFactorizationMonoid R]

variable[NormalizationMonoid R]

-- error in Algebra.Squarefree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem squarefree_iff_nodup_normalized_factors
[decidable_eq R]
{x : R}
(x0 : «expr ≠ »(x, 0)) : «expr ↔ »(squarefree x, multiset.nodup (normalized_factors x)) :=
begin
  have [ident drel] [":", expr decidable_rel (has_dvd.dvd : R → R → exprProp())] [],
  { classical,
    apply_instance },
  haveI [] [] [":=", expr drel],
  rw ["[", expr multiplicity.squarefree_iff_multiplicity_le_one, ",", expr multiset.nodup_iff_count_le_one, "]"] [],
  split; intros [ident h, ident a],
  { by_cases [expr hmem, ":", expr «expr ∈ »(a, normalized_factors x)],
    { have [ident ha] [] [":=", expr irreducible_of_normalized_factor _ hmem],
      rcases [expr h a, "with", ident h, "|", ident h],
      { rw ["<-", expr normalize_normalized_factor _ hmem] [],
        rw ["[", expr multiplicity_eq_count_normalized_factors ha x0, "]"] ["at", ident h],
        assumption_mod_cast },
      { have [] [] [":=", expr ha.1],
        contradiction } },
    { simp [] [] [] ["[", expr multiset.count_eq_zero_of_not_mem hmem, "]"] [] [] } },
  { rw [expr or_iff_not_imp_right] [],
    intro [ident hu],
    by_cases [expr h0, ":", expr «expr = »(a, 0)],
    { simp [] [] [] ["[", expr h0, ",", expr x0, "]"] [] [] },
    rcases [expr wf_dvd_monoid.exists_irreducible_factor hu h0, "with", "⟨", ident b, ",", ident hib, ",", ident hdvd, "⟩"],
    apply [expr le_trans (multiplicity.multiplicity_le_multiplicity_of_dvd_left hdvd)],
    rw ["[", expr multiplicity_eq_count_normalized_factors hib x0, "]"] [],
    specialize [expr h (normalize b)],
    assumption_mod_cast }
end

theorem dvd_pow_iff_dvd_of_squarefree {x y : R} {n : ℕ} (hsq : Squarefree x) (h0 : n ≠ 0) : x ∣ (y^n) ↔ x ∣ y :=
  by 
    classical 
    byCases' hx : x = 0
    ·
      simp [hx, pow_eq_zero_iff (Nat.pos_of_ne_zeroₓ h0)]
    byCases' hy : y = 0
    ·
      simp [hy, zero_pow (Nat.pos_of_ne_zeroₓ h0)]
    refine' ⟨fun h => _, fun h => h.pow h0⟩
    rw [dvd_iff_normalized_factors_le_normalized_factors hx (pow_ne_zero n hy), normalized_factors_pow,
      ((squarefree_iff_nodup_normalized_factors hx).1 hsq).le_nsmul_iff_le h0] at h 
    rwa [dvd_iff_normalized_factors_le_normalized_factors hx hy]

end UniqueFactorizationMonoid

namespace Nat

theorem squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) : Squarefree n ↔ n.factors.nodup :=
  by 
    rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalized_factors h0, Nat.factors_eq]
    simp 

instance  : DecidablePred (Squarefree : ℕ → Prop)
| 0 => is_false not_squarefree_zero
| n+1 => decidableOfIff _ (squarefree_iff_nodup_factors (Nat.succ_ne_zero n)).symm

open UniqueFactorizationMonoid

-- error in Algebra.Squarefree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem divisors_filter_squarefree
{n : exprℕ()}
(h0 : «expr ≠ »(n, 0)) : «expr = »((n.divisors.filter squarefree).val, (unique_factorization_monoid.normalized_factors n).to_finset.powerset.val.map (λ
  x, x.val.prod)) :=
begin
  rw [expr multiset.nodup_ext (finset.nodup _) (multiset.nodup_map_on _ (finset.nodup _))] [],
  { intro [ident a],
    simp [] [] ["only"] ["[", expr multiset.mem_filter, ",", expr id.def, ",", expr multiset.mem_map, ",", expr finset.filter_val, ",", "<-", expr finset.mem_def, ",", expr mem_divisors, "]"] [] [],
    split,
    { rintro ["⟨", "⟨", ident an, ",", ident h0, "⟩", ",", ident hsq, "⟩"],
      use [expr (unique_factorization_monoid.normalized_factors a).to_finset],
      simp [] [] ["only"] ["[", expr id.def, ",", expr finset.mem_powerset, "]"] [] [],
      rcases [expr an, "with", "⟨", ident b, ",", ident rfl, "⟩"],
      rw [expr mul_ne_zero_iff] ["at", ident h0],
      rw [expr unique_factorization_monoid.squarefree_iff_nodup_normalized_factors h0.1] ["at", ident hsq],
      rw ["[", expr multiset.to_finset_subset, ",", expr multiset.to_finset_val, ",", expr hsq.erase_dup, ",", "<-", expr associated_iff_eq, ",", expr normalized_factors_mul h0.1 h0.2, "]"] [],
      exact [expr ⟨multiset.subset_of_le (multiset.le_add_right _ _), normalized_factors_prod h0.1⟩] },
    { rintro ["⟨", ident s, ",", ident hs, ",", ident rfl, "⟩"],
      rw ["[", expr finset.mem_powerset, ",", "<-", expr finset.val_le_iff, ",", expr multiset.to_finset_val, "]"] ["at", ident hs],
      have [ident hs0] [":", expr «expr ≠ »(s.val.prod, 0)] [],
      { rw ["[", expr ne.def, ",", expr multiset.prod_eq_zero_iff, "]"] [],
        simp [] [] ["only"] ["[", expr exists_prop, ",", expr id.def, ",", expr exists_eq_right, "]"] [] [],
        intro [ident con],
        apply [expr not_irreducible_zero (irreducible_of_normalized_factor 0 (multiset.mem_erase_dup.1 (multiset.mem_of_le hs con)))] },
      rw [expr (normalized_factors_prod h0).symm.dvd_iff_dvd_right] [],
      refine [expr ⟨⟨multiset.prod_dvd_prod (le_trans hs (multiset.erase_dup_le _)), h0⟩, _⟩],
      have [ident h] [] [":=", expr unique_factorization_monoid.factors_unique irreducible_of_normalized_factor (λ
        x
        hx, irreducible_of_normalized_factor x (multiset.mem_of_le (le_trans hs (multiset.erase_dup_le _)) hx)) (normalized_factors_prod hs0)],
      rw ["[", expr associated_eq_eq, ",", expr multiset.rel_eq, "]"] ["at", ident h],
      rw ["[", expr unique_factorization_monoid.squarefree_iff_nodup_normalized_factors hs0, ",", expr h, "]"] [],
      apply [expr s.nodup] } },
  { intros [ident x, ident hx, ident y, ident hy, ident h],
    rw ["[", "<-", expr finset.val_inj, ",", "<-", expr multiset.rel_eq, ",", "<-", expr associated_eq_eq, "]"] [],
    rw ["[", "<-", expr finset.mem_def, ",", expr finset.mem_powerset, "]"] ["at", ident hx, ident hy],
    apply [expr unique_factorization_monoid.factors_unique _ _ (associated_iff_eq.2 h)],
    { intros [ident z, ident hz],
      apply [expr irreducible_of_normalized_factor z],
      rw ["<-", expr multiset.mem_to_finset] [],
      apply [expr hx hz] },
    { intros [ident z, ident hz],
      apply [expr irreducible_of_normalized_factor z],
      rw ["<-", expr multiset.mem_to_finset] [],
      apply [expr hy hz] } }
end

open_locale BigOperators

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type _} [AddCommMonoidₓ α] {f : ℕ → α} :
  (∑i in n.divisors.filter Squarefree, f i) =
    ∑i in (UniqueFactorizationMonoid.normalizedFactors n).toFinset.Powerset, f i.val.prod :=
  by 
    rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map, Finset.sum_eq_multiset_sum]

-- error in Algebra.Squarefree: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sq_mul_squarefree_of_pos
{n : exprℕ()}
(hn : «expr < »(0, n)) : «expr∃ , »((a
  b : exprℕ()), «expr ∧ »(«expr < »(0, a), «expr ∧ »(«expr < »(0, b), «expr ∧ »(«expr = »(«expr * »(«expr ^ »(b, 2), a), n), squarefree a)))) :=
begin
  let [ident S] [] [":=", expr {s ∈ finset.range «expr + »(n, 1) | «expr ∧ »(«expr ∣ »(s, n), «expr∃ , »((x), «expr = »(s, «expr ^ »(x, 2))))}],
  have [ident hSne] [":", expr S.nonempty] [],
  { use [expr 1],
    have [ident h1] [":", expr «expr ∧ »(«expr < »(0, n), «expr∃ , »((x : exprℕ()), «expr = »(1, «expr ^ »(x, 2))))] [":=", expr ⟨hn, ⟨1, (one_pow 2).symm⟩⟩],
    simpa [] [] [] ["[", expr S, "]"] [] [] },
  let [ident s] [] [":=", expr finset.max' S hSne],
  have [ident hs] [":", expr «expr ∈ »(s, S)] [":=", expr finset.max'_mem S hSne],
  simp [] [] ["only"] ["[", expr finset.sep_def, ",", expr S, ",", expr finset.mem_filter, ",", expr finset.mem_range, "]"] [] ["at", ident hs],
  obtain ["⟨", ident hsn1, ",", "⟨", ident a, ",", ident hsa, "⟩", ",", "⟨", ident b, ",", ident hsb, "⟩", "⟩", ":=", expr hs],
  rw [expr hsa] ["at", ident hn],
  obtain ["⟨", ident hlts, ",", ident hlta, "⟩", ":=", expr canonically_ordered_comm_semiring.mul_pos.mp hn],
  rw [expr hsb] ["at", ident hsa, ident hn, ident hlts],
  refine [expr ⟨a, b, hlta, (pow_pos_iff zero_lt_two).mp hlts, hsa.symm, _⟩],
  rintro [ident x, "⟨", ident y, ",", ident hy, "⟩"],
  rw [expr nat.is_unit_iff] [],
  by_contra [ident hx],
  refine [expr lt_le_antisymm _ (finset.le_max' S «expr ^ »(«expr * »(b, x), 2) _)],
  { simp_rw ["[", expr S, ",", expr hsa, ",", expr finset.sep_def, ",", expr finset.mem_filter, ",", expr finset.mem_range, "]"] [],
    refine [expr ⟨lt_succ_iff.mpr (le_of_dvd hn _), _, ⟨«expr * »(b, x), rfl⟩⟩]; use [expr y]; rw [expr hy] []; ring [] },
  { convert [] [expr lt_mul_of_one_lt_right hlts (one_lt_pow 2 x zero_lt_two (one_lt_iff_ne_zero_and_ne_one.mpr ⟨λ
        h, by simp [] [] [] ["*"] [] ["at", "*"], hx⟩))] [],
    rw [expr mul_pow] [] }
end

theorem sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) : ∃ a b : ℕ, (((b+1)^2)*a+1) = n ∧ Squarefree (a+1) :=
  by 
    obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h 
    refine' ⟨a₁.pred, b₁.pred, _, _⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

theorem sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, ((b^2)*a) = n ∧ Squarefree a :=
  by 
    cases n
    ·
      exact
        ⟨1, 0,
          by 
            simp ,
          squarefree_one⟩
    ·
      obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
      exact ⟨a, b, h₁, h₂⟩

end Nat

