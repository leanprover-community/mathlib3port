import Mathbin.Analysis.SpecificLimits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `one_sub`, `add` and `unit_of_nearby` state, in varying forms, that perturbations
of a unit are units.  The latter two are not stated in their optimal form; more precise versions
would use the spectral radius.

The first main result is `is_open`:  the group of units of a complete normed ring is an open subset
of the ring.

The function `inverse` (defined in `algebra.ring`), for a ring `R`, sends `a : R` to `a⁻¹` if `a` is
a unit and 0 if not.  The other major results of this file (notably `inverse_add`,
`inverse_add_norm` and `inverse_add_norm_diff_nth_order`) cover the asymptotic properties of
`inverse (x + t)` as `t → 0`.

-/


noncomputable theory

open_locale TopologicalSpace

variable{R : Type _}[NormedRing R][CompleteSpace R]

namespace Units

/-- In a complete normed ring, a perturbation of `1` by an element `t` of distance less than `1`
from `1` is a unit.  Here we construct its `units` structure.  -/
@[simps coe]
def one_sub (t : R) (h : ∥t∥ < 1) : Units R :=
  { val := 1 - t, inv := ∑'n : ℕ, t ^ n, val_inv := mul_neg_geom_series t h, inv_val := geom_series_mul_neg t h }

/-- In a complete normed ring, a perturbation of a unit `x` by an element `t` of distance less than
`∥x⁻¹∥⁻¹` from `x` is a unit.  Here we construct its `units` structure. -/
@[simps coe]
def add (x : Units R) (t : R) (h : ∥t∥ < ∥(«expr↑ » (x⁻¹) : R)∥⁻¹) : Units R :=
  Units.copy
    (x*Units.oneSub (-«expr↑ » (x⁻¹)*t)
        (by 
          nontriviality R using zero_lt_one 
          have hpos : 0 < ∥(«expr↑ » (x⁻¹) : R)∥ := Units.norm_pos (x⁻¹)
          calc ∥-«expr↑ » (x⁻¹)*t∥ = ∥«expr↑ » (x⁻¹)*t∥ :=
            by 
              rw [norm_neg]_ ≤ ∥(«expr↑ » (x⁻¹) : R)∥*∥t∥ :=
            norm_mul_le («expr↑ » (x⁻¹)) _ _ < ∥(«expr↑ » (x⁻¹) : R)∥*∥(«expr↑ » (x⁻¹) : R)∥⁻¹ :=
            by 
              nlinarith only [h, hpos]_ = 1 :=
            mul_inv_cancel (ne_of_gtₓ hpos)))
    (x+t)
    (by 
      simp [mul_addₓ])
    _ rfl

/-- In a complete normed ring, an element `y` of distance less than `∥x⁻¹∥⁻¹` from `x` is a unit.
Here we construct its `units` structure. -/
@[simps coe]
def unit_of_nearby (x : Units R) (y : R) (h : ∥y - x∥ < ∥(«expr↑ » (x⁻¹) : R)∥⁻¹) : Units R :=
  Units.copy (x.add (y - x : R) h) y
    (by 
      simp )
    _ rfl

/-- The group of units of a complete normed ring is an open subset of the ring. -/
protected theorem IsOpen : IsOpen { x : R | IsUnit x } :=
  by 
    nontriviality R 
    apply metric.is_open_iff.mpr 
    rintro x' ⟨x, rfl⟩
    refine' ⟨∥(«expr↑ » (x⁻¹) : R)∥⁻¹, inv_pos.mpr (Units.norm_pos (x⁻¹)), _⟩
    intro y hy 
    rw [Metric.mem_ball, dist_eq_norm] at hy 
    exact (x.unit_of_nearby y hy).IsUnit

protected theorem nhds (x : Units R) : { x : R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.is_open x.is_unit

end Units

namespace NormedRing

open_locale Classical BigOperators

open Asymptotics Filter Metric Finset Ringₓ

theorem inverse_one_sub (t : R) (h : ∥t∥ < 1) : inverse (1 - t) = «expr↑ » (Units.oneSub t h⁻¹) :=
  by 
    rw [←inverse_unit (Units.oneSub t h), Units.coe_one_sub]

/-- The formula `inverse (x + t) = inverse (1 + x⁻¹ * t) * x⁻¹` holds for `t` sufficiently small. -/
theorem inverse_add (x : Units R) : ∀ᶠt in 𝓝 0, inverse ((x : R)+t) = inverse (1+«expr↑ » (x⁻¹)*t)*«expr↑ » (x⁻¹) :=
  by 
    nontriviality R 
    rw [eventually_iff, Metric.mem_nhds_iff]
    have hinv : 0 < ∥(«expr↑ » (x⁻¹) : R)∥⁻¹
    ·
      cancelDenoms 
    use ∥(«expr↑ » (x⁻¹) : R)∥⁻¹, hinv 
    intro t ht 
    simp only [mem_ball, dist_zero_right] at ht 
    have ht' : ∥(-«expr↑ » (x⁻¹))*t∥ < 1
    ·
      refine' lt_of_le_of_ltₓ (norm_mul_le _ _) _ 
      rw [norm_neg]
      refine' lt_of_lt_of_leₓ (mul_lt_mul_of_pos_left ht x⁻¹.norm_pos) _ 
      cancelDenoms 
    have hright := inverse_one_sub ((-«expr↑ » (x⁻¹))*t) ht' 
    have hleft := inverse_unit (x.add t ht)
    simp only [←neg_mul_eq_neg_mul, sub_neg_eq_add] at hright 
    simp only [Units.coe_add] at hleft 
    simp [hleft, hright, Units.add]

theorem inverse_one_sub_nth_order (n : ℕ) :
  ∀ᶠt in 𝓝 0, inverse ((1 : R) - t) = (∑i in range n, t ^ i)+(t ^ n)*inverse (1 - t) :=
  by 
    simp only [eventually_iff, Metric.mem_nhds_iff]
    use 1,
      by 
        normNum 
    intro t ht 
    simp only [mem_ball, dist_zero_right] at ht 
    simp only [inverse_one_sub t ht, Set.mem_set_of_eq]
    have h : 1 = (((range n).Sum fun i => t ^ i)*Units.oneSub t ht)+t ^ n
    ·
      simp only [Units.coe_one_sub]
      rw [←geomSum, geom_sum_mul_neg]
      simp 
    rw [←one_mulₓ («expr↑ » (Units.oneSub t ht⁻¹)), h, add_mulₓ]
    congr
    ·
      rw [mul_assocₓ, (Units.oneSub t ht).mul_inv]
      simp 
    ·
      simp only [Units.coe_one_sub]
      rw [←add_mulₓ, ←geomSum, geom_sum_mul_neg]
      simp 

/-- The formula
`inverse (x + t) = (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹ + (- x⁻¹ * t) ^ n * inverse (x + t)`
holds for `t` sufficiently small. -/
theorem inverse_add_nth_order (x : Units R) (n : ℕ) :
  ∀ᶠt in 𝓝 0,
    inverse ((x : R)+t) =
      ((∑i in range n, ((-«expr↑ » (x⁻¹))*t) ^ i)*«expr↑ » (x⁻¹))+(((-«expr↑ » (x⁻¹))*t) ^ n)*inverse (x+t) :=
  by 
    refine' (inverse_add x).mp _ 
    have hzero : tendsto (fun t : R => (-«expr↑ » (x⁻¹))*t) (𝓝 0) (𝓝 0)
    ·
      convert ((mul_left_continuous (-(«expr↑ » (x⁻¹) : R))).Tendsto 0).comp tendsto_id 
      simp 
    refine' (hzero.eventually (inverse_one_sub_nth_order n)).mp (eventually_of_forall _)
    simp only [neg_mul_eq_neg_mul_symm, sub_neg_eq_add]
    intro t h1 h2 
    have h := congr_argₓ (fun a : R => a*«expr↑ » (x⁻¹)) h1 
    dsimp  at h 
    convert h 
    rw [add_mulₓ, mul_assocₓ]
    simp [h2.symm]

theorem inverse_one_sub_norm : is_O (fun t => inverse ((1 : R) - t)) (fun t => (1 : ℝ)) (𝓝 (0 : R)) :=
  by 
    simp only [is_O, is_O_with, eventually_iff, Metric.mem_nhds_iff]
    refine'
      ⟨∥(1 : R)∥+1, (2 : ℝ)⁻¹,
        by 
          normNum,
        _⟩
    intro t ht 
    simp only [ball, dist_zero_right, Set.mem_set_of_eq] at ht 
    have ht' : ∥t∥ < 1
    ·
      have  : (2 : ℝ)⁻¹ < 1 :=
        by 
          cancelDenoms 
      linarith 
    simp only [inverse_one_sub t ht', norm_one, mul_oneₓ, Set.mem_set_of_eq]
    change ∥∑'n : ℕ, t ^ n∥ ≤ _ 
    have  := NormedRing.tsum_geometric_of_norm_lt_1 t ht' 
    have  : (1 - ∥t∥)⁻¹ ≤ 2
    ·
      rw [←inv_inv₀ (2 : ℝ)]
      refine'
        inv_le_inv_of_le
          (by 
            normNum)
          _ 
      have  : ((2 : ℝ)⁻¹+(2 : ℝ)⁻¹) = 1 :=
        by 
          ring 
      linarith 
    linarith

/-- The function `λ t, inverse (x + t)` is O(1) as `t → 0`. -/
theorem inverse_add_norm (x : Units R) : is_O (fun t => inverse («expr↑ » x+t)) (fun t => (1 : ℝ)) (𝓝 (0 : R)) :=
  by 
    nontriviality R 
    simp only [is_O_iff, norm_one, mul_oneₓ]
    cases' is_O_iff.mp (@inverse_one_sub_norm R _ _) with C hC 
    use C*∥((x⁻¹ : Units R) : R)∥
    have hzero : tendsto (fun t => (-(«expr↑ » (x⁻¹) : R))*t) (𝓝 0) (𝓝 0)
    ·
      convert ((mul_left_continuous (-«expr↑ » (x⁻¹) : R)).Tendsto 0).comp tendsto_id 
      simp 
    refine' (inverse_add x).mp ((hzero.eventually hC).mp (eventually_of_forall _))
    intro t bound iden 
    rw [iden]
    simp  at bound 
    have hmul := norm_mul_le (inverse (1+«expr↑ » (x⁻¹)*t)) («expr↑ » (x⁻¹))
    nlinarith [norm_nonneg («expr↑ » (x⁻¹) : R)]

/-- The function
`λ t, inverse (x + t) - (∑ i in range n, (- x⁻¹ * t) ^ i) * x⁻¹`
is `O(t ^ n)` as `t → 0`. -/
theorem inverse_add_norm_diff_nth_order (x : Units R) (n : ℕ) :
  is_O (fun t : R => inverse («expr↑ » x+t) - (∑i in range n, ((-«expr↑ » (x⁻¹))*t) ^ i)*«expr↑ » (x⁻¹))
    (fun t => ∥t∥ ^ n) (𝓝 (0 : R)) :=
  by 
    byCases' h : n = 0
    ·
      simpa [h] using inverse_add_norm x 
    have hn : 0 < n := Nat.pos_of_ne_zeroₓ h 
    simp [is_O_iff]
    cases' is_O_iff.mp (inverse_add_norm x) with C hC 
    use (C*∥(1 : ℝ)∥)*∥(«expr↑ » (x⁻¹) : R)∥ ^ n 
    have h :
      eventually_eq (𝓝 (0 : R))
        (fun t => inverse («expr↑ » x+t) - (∑i in range n, ((-«expr↑ » (x⁻¹))*t) ^ i)*«expr↑ » (x⁻¹))
        fun t => (((-«expr↑ » (x⁻¹))*t) ^ n)*inverse (x+t)
    ·
      refine' (inverse_add_nth_order x n).mp (eventually_of_forall _)
      intro t ht 
      convert congr_argₓ (fun a => a - (range n).Sum (pow ((-«expr↑ » (x⁻¹))*t))*«expr↑ » (x⁻¹)) ht 
      simp 
    refine' h.mp (hC.mp (eventually_of_forall _))
    intro t _ hLHS 
    simp only [neg_mul_eq_neg_mul_symm] at hLHS 
    rw [hLHS]
    refine' le_transₓ (norm_mul_le _ _) _ 
    have h' : ∥(-«expr↑ » (x⁻¹)*t) ^ n∥ ≤ (∥(«expr↑ » (x⁻¹) : R)∥ ^ n)*∥t∥ ^ n
    ·
      calc ∥(-«expr↑ » (x⁻¹)*t) ^ n∥ ≤ ∥-«expr↑ » (x⁻¹)*t∥ ^ n := norm_pow_le' _ hn _ = ∥«expr↑ » (x⁻¹)*t∥ ^ n :=
        by 
          rw [norm_neg]_ ≤ (∥(«expr↑ » (x⁻¹) : R)∥*∥t∥) ^ n :=
        _ _ = (∥(«expr↑ » (x⁻¹) : R)∥ ^ n)*∥t∥ ^ n := mul_powₓ _ _ n 
      exact pow_le_pow_of_le_left (norm_nonneg _) (norm_mul_le («expr↑ » (x⁻¹)) t) n 
    have h'' : 0 ≤ (∥(«expr↑ » (x⁻¹) : R)∥ ^ n)*∥t∥ ^ n
    ·
      refine' mul_nonneg _ _ <;> exact pow_nonneg (norm_nonneg _) n 
    nlinarith [norm_nonneg (inverse («expr↑ » x+t))]

/-- The function `λ t, inverse (x + t) - x⁻¹` is `O(t)` as `t → 0`. -/
theorem inverse_add_norm_diff_first_order (x : Units R) :
  is_O (fun t => inverse («expr↑ » x+t) - «expr↑ » (x⁻¹)) (fun t => ∥t∥) (𝓝 (0 : R)) :=
  by 
    convert inverse_add_norm_diff_nth_order x 1 <;> simp 

/-- The function
`λ t, inverse (x + t) - x⁻¹ + x⁻¹ * t * x⁻¹`
is `O(t ^ 2)` as `t → 0`. -/
theorem inverse_add_norm_diff_second_order (x : Units R) :
  is_O (fun t => (inverse («expr↑ » x+t) - «expr↑ » (x⁻¹))+(«expr↑ » (x⁻¹)*t)*«expr↑ » (x⁻¹)) (fun t => ∥t∥ ^ 2)
    (𝓝 (0 : R)) :=
  by 
    convert inverse_add_norm_diff_nth_order x 2 
    ext t 
    simp only [range_succ, range_one, sum_insert, mem_singleton, sum_singleton, not_false_iff, one_ne_zero, pow_zeroₓ,
      add_mulₓ, pow_oneₓ, one_mulₓ, neg_mul_eq_neg_mul_symm, sub_add_eq_sub_sub_swap, sub_neg_eq_add]

/-- The function `inverse` is continuous at each unit of `R`. -/
theorem inverse_continuous_at (x : Units R) : ContinuousAt inverse (x : R) :=
  by 
    have h_is_o : is_o (fun t : R => ∥inverse («expr↑ » x+t) - «expr↑ » (x⁻¹)∥) (fun t : R => (1 : ℝ)) (𝓝 0)
    ·
      refine' is_o_norm_left.mpr ((inverse_add_norm_diff_first_order x).trans_is_o _)
      exact is_o_norm_left.mpr (is_o_id_const one_ne_zero)
    have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0)
    ·
      refine' tendsto_zero_iff_norm_tendsto_zero.mpr _ 
      exact tendsto_iff_norm_tendsto_zero.mp tendsto_id 
    simp only [ContinuousAt]
    rw [tendsto_iff_norm_tendsto_zero, inverse_unit]
    convert h_is_o.tendsto_0.comp h_lim 
    ext 
    simp 

end NormedRing

namespace Units

open Opposite Filter NormedRing

/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open map. -/
theorem is_open_map_coe : IsOpenMap (coeₓ : Units R → R) :=
  by 
    rw [is_open_map_iff_nhds_le]
    intro x s 
    rw [mem_map, mem_nhds_induced]
    rintro ⟨t, ht, hts⟩
    obtain ⟨u, hu, v, hv, huvt⟩ :
      ∃ u : Set R, u ∈ 𝓝 («expr↑ » x) ∧ ∃ v : Set («expr ᵒᵖ» R), v ∈ 𝓝 (Opposite.op («expr↑ » (x⁻¹))) ∧ u.prod v ⊆ t
    ·
      simpa [embedProduct, mem_nhds_prod_iff] using ht 
    have  : u ∩ (op ∘ Ring.inverse) ⁻¹' v ∩ Set.Range (coeₓ : Units R → R) ∈ 𝓝 («expr↑ » x)
    ·
      refine' inter_mem (inter_mem hu _) (Units.nhds x)
      refine' (continuous_op.continuous_at.comp (inverse_continuous_at x)).preimage_mem_nhds _ 
      simpa using hv 
    refine' mem_of_superset this _ 
    rintro _ ⟨⟨huy, hvy⟩, ⟨y, rfl⟩⟩
    have  : embedProduct R y ∈ u.prod v :=
      ⟨huy,
        by 
          simpa using hvy⟩
    simpa using hts (huvt this)

/-- In a normed ring, the coercion from `units R` (equipped with the induced topology from the
embedding in `R × R`) to `R` is an open embedding. -/
theorem open_embedding_coe : OpenEmbedding (coeₓ : Units R → R) :=
  open_embedding_of_continuous_injective_open continuous_coe ext is_open_map_coe

end Units

