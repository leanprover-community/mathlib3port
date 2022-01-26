import Mathbin.MeasureTheory.Constructions.Prod
import Mathbin.MeasureTheory.Group.Basic

/-!
# Measure theory in the product of groups

In this file we show properties about measure theory in products of topological groups
and properties of iterated integrals in topological groups.

These lemmas show the uniqueness of left invariant measures on locally compact groups, up to
scaling. In this file we follow the proof and refer to the book *Measure Theory* by Paul Halmos.

The idea of the proof is to use the translation invariance of measures to prove `μ(F) = c * μ(E)`
for two sets `E` and `F`, where `c` is a constant that does not depend on `μ`. Let `e` and `f` be
the characteristic functions of `E` and `F`.
Assume that `μ` and `ν` are left-invariant measures. Then the map `(x, y) ↦ (y * x, x⁻¹)`
preserves the measure `μ.prod ν`, which means that
```
  ∫ x, ∫ y, h x y ∂ν ∂μ = ∫ x, ∫ y, h (y * x) x⁻¹ ∂ν ∂μ
```
If we apply this to `h x y := e x * f y⁻¹ / ν ((λ h, h * y⁻¹) ⁻¹' E)`, we can rewrite the RHS to
`μ(F)`, and the LHS to `c * μ(E)`, where `c = c(ν)` does not depend on `μ`.
Applying this to `μ` and to `ν` gives `μ (F) / μ (E) = ν (F) / ν (E)`, which is the uniqueness up to
scalar multiplication.

The proof in [Halmos] seems to contain an omission in §60 Th. A, see
`measure_theory.measure_lintegral_div_measure` and
https://math.stackexchange.com/questions/3974485/does-right-translation-preserve-finiteness-for-a-left-invariant-measure
-/


noncomputable section

open TopologicalSpace

open Set hiding prod_eq

open Function

open_locale Classical Ennreal Pointwise

namespace MeasureTheory

open Measureₓ

variable {G : Type _} [TopologicalSpace G] [MeasurableSpace G] [second_countable_topology G]

variable [BorelSpace G] [Groupₓ G] [TopologicalGroup G]

variable {μ ν : Measureₓ G} [sigma_finite ν] [sigma_finite μ]

/-- This condition is part of the definition of a measurable group in [Halmos, §59].
  There, the map in this lemma is called `S`. -/
@[to_additive map_prod_sum_eq]
theorem map_prod_mul_eq (hν : is_mul_left_invariant ν) :
    map (fun z : G × G => (z.1, z.1 * z.2)) (μ.prod ν) = μ.prod ν := by
  refine' (prod_eq _).symm
  intro s t hs ht
  simp_rw [map_apply (measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht),
    prod_apply ((measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht)), preimage_preimage]
  conv_lhs => congr skip ext rw [mk_preimage_prod_right_fn_eq_if ((· * ·) x), measure_if]
  simp_rw [hν _ ht, lintegral_indicator _ hs, set_lintegral_const, mul_comm]

/-- The function we are mapping along is `SR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_eq_swap]
theorem map_prod_mul_eq_swap (hμ : is_mul_left_invariant μ) :
    map (fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) = ν.prod μ := by
  rw [← prod_swap]
  simp_rw [map_map (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)) measurable_swap]
  exact map_prod_mul_eq hμ

/-- The function we are mapping along is `S⁻¹` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq`. -/
@[to_additive map_prod_neg_add_eq]
theorem map_prod_inv_mul_eq (hν : is_mul_left_invariant ν) :
    map (fun z : G × G => (z.1, z.1⁻¹ * z.2)) (μ.prod ν) = μ.prod ν :=
  (Homeomorph.shearMulRight G).toMeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq.mp <| map_prod_mul_eq hν

/-- The function we are mapping along is `S⁻¹R` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_neg_add_eq_swap]
theorem map_prod_inv_mul_eq_swap (hμ : is_mul_left_invariant μ) :
    map (fun z : G × G => (z.2, z.2⁻¹ * z.1)) (μ.prod ν) = ν.prod μ := by
  rw [← prod_swap]
  simp_rw [map_map (measurable_snd.prod_mk <| measurable_snd.inv.mul measurable_fst) measurable_swap]
  exact map_prod_inv_mul_eq hμ

/-- The function we are mapping along is `S⁻¹RSR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive map_prod_add_neg_eq]
theorem map_prod_mul_inv_eq (hμ : is_mul_left_invariant μ) (hν : is_mul_left_invariant ν) :
    map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod ν) = μ.prod ν := by
  let S := (Homeomorph.shearMulRight G).toMeasurableEquiv
  suffices map ((fun z : G × G => (z.2, z.2⁻¹ * z.1)) ∘ fun z : G × G => (z.2, z.2 * z.1)) (μ.prod ν) = μ.prod ν by
    convert this
    ext1 ⟨x, y⟩
    simp
  simp_rw [←
    map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst))
      (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)),
    map_prod_mul_eq_swap hμ, map_prod_inv_mul_eq_swap hν]

@[to_additive]
theorem quasi_measure_preserving_inv (hμ : is_mul_left_invariant μ) : quasi_measure_preserving (Inv.inv : G → G) μ μ :=
  by
  refine' ⟨measurable_inv, absolutely_continuous.mk fun s hsm hμs => _⟩
  rw [map_apply measurable_inv hsm, inv_preimage]
  have hf : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  suffices map (fun z : G × G => (z.2 * z.1, z.1⁻¹)) (μ.prod μ) (s⁻¹ ×ˢ s⁻¹) = 0 by
    simpa only [map_prod_mul_inv_eq hμ hμ, prod_prod, mul_eq_zero, or_selfₓ] using this
  have hsm' : MeasurableSet (s⁻¹ ×ˢ s⁻¹) := hsm.inv.prod hsm.inv
  simp_rw [map_apply hf hsm', prod_apply_symm (hf hsm'), preimage_preimage, mk_preimage_prod, inv_preimage, Set.inv_inv,
    measure_mono_null (inter_subset_right _ _) hμs, lintegral_zero]

@[to_additive]
theorem measure_inv_null (hμ : is_mul_left_invariant μ) {E : Set G} : μ ((fun x => x⁻¹) ⁻¹' E) = 0 ↔ μ E = 0 := by
  refine' ⟨fun hE => _, (quasi_measure_preserving_inv hμ).preimage_null⟩
  convert (quasi_measure_preserving_inv hμ).preimage_null hE
  exact set.inv_inv.symm

@[to_additive]
theorem measurable_measure_mul_right {E : Set G} (hE : MeasurableSet E) :
    Measurable fun x => μ ((fun y => y * x) ⁻¹' E) := by
  suffices
    Measurable fun y => μ ((fun x => (x, y)) ⁻¹' ((fun z : G × G => ((1 : G), z.1 * z.2)) ⁻¹' ((univ : Set G) ×ˢ E))) by
    convert this
    ext1 x
    congr 1 with y : 1
    simp
  apply measurable_measure_prod_mk_right
  exact measurable_const.prod_mk (measurable_fst.mul measurable_snd) (measurable_set.univ.prod hE)

@[to_additive]
theorem lintegral_lintegral_mul_inv (hμ : is_mul_left_invariant μ) (hν : is_mul_left_invariant ν) (f : G → G → ℝ≥0∞)
    (hf : AeMeasurable (uncurry f) (μ.prod ν)) : (∫⁻ x, ∫⁻ y, f (y * x) x⁻¹ ∂ν ∂μ) = ∫⁻ x, ∫⁻ y, f x y ∂ν ∂μ := by
  have h : Measurable fun z : G × G => (z.2 * z.1, z.1⁻¹) :=
    (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv
  have h2f : AeMeasurable (uncurry fun x y => f (y * x) x⁻¹) (μ.prod ν) := by
    apply hf.comp_measurable' h (map_prod_mul_inv_eq hμ hν).AbsolutelyContinuous
  simp_rw [lintegral_lintegral h2f, lintegral_lintegral hf]
  conv_rhs => rw [← map_prod_mul_inv_eq hμ hν]
  symm
  exact lintegral_map' (hf.mono' (map_prod_mul_inv_eq hμ hν).AbsolutelyContinuous) h

@[to_additive]
theorem measure_mul_right_null (hμ : is_mul_left_invariant μ) {E : Set G} (y : G) :
    μ ((fun x => x * y) ⁻¹' E) = 0 ↔ μ E = 0 :=
  calc
    μ ((fun x => x * y) ⁻¹' E) = 0 ↔ μ (Inv.inv ⁻¹' ((fun x => y⁻¹ * x) ⁻¹' (Inv.inv ⁻¹' E))) = 0 := by
      simp only [preimage_preimage, mul_inv_rev, inv_invₓ]
    _ ↔ μ E = 0 := by
      simp only [measure_inv_null hμ, hμ.measure_preimage_mul]
    

@[to_additive]
theorem measure_mul_right_ne_zero (hμ : is_mul_left_invariant μ) {E : Set G} (h2E : μ E ≠ 0) (y : G) :
    μ ((fun x => x * y) ⁻¹' E) ≠ 0 :=
  (not_iff_not_of_iff (measure_mul_right_null hμ y)).mpr h2E

/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `F` this states that
  `μ F = c * μ E` for a constant `c` that does not depend on `μ`.
  There seems to be a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(Ex⁻¹) = f(x)` holds if we can prove that
  `0 < ν(Ex⁻¹) < ∞`. The first inequality follows from §59, Th. D, but I couldn't find the second
  inequality. For this reason, we use a compact `E` instead of a measurable `E` as in [Halmos], and
  additionally assume that `ν` is a regular measure (we only need that it is finite on compact
  sets). -/
@[to_additive]
theorem measure_lintegral_div_measure [T2Space G] (hμ : is_mul_left_invariant μ) (hν : is_mul_left_invariant ν)
    [regular ν] {E : Set G} (hE : IsCompact E) (h2E : ν E ≠ 0) (f : G → ℝ≥0∞) (hf : Measurable f) :
    (μ E * ∫⁻ y, f y⁻¹ / ν ((fun h => h * y⁻¹) ⁻¹' E) ∂ν) = ∫⁻ x, f x ∂μ := by
  have Em := hE.measurable_set
  symm
  set g := fun y => f y⁻¹ / ν ((fun h => h * y⁻¹) ⁻¹' E)
  have hg : Measurable g := (hf.comp measurable_inv).div ((measurable_measure_mul_right Em).comp measurable_inv)
  rw [← set_lintegral_one, ← lintegral_indicator _ Em, ←
    lintegral_lintegral_mul (measurable_const.indicator Em).AeMeasurable hg.ae_measurable, ←
    lintegral_lintegral_mul_inv hμ hν]
  swap
  · exact (((measurable_const.indicator Em).comp measurable_fst).mul (hg.comp measurable_snd)).AeMeasurable
    
  have mE : ∀ x : G, Measurable fun y => ((fun z => z * x) ⁻¹' E).indicator (fun z => (1 : ℝ≥0∞)) y := fun x =>
    measurable_const.indicator (measurable_mul_const _ Em)
  have : ∀ x y, E.indicator (fun z : G => (1 : ℝ≥0∞)) (y * x) = ((fun z => z * x) ⁻¹' E).indicator (fun b : G => 1) y :=
    by
    intro x y
    symm
    convert indicator_comp_right fun y => y * x
    ext1 z
    rfl
  have h3E : ∀ y, ν ((fun x => x * y) ⁻¹' E) ≠ ∞ := fun y =>
    (IsCompact.measure_lt_top <| (Homeomorph.mulRight _).compact_preimage.mpr hE).Ne
  simp_rw [this, lintegral_mul_const _ (mE _), lintegral_indicator _ (measurable_mul_const _ Em), set_lintegral_one, g,
    inv_invₓ, Ennreal.mul_div_cancel' (measure_mul_right_ne_zero hν h2E _) (h3E _)]

/-- This is roughly the uniqueness (up to a scalar) of left invariant Borel measures on a second
  countable locally compact group. The uniqueness of Haar measure is proven from this in
  `measure_theory.measure.haar_measure_unique` -/
@[to_additive]
theorem measure_mul_measure_eq [T2Space G] (hμ : is_mul_left_invariant μ) (hν : is_mul_left_invariant ν) [regular ν]
    {E F : Set G} (hE : IsCompact E) (hF : MeasurableSet F) (h2E : ν E ≠ 0) : μ E * ν F = ν E * μ F := by
  have h1 := measure_lintegral_div_measure hν hν hE h2E (F.indicator fun x => 1) (measurable_const.indicator hF)
  have h2 := measure_lintegral_div_measure hμ hν hE h2E (F.indicator fun x => 1) (measurable_const.indicator hF)
  rw [lintegral_indicator _ hF, set_lintegral_one] at h1 h2
  rw [← h1, mul_left_commₓ, h2]

end MeasureTheory

