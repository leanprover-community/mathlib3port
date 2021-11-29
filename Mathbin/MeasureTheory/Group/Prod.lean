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


noncomputable theory

open TopologicalSpace

open Set hiding prod_eq

open Function

open_locale Classical Ennreal Pointwise

namespace MeasureTheory

open Measureₓ

variable{G : Type _}[TopologicalSpace G][MeasurableSpace G][second_countable_topology G]

variable[BorelSpace G][Groupₓ G][TopologicalGroup G]

variable{μ ν : Measureₓ G}[sigma_finite ν][sigma_finite μ]

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- This condition is part of the definition of a measurable group in [Halmos, §59].
  There, the map in this lemma is called `S`. -/
@[to_additive #[ident map_prod_sum_eq]]
theorem map_prod_mul_eq
(hν : is_mul_left_invariant ν) : «expr = »(map (λ
  z : «expr × »(G, G), (z.1, «expr * »(z.1, z.2))) (μ.prod ν), μ.prod ν) :=
begin
  refine [expr (prod_eq _).symm],
  intros [ident s, ident t, ident hs, ident ht],
  simp_rw ["[", expr map_apply (measurable_fst.prod_mk (measurable_fst.mul measurable_snd)) (hs.prod ht), ",", expr prod_apply (measurable_fst.prod_mk (measurable_fst.mul measurable_snd) (hs.prod ht)), ",", expr preimage_preimage, "]"] [],
  conv_lhs [] [] { congr,
    skip,
    funext,
    rw ["[", expr mk_preimage_prod_right_fn_eq_if (((«expr * »)) x), ",", expr measure_if, "]"] },
  simp_rw ["[", expr hν _ ht, ",", expr lintegral_indicator _ hs, ",", expr set_lintegral_const, ",", expr mul_comm, "]"] []
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The function we are mapping along is `SR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive #[ident map_prod_add_eq_swap]]
theorem map_prod_mul_eq_swap
(hμ : is_mul_left_invariant μ) : «expr = »(map (λ
  z : «expr × »(G, G), (z.2, «expr * »(z.2, z.1))) (μ.prod ν), ν.prod μ) :=
begin
  rw ["[", "<-", expr prod_swap, "]"] [],
  simp_rw ["[", expr map_map (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)) measurable_swap, "]"] [],
  exact [expr map_prod_mul_eq hμ]
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The function we are mapping along is `S⁻¹` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq`. -/
@[to_additive #[ident map_prod_neg_add_eq]]
theorem map_prod_inv_mul_eq
(hν : is_mul_left_invariant ν) : «expr = »(map (λ
  z : «expr × »(G, G), (z.1, «expr * »(«expr ⁻¹»(z.1), z.2))) (μ.prod ν), μ.prod ν) :=
«expr $ »((homeomorph.shear_mul_right G).to_measurable_equiv.map_apply_eq_iff_map_symm_apply_eq.mp, map_prod_mul_eq hν)

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The function we are mapping along is `S⁻¹R` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive #[ident map_prod_neg_add_eq_swap]]
theorem map_prod_inv_mul_eq_swap
(hμ : is_mul_left_invariant μ) : «expr = »(map (λ
  z : «expr × »(G, G), (z.2, «expr * »(«expr ⁻¹»(z.2), z.1))) (μ.prod ν), ν.prod μ) :=
begin
  rw ["[", "<-", expr prod_swap, "]"] [],
  simp_rw ["[", expr map_map «expr $ »(measurable_snd.prod_mk, measurable_snd.inv.mul measurable_fst) measurable_swap, "]"] [],
  exact [expr map_prod_inv_mul_eq hμ]
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The function we are mapping along is `S⁻¹RSR` in [Halmos, §59],
  where `S` is the map in `map_prod_mul_eq` and `R` is `prod.swap`. -/
@[to_additive #[ident map_prod_add_neg_eq]]
theorem map_prod_mul_inv_eq
(hμ : is_mul_left_invariant μ)
(hν : is_mul_left_invariant ν) : «expr = »(map (λ
  z : «expr × »(G, G), («expr * »(z.2, z.1), «expr ⁻¹»(z.1))) (μ.prod ν), μ.prod ν) :=
begin
  let [ident S] [] [":=", expr (homeomorph.shear_mul_right G).to_measurable_equiv],
  suffices [] [":", expr «expr = »(map «expr ∘ »(λ
     z : «expr × »(G, G), (z.2, «expr * »(«expr ⁻¹»(z.2), z.1)), λ
     z : «expr × »(G, G), (z.2, «expr * »(z.2, z.1))) (μ.prod ν), μ.prod ν)],
  { convert [] [expr this] [],
    ext1 [] ["⟨", ident x, ",", ident y, "⟩"],
    simp [] [] [] [] [] [] },
  simp_rw ["[", "<-", expr map_map (measurable_snd.prod_mk (measurable_snd.inv.mul measurable_fst)) (measurable_snd.prod_mk (measurable_snd.mul measurable_fst)), ",", expr map_prod_mul_eq_swap hμ, ",", expr map_prod_inv_mul_eq_swap hν, "]"] []
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem quasi_measure_preserving_inv
(hμ : is_mul_left_invariant μ) : quasi_measure_preserving (has_inv.inv : G → G) μ μ :=
begin
  refine [expr ⟨measurable_inv, «expr $ »(absolutely_continuous.mk, λ s hsm hμs, _)⟩],
  rw ["[", expr map_apply measurable_inv hsm, ",", expr inv_preimage, "]"] [],
  have [ident hf] [":", expr measurable (λ
    z : «expr × »(G, G), («expr * »(z.2, z.1), «expr ⁻¹»(z.1)))] [":=", expr (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv],
  suffices [] [":", expr «expr = »(map (λ
     z : «expr × »(G, G), («expr * »(z.2, z.1), «expr ⁻¹»(z.1))) (μ.prod μ) («expr ⁻¹»(s).prod «expr ⁻¹»(s)), 0)],
  { simpa [] [] ["only"] ["[", expr map_prod_mul_inv_eq hμ hμ, ",", expr prod_prod, ",", expr mul_eq_zero, ",", expr or_self, "]"] [] ["using", expr this] },
  have [ident hsm'] [":", expr measurable_set («expr ⁻¹»(s).prod «expr ⁻¹»(s))] [":=", expr hsm.inv.prod hsm.inv],
  simp_rw ["[", expr map_apply hf hsm', ",", expr prod_apply_symm (hf hsm'), ",", expr preimage_preimage, ",", expr mk_preimage_prod, ",", expr inv_preimage, ",", expr set.inv_inv, ",", expr measure_mono_null (inter_subset_right _ _) hμs, ",", expr lintegral_zero, "]"] []
end

@[toAdditive]
theorem measure_inv_null (hμ : is_mul_left_invariant μ) {E : Set G} : μ ((fun x => x⁻¹) ⁻¹' E) = 0 ↔ μ E = 0 :=
  by 
    refine' ⟨fun hE => _, (quasi_measure_preserving_inv hμ).preimage_null⟩
    convert (quasi_measure_preserving_inv hμ).preimage_null hE 
    exact set.inv_inv.symm

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
@[to_additive #[]]
theorem measurable_measure_mul_right
{E : set G}
(hE : measurable_set E) : measurable (λ x, μ «expr ⁻¹' »(λ y, «expr * »(y, x), E)) :=
begin
  suffices [] [":", expr measurable (λ
    y, μ «expr ⁻¹' »(λ x, (x, y), «expr ⁻¹' »(λ z : «expr × »(G, G), (1, «expr * »(z.1, z.2)), set.prod univ E)))],
  { convert [] [expr this] [],
    ext1 [] [ident x],
    congr' [1] ["with", ident y, ":", 1],
    simp [] [] [] [] [] [] },
  apply [expr measurable_measure_prod_mk_right],
  exact [expr measurable_const.prod_mk (measurable_fst.mul measurable_snd) (measurable_set.univ.prod hE)]
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem lintegral_lintegral_mul_inv
(hμ : is_mul_left_invariant μ)
(hν : is_mul_left_invariant ν)
(f : G → G → «exprℝ≥0∞»())
(hf : ae_measurable (uncurry f) (μ.prod ν)) : «expr = »(«expr∫⁻ , ∂ »((x), «expr∫⁻ , ∂ »((y), f «expr * »(y, x) «expr ⁻¹»(x), ν), μ), «expr∫⁻ , ∂ »((x), «expr∫⁻ , ∂ »((y), f x y, ν), μ)) :=
begin
  have [ident h] [":", expr measurable (λ
    z : «expr × »(G, G), («expr * »(z.2, z.1), «expr ⁻¹»(z.1)))] [":=", expr (measurable_snd.mul measurable_fst).prod_mk measurable_fst.inv],
  have [ident h2f] [":", expr ae_measurable «expr $ »(uncurry, λ x y, f «expr * »(y, x) «expr ⁻¹»(x)) (μ.prod ν)] [],
  { apply [expr hf.comp_measurable' h (map_prod_mul_inv_eq hμ hν).absolutely_continuous] },
  simp_rw ["[", expr lintegral_lintegral h2f, ",", expr lintegral_lintegral hf, "]"] [],
  conv_rhs [] [] { rw ["[", "<-", expr map_prod_mul_inv_eq hμ hν, "]"] },
  symmetry,
  exact [expr lintegral_map' (hf.mono' (map_prod_mul_inv_eq hμ hν).absolutely_continuous) h]
end

@[toAdditive]
theorem measure_mul_right_null (hμ : is_mul_left_invariant μ) {E : Set G} (y : G) :
  μ ((fun x => x*y) ⁻¹' E) = 0 ↔ μ E = 0 :=
  calc μ ((fun x => x*y) ⁻¹' E) = 0 ↔ μ (HasInv.inv ⁻¹' ((fun x => y⁻¹*x) ⁻¹' (HasInv.inv ⁻¹' E))) = 0 :=
    by 
      simp only [preimage_preimage, mul_inv_rev, inv_invₓ]
    _ ↔ μ E = 0 :=
    by 
      simp only [measure_inv_null hμ, hμ.measure_preimage_mul]
    

@[toAdditive]
theorem measure_mul_right_ne_zero (hμ : is_mul_left_invariant μ) {E : Set G} (h2E : μ E ≠ 0) (y : G) :
  μ ((fun x => x*y) ⁻¹' E) ≠ 0 :=
  (not_iff_not_of_iff (measure_mul_right_null hμ y)).mpr h2E

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A technical lemma relating two different measures. This is basically [Halmos, §60 Th. A].
  Note that if `f` is the characteristic function of a measurable set `F` this states that
  `μ F = c * μ E` for a constant `c` that does not depend on `μ`.
  There seems to be a gap in the last step of the proof in [Halmos].
  In the last line, the equality `g(x⁻¹)ν(Ex⁻¹) = f(x)` holds if we can prove that
  `0 < ν(Ex⁻¹) < ∞`. The first inequality follows from §59, Th. D, but I couldn't find the second
  inequality. For this reason, we use a compact `E` instead of a measurable `E` as in [Halmos], and
  additionally assume that `ν` is a regular measure (we only need that it is finite on compact
  sets). -/
@[to_additive #[]]
theorem measure_lintegral_div_measure
[t2_space G]
(hμ : is_mul_left_invariant μ)
(hν : is_mul_left_invariant ν)
[regular ν]
{E : set G}
(hE : is_compact E)
(h2E : «expr ≠ »(ν E, 0))
(f : G → «exprℝ≥0∞»())
(hf : measurable f) : «expr = »(«expr * »(μ E, «expr∫⁻ , ∂ »((y), «expr / »(f «expr ⁻¹»(y), ν «expr ⁻¹' »(λ
     h, «expr * »(h, «expr ⁻¹»(y)), E)), ν)), «expr∫⁻ , ∂ »((x), f x, μ)) :=
begin
  have [ident Em] [] [":=", expr hE.measurable_set],
  symmetry,
  set [] [ident g] [] [":="] [expr λ
   y, «expr / »(f «expr ⁻¹»(y), ν «expr ⁻¹' »(λ h, «expr * »(h, «expr ⁻¹»(y)), E))] [],
  have [ident hg] [":", expr measurable g] [":=", expr (hf.comp measurable_inv).div ((measurable_measure_mul_right Em).comp measurable_inv)],
  rw ["[", "<-", expr set_lintegral_one, ",", "<-", expr lintegral_indicator _ Em, ",", "<-", expr lintegral_lintegral_mul (measurable_const.indicator Em).ae_measurable hg.ae_measurable, ",", "<-", expr lintegral_lintegral_mul_inv hμ hν, "]"] [],
  swap,
  { exact [expr (((measurable_const.indicator Em).comp measurable_fst).mul (hg.comp measurable_snd)).ae_measurable] },
  have [ident mE] [":", expr ∀
   x : G, measurable (λ
    y, «expr ⁻¹' »(λ
     z, «expr * »(z, x), E).indicator (λ
     z, (1 : «exprℝ≥0∞»())) y)] [":=", expr λ x, measurable_const.indicator (measurable_mul_const _ Em)],
  have [] [":", expr ∀
   x
   y, «expr = »(E.indicator (λ
     z : G, (1 : «exprℝ≥0∞»())) «expr * »(y, x), «expr ⁻¹' »(λ z, «expr * »(z, x), E).indicator (λ b : G, 1) y)] [],
  { intros [ident x, ident y],
    symmetry,
    convert [] [expr indicator_comp_right (λ y, «expr * »(y, x))] [],
    ext1 [] [ident z],
    refl },
  have [ident h3E] [":", expr ∀
   y, «expr ≠ »(ν «expr ⁻¹' »(λ
     x, «expr * »(x, y), E), «expr∞»())] [":=", expr λ
   y, «expr $ »(regular.lt_top_of_is_compact, (homeomorph.mul_right _).compact_preimage.mpr hE).ne],
  simp_rw ["[", expr this, ",", expr lintegral_mul_const _ (mE _), ",", expr lintegral_indicator _ (measurable_mul_const _ Em), ",", expr set_lintegral_one, ",", expr g, ",", expr inv_inv, ",", expr ennreal.mul_div_cancel' (measure_mul_right_ne_zero hν h2E _) (h3E _), "]"] []
end

-- error in MeasureTheory.Group.Prod: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This is roughly the uniqueness (up to a scalar) of left invariant Borel measures on a second
  countable locally compact group. The uniqueness of Haar measure is proven from this in
  `measure_theory.measure.haar_measure_unique` -/
@[to_additive #[]]
theorem measure_mul_measure_eq
[t2_space G]
(hμ : is_mul_left_invariant μ)
(hν : is_mul_left_invariant ν)
[regular ν]
{E F : set G}
(hE : is_compact E)
(hF : measurable_set F)
(h2E : «expr ≠ »(ν E, 0)) : «expr = »(«expr * »(μ E, ν F), «expr * »(ν E, μ F)) :=
begin
  have [ident h1] [] [":=", expr measure_lintegral_div_measure hν hν hE h2E (F.indicator (λ
     x, 1)) (measurable_const.indicator hF)],
  have [ident h2] [] [":=", expr measure_lintegral_div_measure hμ hν hE h2E (F.indicator (λ
     x, 1)) (measurable_const.indicator hF)],
  rw ["[", expr lintegral_indicator _ hF, ",", expr set_lintegral_one, "]"] ["at", ident h1, ident h2],
  rw ["[", "<-", expr h1, ",", expr mul_left_comm, ",", expr h2, "]"] []
end

end MeasureTheory

