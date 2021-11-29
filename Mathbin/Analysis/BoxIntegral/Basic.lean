import Mathbin.Analysis.BoxIntegral.Partition.Filter 
import Mathbin.Analysis.BoxIntegral.Partition.Measure 
import Mathbin.Topology.UniformSpace.CompactSeparated

/-!
# Integrals of Riemann, Henstock-Kurzweil, and McShane

In this file we define the integral of a function over a box in `ℝⁿ. The same definition works for
Riemann, Henstock-Kurzweil, and McShane integrals.

As usual, we represent `ℝⁿ` as the type of functions `ι → ℝ` for some finite type `ι`. A rectangular
box `(l, u]` in `ℝⁿ` is defined to be the set `{x : ι → ℝ | ∀ i, l i < x i ∧ x i ≤ u i}`, see
`box_integral.box`.

Let `vol` be a box-additive function on boxes in `ℝⁿ` with codomain `E →L[ℝ] F`. Given a function
`f : ℝⁿ → E`, a box `I` and a tagged partition `π` of this box, the *integral sum* of `f` over `π`
with respect to the volume `vol` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. Here
`π.tag J` is the point (tag) in `ℝⁿ` associated with the box `J`.

The integral is defined as the limit of integral sums along a filter. Different filters correspond
to different integration theories. In order to avoid code duplication, all our definitions and
theorems take an argument `l : box_integral.integration_params`. This is a type that holds three
boolean values, and encodes eight filters including those corresponding to Riemann,
Henstock-Kurzweil, and McShane integrals.

Following the design of infinite sums (see `has_sum` and `tsum`), we define a predicate
`box_integral.has_integral` and a function `box_integral.integral` that returns a vector satisfying
the predicate or zero if the function is not integrable.

Then we prove some basic properties of box integrals (linearity, a formula for the integral of a
constant). We also prove a version of the Henstock-Sacks inequality (see
`box_integral.integrable.dist_integral_sum_le_of_mem_base_set` and
`box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq`), prove
integrability of continuous functions, and provide a criterion for integrability w.r.t. a
non-Riemann filter (e.g., Henstock-Kurzweil and McShane).

## Notation

- `ℝⁿ`: local notation for `ι → ℝ`

## Tags

integral
-/


open_locale BigOperators Classical TopologicalSpace Nnreal Filter uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable theory

namespace BoxIntegral

universe u v w

variable{ι :
    Type
      u}{E :
    Type
      v}{F :
    Type w}[NormedGroup E][NormedSpace ℝ E][NormedGroup F][NormedSpace ℝ F]{I J : box ι}{π : tagged_prepartition I}

open TaggedPrepartition

local notation "ℝⁿ" => ι → ℝ

/-!
### Integral sum and its basic properties
-/


/-- The integral sum of `f : ℝⁿ → E` over a tagged prepartition `π` w.r.t. box-additive volume `vol`
with codomain `E →L[ℝ] F` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. -/
def integral_sum (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I) : F :=
  ∑J in π.boxes, vol J (f (π.tag J))

theorem integral_sum_bUnion_tagged (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : prepartition I)
  (πi : ∀ J, tagged_prepartition J) :
  integral_sum f vol (π.bUnion_tagged πi) = ∑J in π.boxes, integral_sum f vol (πi J) :=
  by 
    refine' (π.sum_bUnion_boxes _ _).trans (sum_congr rfl$ fun J hJ => sum_congr rfl$ fun J' hJ' => _)
    rw [π.tag_bUnion_tagged hJ hJ']

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem integral_sum_bUnion_partition
(f : «exprℝⁿ»() → E)
(vol : «expr →ᵇᵃ »(ι, «expr →L[ ] »(E, exprℝ(), F)))
(π : tagged_prepartition I)
(πi : ∀ J, prepartition J)
(hπi : ∀
 J «expr ∈ » π, (πi J).is_partition) : «expr = »(integral_sum f vol (π.bUnion_prepartition πi), integral_sum f vol π) :=
begin
  refine [expr (π.to_prepartition.sum_bUnion_boxes _ _).trans «expr $ »(sum_congr rfl, λ J hJ, _)],
  calc
    «expr = »(«expr∑ in , »((J'), (πi J).boxes, vol J' (f «expr $ »(π.tag, π.to_prepartition.bUnion_index πi J'))), «expr∑ in , »((J'), (πi J).boxes, vol J' (f (π.tag J)))) : sum_congr rfl (λ
     J' hJ', by rw ["[", expr prepartition.bUnion_index_of_mem _ hJ hJ', "]"] [])
    «expr = »(..., vol J (f (π.tag J))) : (vol.map ⟨λ
      g : «expr →L[ ] »(E, exprℝ(), F), g (f (π.tag J)), rfl, λ _ _, rfl⟩).sum_partition_boxes le_top (hπi J hJ)
end

theorem integral_sum_inf_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I)
  {π' : prepartition I} (h : π'.is_partition) : integral_sum f vol (π.inf_prepartition π') = integral_sum f vol π :=
  integral_sum_bUnion_partition f vol π _$ fun J hJ => h.restrict (prepartition.le_of_mem _ hJ)

theorem integral_sum_fiberwise {α} (g : box ι → α) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I) :
  (∑y in π.boxes.image g, integral_sum f vol (π.filter fun x => g x = y)) = integral_sum f vol π :=
  π.to_prepartition.sum_fiberwise g fun J => vol J (f$ π.tag J)

theorem integral_sum_sub_partitions (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) {π₁ π₂ : tagged_prepartition I}
  (h₁ : π₁.is_partition) (h₂ : π₂.is_partition) :
  integral_sum f vol π₁ - integral_sum f vol π₂ =
    ∑J in (π₁.to_prepartition⊓π₂.to_prepartition).boxes,
      vol J (f$ (π₁.inf_prepartition π₂.to_prepartition).Tag J) -
        vol J (f$ (π₂.inf_prepartition π₁.to_prepartition).Tag J) :=
  by 
    rw [←integral_sum_inf_partition f vol π₁ h₂, ←integral_sum_inf_partition f vol π₂ h₁, integral_sum, integral_sum,
      Finset.sum_sub_distrib]
    simp only [inf_prepartition_to_prepartition, inf_comm]

@[simp]
theorem integral_sum_disj_union (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) {π₁ π₂ : tagged_prepartition I}
  (h : Disjoint π₁.Union π₂.Union) :
  integral_sum f vol (π₁.disj_union π₂ h) = integral_sum f vol π₁+integral_sum f vol π₂ :=
  by 
    refine'
      (prepartition.sum_disj_union_boxes h _).trans
        (congr_arg2 (·+·) (sum_congr rfl$ fun J hJ => _) (sum_congr rfl$ fun J hJ => _))
    ·
      rw [disj_union_tag_of_mem_left _ hJ]
    ·
      rw [disj_union_tag_of_mem_right _ hJ]

@[simp]
theorem integral_sum_add (f g : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I) :
  integral_sum (f+g) vol π = integral_sum f vol π+integral_sum g vol π :=
  by 
    simp only [integral_sum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]

@[simp]
theorem integral_sum_neg (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
  by 
    simp only [integral_sum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]

@[simp]
theorem integral_sum_smul (c : ℝ) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : tagged_prepartition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
  by 
    simp only [integral_sum, Finset.smul_sum, Pi.smul_apply, ContinuousLinearMap.map_smul]

variable[Fintype ι]

/-!
### Basic integrability theory
-/


/-- The predicate `has_integral I l f vol y` says that `y` is the integral of `f` over `I` along `l`
w.r.t. volume `vol`. This means that integral sums of `f` tend to `𝓝 y` along
`box_integral.integration_params.to_filter_Union I ⊤`. -/
def has_integral (I : box ι) (l : integration_params) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (y : F) : Prop :=
  tendsto (integral_sum f vol) (l.to_filter_Union I ⊤) (𝓝 y)

/-- A function is integrable if there exists a vector that satisfies the `has_integral`
predicate. -/
def integrable (I : box ι) (l : integration_params) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  ∃ y, has_integral I l f vol y

/-- The integral of a function `f` over a box `I` along a filter `l` w.r.t. a volume `vol`.  Returns
zero on non-integrable functions. -/
def integral (I : box ι) (l : integration_params) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  if h : integrable I l f vol then h.some else 0

variable{l : integration_params}{f g : ℝⁿ → E}{vol : ι →ᵇᵃ E →L[ℝ] F}{y y' : F}

/-- Reinterpret `box_integral.has_integral` as `filter.tendsto`, e.g., dot-notation theorems
that are shadowed in the `box_integral.has_integral` namespace. -/
theorem has_integral.tendsto (h : has_integral I l f vol y) :
  tendsto (integral_sum f vol) (l.to_filter_Union I ⊤) (𝓝 y) :=
  h

/-- The `ε`-`δ` definition of `box_integral.has_integral`. -/
theorem has_integral_iff :
  has_integral I l f vol y ↔
    ∀ ε (_ : ε > (0 : ℝ)),
      ∃ r :  ℝ≥0  → ℝⁿ → Ioi (0 : ℝ),
        (∀ c, l.r_cond (r c)) ∧
          ∀ c π, l.mem_base_set I c (r c) π → is_partition π → dist (integral_sum f vol π) y ≤ ε :=
  ((l.has_basis_to_filter_Union_top I).tendsto_iff nhds_basis_closed_ball).trans$
    by 
      simp [@forall_swap ℝ≥0  (tagged_prepartition I)]

/-- Quite often it is more natural to prove an estimate of the form `a * ε`, not `ε` in the RHS of
`box_integral.has_integral_iff`, so we provide this auxiliary lemma.  -/
theorem has_integral_of_mul (a : ℝ)
  (h :
    ∀ (ε : ℝ),
      0 < ε →
        ∃ r :  ℝ≥0  → ℝⁿ → Ioi (0 : ℝ),
          (∀ c, l.r_cond (r c)) ∧
            ∀ c π, l.mem_base_set I c (r c) π → is_partition π → dist (integral_sum f vol π) y ≤ a*ε) :
  has_integral I l f vol y :=
  by 
    refine' has_integral_iff.2 fun ε hε => _ 
    rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
    rcases h ε' hε' with ⟨r, hr, H⟩
    exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩

theorem integrable_iff_cauchy [CompleteSpace F] :
  integrable I l f vol ↔ Cauchy ((l.to_filter_Union I ⊤).map (integral_sum f vol)) :=
  cauchy_map_iff_exists_tendsto.symm

/-- In a complete space, a function is integrable if and only if its integral sums form a Cauchy
net. Here we restate this fact in terms of `∀ ε > 0, ∃ r, ...`. -/
theorem integrable_iff_cauchy_basis [CompleteSpace F] :
  integrable I l f vol ↔
    ∀ ε (_ : ε > (0 : ℝ)),
      ∃ r :  ℝ≥0  → ℝⁿ → Ioi (0 : ℝ),
        (∀ c, l.r_cond (r c)) ∧
          ∀ c₁ c₂ π₁ π₂,
            l.mem_base_set I c₁ (r c₁) π₁ →
              π₁.is_partition →
                l.mem_base_set I c₂ (r c₂) π₂ →
                  π₂.is_partition → dist (integral_sum f vol π₁) (integral_sum f vol π₂) ≤ ε :=
  by 
    rw [integrable_iff_cauchy, cauchy_map_iff',
      (l.has_basis_to_filter_Union_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
    refine' forall_congrₓ fun ε => forall_congrₓ$ fun ε0 => exists_congr$ fun r => _ 
    simp only [exists_prop, Prod.forall, Set.mem_Union, exists_imp_distrib, prod_mk_mem_set_prod_eq, and_imp,
      mem_inter_eq, mem_set_of_eq]
    exact
      and_congr Iff.rfl
        ⟨fun H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂ => H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂,
          fun H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂ => H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂⟩

theorem has_integral.mono {l₁ l₂ : integration_params} (h : has_integral I l₁ f vol y) (hl : l₂ ≤ l₁) :
  has_integral I l₂ f vol y :=
  h.mono_left$ integration_params.to_filter_Union_mono _ hl _

protected theorem integrable.has_integral (h : integrable I l f vol) : has_integral I l f vol (integral I l f vol) :=
  by 
    rw [integral, dif_pos h]
    exact Classical.some_spec h

theorem integrable.mono {l'} (h : integrable I l f vol) (hle : l' ≤ l) : integrable I l' f vol :=
  ⟨_, h.has_integral.mono hle⟩

theorem has_integral.unique (h : has_integral I l f vol y) (h' : has_integral I l f vol y') : y = y' :=
  tendsto_nhds_unique h h'

theorem has_integral.integrable (h : has_integral I l f vol y) : integrable I l f vol :=
  ⟨_, h⟩

theorem has_integral.integral_eq (h : has_integral I l f vol y) : integral I l f vol = y :=
  h.integrable.has_integral.unique h

theorem has_integral.add (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f+g) vol (y+y') :=
  by 
    simpa only [has_integral, ←integral_sum_add] using h.add h'

theorem integrable.add (hf : integrable I l f vol) (hg : integrable I l g vol) : integrable I l (f+g) vol :=
  (hf.has_integral.add hg.has_integral).Integrable

theorem integral_add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f+g) vol = integral I l f vol+integral I l g vol :=
  (hf.has_integral.add hg.has_integral).integral_eq

theorem has_integral.neg (hf : has_integral I l f vol y) : has_integral I l (-f) vol (-y) :=
  by 
    simpa only [has_integral, ←integral_sum_neg] using hf.neg

theorem integrable.neg (hf : integrable I l f vol) : integrable I l (-f) vol :=
  hf.has_integral.neg.integrable

theorem integrable.of_neg (hf : integrable I l (-f) vol) : integrable I l f vol :=
  neg_negₓ f ▸ hf.neg

@[simp]
theorem integrable_neg : integrable I l (-f) vol ↔ integrable I l f vol :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩

@[simp]
theorem integral_neg : integral I l (-f) vol = -integral I l f vol :=
  if h : integrable I l f vol then h.has_integral.neg.integral_eq else
    by 
      rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

theorem has_integral.sub (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f - g) vol (y - y') :=
  by 
    simpa only [sub_eq_add_neg] using h.add h'.neg

theorem integrable.sub (hf : integrable I l f vol) (hg : integrable I l g vol) : integrable I l (f - g) vol :=
  (hf.has_integral.sub hg.has_integral).Integrable

theorem integral_sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
  (hf.has_integral.sub hg.has_integral).integral_eq

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem has_integral_const (c : E) : has_integral I l (λ _, c) vol (vol I c) :=
«expr $ »(tendsto_const_nhds.congr', «expr $ »((l.eventually_is_partition I).mono, λ
  π hπ, ((vol.map ⟨λ g : «expr →L[ ] »(E, exprℝ(), F), g c, rfl, λ _ _, rfl⟩).sum_partition_boxes le_top hπ).symm))

@[simp]
theorem integral_const (c : E) : integral I l (fun _ => c) vol = vol I c :=
  (has_integral_const c).integral_eq

theorem integrable_const (c : E) : integrable I l (fun _ => c) vol :=
  ⟨_, has_integral_const c⟩

theorem has_integral_zero : has_integral I l (fun _ => (0 : E)) vol 0 :=
  by 
    simpa only [←(vol I).map_zero] using has_integral_const (0 : E)

theorem integrable_zero : integrable I l (fun _ => (0 : E)) vol :=
  ⟨0, has_integral_zero⟩

theorem integral_zero : integral I l (fun _ => (0 : E)) vol = 0 :=
  has_integral_zero.integral_eq

theorem has_integral_sum {α : Type _} {s : Finset α} {f : α → ℝⁿ → E} {g : α → F}
  (h : ∀ i (_ : i ∈ s), has_integral I l (f i) vol (g i)) :
  has_integral I l (fun x => ∑i in s, f i x) vol (∑i in s, g i) :=
  by 
    induction' s using Finset.induction_on with a s ha ihs
    ·
      simp [has_integral_zero]
    simp only [Finset.sum_insert ha]
    rw [Finset.forall_mem_insert] at h 
    exact h.1.add (ihs h.2)

theorem has_integral.smul (hf : has_integral I l f vol y) (c : ℝ) : has_integral I l (c • f) vol (c • y) :=
  by 
    simpa only [has_integral, ←integral_sum_smul] using (tendsto_const_nhds : tendsto _ _ (𝓝 c)).smul hf

theorem integrable.smul (hf : integrable I l f vol) (c : ℝ) : integrable I l (c • f) vol :=
  (hf.has_integral.smul c).Integrable

theorem integrable.of_smul {c : ℝ} (hf : integrable I l (c • f) vol) (hc : c ≠ 0) : integrable I l f vol :=
  by 
    convert hf.smul (c⁻¹)
    ext x 
    simp only [Pi.smul_apply, inv_smul_smul₀ hc]

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem integral_smul
(c : exprℝ()) : «expr = »(integral I l (λ x, «expr • »(c, f x)) vol, «expr • »(c, integral I l f vol)) :=
begin
  rcases [expr eq_or_ne c 0, "with", ident rfl, "|", ident hc],
  { simp [] [] ["only"] ["[", expr zero_smul, ",", expr integral_zero, "]"] [] [] },
  by_cases [expr hf, ":", expr integrable I l f vol],
  { exact [expr (hf.has_integral.smul c).integral_eq] },
  { have [] [":", expr «expr¬ »(integrable I l (λ x, «expr • »(c, f x)) vol)] [],
    from [expr mt (λ h, h.of_smul hc) hf],
    rw ["[", expr integral, ",", expr integral, ",", expr dif_neg hf, ",", expr dif_neg this, ",", expr smul_zero, "]"] [] }
end

open MeasureTheory

/-- The integral of a nonnegative function w.r.t. a volume generated by a locally-finite measure is
nonnegative. -/
theorem integral_nonneg {g : ℝⁿ → ℝ} (hg : ∀ x (_ : x ∈ I.Icc), 0 ≤ g x) (μ : Measureₓ ℝⁿ)
  [is_locally_finite_measure μ] : 0 ≤ integral I l g μ.to_box_additive.to_smul :=
  by 
    byCases' hgi : integrable I l g μ.to_box_additive.to_smul
    ·
      refine' ge_of_tendsto' hgi.has_integral fun π => sum_nonneg$ fun J hJ => _ 
      exact mul_nonneg Ennreal.to_real_nonneg (hg _$ π.tag_mem_Icc _)
    ·
      rw [integral, dif_neg hgi]

/-- If `∥f x∥ ≤ g x` on `[l, u]` and `g` is integrable, then the norm of the integral of `f` is less
than or equal to the integral of `g`. -/
theorem norm_integral_le_of_norm_le {g : ℝⁿ → ℝ} (hle : ∀ x (_ : x ∈ I.Icc), ∥f x∥ ≤ g x) (μ : Measureₓ ℝⁿ)
  [is_locally_finite_measure μ] (hg : integrable I l g μ.to_box_additive.to_smul) :
  ∥(integral I l f μ.to_box_additive.to_smul : E)∥ ≤ integral I l g μ.to_box_additive.to_smul :=
  by 
    byCases' hfi : integrable.{u, v, v} I l f μ.to_box_additive.to_smul
    ·
      refine' le_of_tendsto_of_tendsto' hfi.has_integral.norm hg.has_integral fun π => _ 
      refine' norm_sum_le_of_le _ fun J hJ => _ 
      simp only [box_additive_map.to_smul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs, μ.to_box_additive_apply,
        abs_of_nonneg Ennreal.to_real_nonneg]
      exact mul_le_mul_of_nonneg_left (hle _$ π.tag_mem_Icc _) Ennreal.to_real_nonneg
    ·
      rw [integral, dif_neg hfi, norm_zero]
      exact integral_nonneg (fun x hx => (norm_nonneg _).trans (hle x hx)) μ

theorem norm_integral_le_of_le_const {c : ℝ} (hc : ∀ x (_ : x ∈ I.Icc), ∥f x∥ ≤ c) (μ : Measureₓ ℝⁿ)
  [is_locally_finite_measure μ] : ∥(integral I l f μ.to_box_additive.to_smul : E)∥ ≤ (μ I).toReal*c :=
  by 
    simpa only [integral_const] using norm_integral_le_of_norm_le hc μ (integrable_const c)

/-!
# Henstock-Sacks inequality and integrability on subboxes

Henstock-Sacks inequality for Henstock-Kurzweil integral says the following. Let `f` be a function
integrable on a box `I`; let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged partition of
`I` subordinate to `r`, the integral sum over this partition is `ε`-close to the integral. Then for
any tagged prepartition (i.e. a finite collections of pairwise disjoint subboxes of `I` with tagged
points) `π`, the integral sum over `π` differs from the integral of `f` over the part of `I` covered
by `π` by at most `ε`. The actual statement in the library is a bit more complicated to make it work
for any `box_integral.integration_params`. We formalize several versions of this inequality in
`box_integral.integrable.dist_integral_sum_le_of_mem_base_set`,
`box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq`, and
`box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set`.

Instead of using predicate assumptions on `r`, we define
`box_integral.integrable.convergence_r (h : integrable I l f vol) (ε : ℝ) (c : ℝ≥0) : ℝⁿ → (0, ∞)`
to be a function `r` such that

- if `l.bRiemann`, then `r` is a constant;
- if `ε > 0`, then for any tagged partition `π` of `I` subordinate to `r` (more precisely,
  satisfying the predicate `l.mem_base_set I c r`), the integral sum of `f` over `π` differs from
  the integral of `f` over `I` by at most `ε`.

The proof is mostly based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

-/


namespace Integrable

/-- If `ε > 0`, then `box_integral.integrable.convergence_r` is a function `r : ℝ≥0 → ℝⁿ → (0, ∞)`
such that for every `c : ℝ≥0`, for every tagged partition `π` subordinate to `r` (and satisfying
additional distortion estimates if `box_integral.integration_params.bDistortion l = tt`), the
corresponding integral sum is `ε`-close to the integral.

If `box.integral.integration_params.bRiemann = tt`, then `r c x` does not depend on `x`. If `ε ≤ 0`,
then we use `r c x = 1`.  -/
def convergence_r (h : integrable I l f vol) (ε : ℝ) :  ℝ≥0  → ℝⁿ → Ioi (0 : ℝ) :=
  if hε : 0 < ε then (has_integral_iff.1 h.has_integral ε hε).some else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩

variable{c c₁ c₂ :  ℝ≥0 }{ε ε₁ ε₂ : ℝ}{π₁ π₂ : tagged_prepartition I}

theorem convergence_r_cond (h : integrable I l f vol) (ε : ℝ) (c :  ℝ≥0 ) : l.r_cond (h.convergence_r ε c) :=
  by 
    rw [convergence_r]
    splitIfs with h₀ 
    exacts[(has_integral_iff.1 h.has_integral ε h₀).some_spec.1 _, fun _ x => rfl]

theorem dist_integral_sum_integral_le_of_mem_base_set (h : integrable I l f vol) (h₀ : 0 < ε)
  (hπ : l.mem_base_set I c (h.convergence_r ε c) π) (hπp : π.is_partition) :
  dist (integral_sum f vol π) (integral I l f vol) ≤ ε :=
  by 
    rw [convergence_r, dif_pos h₀] at hπ 
    exact (has_integral_iff.1 h.has_integral ε h₀).some_spec.2 c _ hπ hπp

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Henstock-Sacks inequality**. Let `r₁ r₂ : ℝⁿ → (0, ∞)` be function such that for any tagged
*partition* of `I` subordinate to `rₖ`, `k=1,2`, the integral sum of `f` over this partition differs
from the integral of `f` by at most `εₖ`. Then for any two tagged *prepartition* `π₁ π₂` subordinate
to `r₁` and `r₂` respectively and covering the same part of `I`, the integral sums of `f` over these
prepartitions differ from each other by at most `ε₁ + ε₂`.

The actual statement

- uses `box_integral.integrable.convergence_r` instead of a predicate assumption on `r`;
- uses `box_integral.integration_params.mem_base_set` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion.

See also `box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq` and
`box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set`.
-/
theorem dist_integral_sum_le_of_mem_base_set
(h : integrable I l f vol)
(hpos₁ : «expr < »(0, ε₁))
(hpos₂ : «expr < »(0, ε₂))
(h₁ : l.mem_base_set I c₁ (h.convergence_r ε₁ c₁) π₁)
(h₂ : l.mem_base_set I c₂ (h.convergence_r ε₂ c₂) π₂)
(HU : «expr = »(π₁.Union, π₂.Union)) : «expr ≤ »(dist (integral_sum f vol π₁) (integral_sum f vol π₂), «expr + »(ε₁, ε₂)) :=
begin
  rcases [expr h₁.exists_common_compl h₂ HU, "with", "⟨", ident π, ",", ident hπU, ",", ident hπc₁, ",", ident hπc₂, "⟩"],
  set [] [ident r] [":", expr «exprℝⁿ»() → Ioi (0 : exprℝ())] [":="] [expr λ
   x, min (h.convergence_r ε₁ c₁ x) (h.convergence_r ε₂ c₂ x)] [],
  have [ident hr] [":", expr l.r_cond r] [":=", expr (h.convergence_r_cond _ c₁).min (h.convergence_r_cond _ c₂)],
  set [] [ident πr] [] [":="] [expr π.to_subordinate r] [],
  have [ident H₁] [":", expr «expr ≤ »(dist (integral_sum f vol (π₁.union_compl_to_subordinate π hπU r)) (integral I l f vol), ε₁)] [],
  from [expr h.dist_integral_sum_integral_le_of_mem_base_set hpos₁ (h₁.union_compl_to_subordinate (λ
     _ _, min_le_left _ _) hπU hπc₁) (is_partition_union_compl_to_subordinate _ _ _ _)],
  rw [expr HU] ["at", ident hπU],
  have [ident H₂] [":", expr «expr ≤ »(dist (integral_sum f vol (π₂.union_compl_to_subordinate π hπU r)) (integral I l f vol), ε₂)] [],
  from [expr h.dist_integral_sum_integral_le_of_mem_base_set hpos₂ (h₂.union_compl_to_subordinate (λ
     _ _, min_le_right _ _) hπU hπc₂) (is_partition_union_compl_to_subordinate _ _ _ _)],
  simpa [] [] [] ["[", expr union_compl_to_subordinate, "]"] [] ["using", expr (dist_triangle_right _ _ _).trans (add_le_add H₁ H₂)]
end

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- If `f` is integrable on `I` along `l`, then for two sufficiently fine tagged prepartitions
(in the sense of the filter `box_integral.integration_params.to_filter l I`) such that they cover
the same part of `I`, the integral sums of `f` over `π₁` and `π₂` are very close to each other.  -/
theorem tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity
(h : integrable I l f vol) : tendsto (λ
 π : «expr × »(tagged_prepartition I, tagged_prepartition I), (integral_sum f vol π.1, integral_sum f vol π.2)) «expr ⊓ »(«expr ×ᶠ »(l.to_filter I, l.to_filter I), expr𝓟() {π | «expr = »(π.1.Union, π.2.Union)}) (expr𝓤() F) :=
begin
  refine [expr (((l.has_basis_to_filter I).prod_self.inf_principal _).tendsto_iff uniformity_basis_dist_le).2 (λ
    ε ε0, _)],
  replace [ident ε0] [] [":=", expr half_pos ε0],
  use ["[", expr h.convergence_r «expr / »(ε, 2), ",", expr h.convergence_r_cond «expr / »(ε, 2), "]"],
  rintro ["⟨", ident π₁, ",", ident π₂, "⟩", "⟨", "⟨", ident h₁, ",", ident h₂, "⟩", ",", ident hU, "⟩"],
  rw ["<-", expr add_halves ε] [],
  exact [expr h.dist_integral_sum_le_of_mem_base_set ε0 ε0 h₁.some_spec h₂.some_spec hU]
end

/-- If `f` is integrable on a box `I` along `l`, then for any fixed subset `s` of `I` that can be
represented as a finite union of boxes, the integral sums of `f` over tagged prepartitions that
cover exactly `s` form a Cauchy “sequence” along `l`. -/
theorem cauchy_map_integral_sum_to_filter_Union (h : integrable I l f vol) (π₀ : prepartition I) :
  Cauchy ((l.to_filter_Union I π₀).map (integral_sum f vol)) :=
  by 
    refine' ⟨inferInstance, _⟩
    rw [prod_map_map_eq, ←to_filter_inf_Union_eq, ←prod_inf_prod, prod_principal_principal]
    exact
      h.tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity.mono_left
        (inf_le_inf_left _$ principal_mono.2$ fun π h => h.1.trans h.2.symm)

variable[CompleteSpace F]

theorem to_subbox_aux (h : integrable I l f vol) (hJ : J ≤ I) :
  ∃ y : F,
    has_integral J l f vol y ∧ tendsto (integral_sum f vol) (l.to_filter_Union I (prepartition.single I J hJ)) (𝓝 y) :=
  by 
    refine'
      (cauchy_map_iff_exists_tendsto.1 (h.cauchy_map_integral_sum_to_filter_Union (prepartition.single I J hJ))).imp
        fun y hy => ⟨_, hy⟩
    convert hy.comp (l.tendsto_embed_box_to_filter_Union_top hJ)

/-- If `f` is integrable on a box `I`, then it is integrable on any subbox of `I`. -/
theorem to_subbox (h : integrable I l f vol) (hJ : J ≤ I) : integrable J l f vol :=
  (h.to_subbox_aux hJ).imp$ fun y => And.left

/-- If `f` is integrable on a box `I`, then integral sums of `f` over tagged prepartitions
that cover exactly a subbox `J ≤ I` tend to the integral of `f` over `J` along `l`. -/
theorem tendsto_integral_sum_to_filter_Union_single (h : integrable I l f vol) (hJ : J ≤ I) :
  tendsto (integral_sum f vol) (l.to_filter_Union I (prepartition.single I J hJ)) (𝓝$ integral J l f vol) :=
  let ⟨y, h₁, h₂⟩ := h.to_subbox_aux hJ 
  h₁.integral_eq.symm ▸ h₂

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `box_integral.integrable.convergence_r` instead of a predicate assumption on `r`;
- uses `box_integral.integration_params.mem_base_set` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
- takes an extra argument `π₀ : prepartition I` and an assumption `π.Union = π₀.Union` instead of
  using `π.to_prepartition`.
-/
theorem dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq
(h : integrable I l f vol)
(h0 : «expr < »(0, ε))
(hπ : l.mem_base_set I c (h.convergence_r ε c) π)
{π₀ : prepartition I}
(hU : «expr = »(π.Union, π₀.Union)) : «expr ≤ »(dist (integral_sum f vol π) «expr∑ in , »((J), π₀.boxes, integral J l f vol), ε) :=
begin
  refine [expr le_of_forall_pos_le_add (λ δ δ0, _)],
  set [] [ident δ'] [":", expr exprℝ()] [":="] [expr «expr / »(δ, «expr + »(π₀.boxes.card, 1))] [],
  have [ident H0] [":", expr «expr < »(0, («expr + »(π₀.boxes.card, 1) : exprℝ()))] [":=", expr nat.cast_add_one_pos _],
  have [ident δ'0] [":", expr «expr < »(0, δ')] [":=", expr div_pos δ0 H0],
  set [] [ident C] [] [":="] [expr max π₀.distortion π₀.compl.distortion] [],
  have [] [":", expr ∀
   J «expr ∈ » π₀, «expr∃ , »((πi : tagged_prepartition J), «expr ∧ »(πi.is_partition, «expr ∧ »(«expr ≤ »(dist (integral_sum f vol πi) (integral J l f vol), δ'), l.mem_base_set J C (h.convergence_r δ' C) πi)))] [],
  { intros [ident J, ident hJ],
    have [ident Hle] [":", expr «expr ≤ »(J, I)] [":=", expr π₀.le_of_mem hJ],
    have [ident HJi] [":", expr integrable J l f vol] [":=", expr h.to_subbox Hle],
    set [] [ident r] [] [":="] [expr λ x, min (h.convergence_r δ' C x) (HJi.convergence_r δ' C x)] [],
    have [ident hr] [":", expr l.r_cond r] [],
    from [expr (h.convergence_r_cond _ C).min (HJi.convergence_r_cond _ C)],
    have [ident hJd] [":", expr «expr ≤ »(J.distortion, C)] [],
    from [expr le_trans (finset.le_sup hJ) (le_max_left _ _)],
    rcases [expr l.exists_mem_base_set_is_partition J hJd r, "with", "⟨", ident πJ, ",", ident hC, ",", ident hp, "⟩"],
    have [ident hC₁] [":", expr l.mem_base_set J C (HJi.convergence_r δ' C) πJ] [],
    { refine [expr hC.mono J le_rfl le_rfl (λ x hx, _)],
      exact [expr min_le_right _ _] },
    have [ident hC₂] [":", expr l.mem_base_set J C (h.convergence_r δ' C) πJ] [],
    { refine [expr hC.mono J le_rfl le_rfl (λ x hx, _)],
      exact [expr min_le_left _ _] },
    exact [expr ⟨πJ, hp, HJi.dist_integral_sum_integral_le_of_mem_base_set δ'0 hC₁ hp, hC₂⟩] },
  choose ["!"] [ident πi] [ident hπip, ident hπiδ', ident hπiC] [],
  have [] [":", expr l.mem_base_set I C (h.convergence_r δ' C) (π₀.bUnion_tagged πi)] [],
  from [expr bUnion_tagged_mem_base_set hπiC hπip (λ _, le_max_right _ _)],
  have [ident hU'] [":", expr «expr = »(π.Union, (π₀.bUnion_tagged πi).Union)] [],
  from [expr hU.trans (prepartition.Union_bUnion_partition _ hπip).symm],
  have [] [] [":=", expr h.dist_integral_sum_le_of_mem_base_set h0 δ'0 hπ this hU'],
  rw [expr integral_sum_bUnion_tagged] ["at", ident this],
  calc
    «expr ≤ »(dist (integral_sum f vol π) «expr∑ in , »((J), π₀.boxes, integral J l f vol), «expr + »(dist (integral_sum f vol π) «expr∑ in , »((J), π₀.boxes, integral_sum f vol (πi J)), dist «expr∑ in , »((J), π₀.boxes, integral_sum f vol (πi J)) «expr∑ in , »((J), π₀.boxes, integral J l f vol))) : dist_triangle _ _ _
    «expr ≤ »(..., «expr + »(«expr + »(ε, δ'), «expr∑ in , »((J), π₀.boxes, δ'))) : add_le_add this (dist_sum_sum_le_of_le _ hπiδ')
    «expr = »(..., «expr + »(ε, δ)) : by { field_simp [] ["[", expr H0.ne', "]"] [] [],
      ring [] }
end

/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `box_integral.integrable.convergence_r` instead of a predicate assumption on `r`;
- uses `box_integral.integration_params.mem_base_set` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
-/
theorem dist_integral_sum_sum_integral_le_of_mem_base_set (h : integrable I l f vol) (h0 : 0 < ε)
  (hπ : l.mem_base_set I c (h.convergence_r ε c) π) :
  dist (integral_sum f vol π) (∑J in π.boxes, integral J l f vol) ≤ ε :=
  h.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq h0 hπ rfl

/-- Integral sum of `f` over a tagged prepartition `π` such that `π.Union = π₀.Union` tends to the
sum of integrals of `f` over the boxes of `π₀`. -/
theorem tendsto_integral_sum_sum_integral (h : integrable I l f vol) (π₀ : prepartition I) :
  tendsto (integral_sum f vol) (l.to_filter_Union I π₀) (𝓝$ ∑J in π₀.boxes, integral J l f vol) :=
  by 
    refine' ((l.has_basis_to_filter_Union I π₀).tendsto_iff nhds_basis_closed_ball).2 fun ε ε0 => _ 
    refine' ⟨h.convergence_r ε, h.convergence_r_cond ε, _⟩
    simp only [mem_inter_eq, Set.mem_Union, mem_set_of_eq]
    rintro π ⟨c, hc, hU⟩
    exact h.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq ε0 hc hU

/-- If `f` is integrable on `I`, then `λ J, integral J l f vol` is box-additive on subboxes of `I`:
if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, then the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `box_integral.integrable.to_box_additive` for a bundled version. -/
theorem sum_integral_congr (h : integrable I l f vol) {π₁ π₂ : prepartition I} (hU : π₁.Union = π₂.Union) :
  (∑J in π₁.boxes, integral J l f vol) = ∑J in π₂.boxes, integral J l f vol :=
  by 
    refine' tendsto_nhds_unique (h.tendsto_integral_sum_sum_integral π₁) _ 
    rw [l.to_filter_Union_congr _ hU]
    exact h.tendsto_integral_sum_sum_integral π₂

/-- If `f` is integrable on `I`, then `λ J, integral J l f vol` is box-additive on subboxes of `I`:
if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, then the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `box_integral.integrable.sum_integral_congr` for an unbundled version. -/
@[simps]
def to_box_additive (h : integrable I l f vol) : ι →ᵇᵃ[I] F :=
  { toFun := fun J => integral J l f vol,
    sum_partition_boxes' :=
      fun J hJ π hπ =>
        by 
          replace hπ := hπ.Union_eq 
          rw [←prepartition.Union_top] at hπ 
          rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ, prepartition.top_boxes, sum_singleton] }

end Integrable

open MeasureTheory

/-!
### Integrability conditions
-/


variable(l)

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A continuous function is box-integrable with respect to any locally finite measure.

This is true for any volume with bounded variation. -/
theorem integrable_of_continuous_on
[complete_space E]
{I : box ι}
{f : «exprℝⁿ»() → E}
(hc : continuous_on f I.Icc)
(μ : measure «exprℝⁿ»())
[is_locally_finite_measure μ] : integrable.{u, v, v} I l f μ.to_box_additive.to_smul :=
begin
  have [ident huc] [] [":=", expr I.is_compact_Icc.uniform_continuous_on_of_continuous hc],
  rw [expr metric.uniform_continuous_on_iff_le] ["at", ident huc],
  refine [expr integrable_iff_cauchy_basis.2 (λ ε ε0, _)],
  rcases [expr exists_pos_mul_lt ε0 (μ.to_box_additive I), "with", "⟨", ident ε', ",", ident ε0', ",", ident hε, "⟩"],
  rcases [expr huc ε' ε0', "with", "⟨", ident δ, ",", ident δ0, ":", expr «expr < »(0, δ), ",", ident Hδ, "⟩"],
  refine [expr ⟨λ _ _, ⟨«expr / »(δ, 2), half_pos δ0⟩, λ _ _ _, rfl, λ c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p, _⟩],
  simp [] [] ["only"] ["[", expr dist_eq_norm, ",", expr integral_sum_sub_partitions _ _ h₁p h₂p, ",", expr box_additive_map.to_smul_apply, ",", "<-", expr smul_sub, "]"] [] [],
  have [] [":", expr ∀
   J «expr ∈ » «expr ⊓ »(π₁.to_prepartition, π₂.to_prepartition), «expr ≤ »(«expr∥ ∥»(«expr • »(μ.to_box_additive J, «expr - »(f ((π₁.inf_prepartition π₂.to_prepartition).tag J), f ((π₂.inf_prepartition π₁.to_prepartition).tag J)))), «expr * »(μ.to_box_additive J, ε'))] [],
  { intros [ident J, ident hJ],
    have [] [":", expr «expr ≤ »(0, μ.to_box_additive J)] [],
    from [expr ennreal.to_real_nonneg],
    rw ["[", expr norm_smul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg this, ",", "<-", expr dist_eq_norm, "]"] [],
    refine [expr mul_le_mul_of_nonneg_left _ this],
    refine [expr Hδ _ _ (tagged_prepartition.tag_mem_Icc _ _) (tagged_prepartition.tag_mem_Icc _ _) _],
    rw ["[", "<-", expr add_halves δ, "]"] [],
    refine [expr (dist_triangle_left _ _ J.upper).trans (add_le_add (h₁.1 _ _ _) (h₂.1 _ _ _))],
    { exact [expr prepartition.bUnion_index_mem _ hJ] },
    { exact [expr box.le_iff_Icc.1 (prepartition.le_bUnion_index _ hJ) J.upper_mem_Icc] },
    { rw [expr inf_comm] ["at", ident hJ],
      exact [expr prepartition.bUnion_index_mem _ hJ] },
    { rw [expr inf_comm] ["at", ident hJ],
      exact [expr box.le_iff_Icc.1 (prepartition.le_bUnion_index _ hJ) J.upper_mem_Icc] } },
  refine [expr (norm_sum_le_of_le _ this).trans _],
  rw ["[", "<-", expr finset.sum_mul, ",", expr μ.to_box_additive.sum_partition_boxes le_top (h₁p.inf h₂p), "]"] [],
  exact [expr hε.le]
end

variable{l}

-- error in Analysis.BoxIntegral.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- This is an auxiliary lemma used to prove two statements at once. Use one of the next two
lemmas instead. -/
theorem has_integral_of_bRiemann_eq_ff_of_forall_is_o
(hl : «expr = »(l.bRiemann, ff))
(B : «expr →ᵇᵃ[ ] »(ι, I, exprℝ()))
(hB0 : ∀ J, «expr ≤ »(0, B J))
(g : «expr →ᵇᵃ[ ] »(ι, I, F))
(s : set «exprℝⁿ»())
(hs : s.countable)
(hlH : s.nonempty → «expr = »(l.bHenstock, tt))
(H₁ : ∀
 (c : «exprℝ≥0»())
 (x «expr ∈ » «expr ∩ »(I.Icc, s))
 (ε «expr > » (0 : exprℝ())), «expr∃ , »((δ «expr > » 0), ∀
  J «expr ≤ » I, «expr ⊆ »(J.Icc, metric.closed_ball x δ) → «expr ∈ »(x, J.Icc) → (l.bDistortion → «expr ≤ »(J.distortion, c)) → «expr ≤ »(dist (vol J (f x)) (g J), ε)))
(H₂ : ∀
 (c : «exprℝ≥0»())
 (x «expr ∈ » «expr \ »(I.Icc, s))
 (ε «expr > » (0 : exprℝ())), «expr∃ , »((δ «expr > » 0), ∀
  J «expr ≤ » I, «expr ⊆ »(J.Icc, metric.closed_ball x δ) → (l.bHenstock → «expr ∈ »(x, J.Icc)) → (l.bDistortion → «expr ≤ »(J.distortion, c)) → «expr ≤ »(dist (vol J (f x)) (g J), «expr * »(ε, B J)))) : has_integral I l f vol (g I) :=
begin
  refine [expr ((l.has_basis_to_filter_Union_top _).tendsto_iff metric.nhds_basis_closed_ball).2 _],
  intros [ident ε, ident ε0],
  simp [] [] ["only"] ["[", expr subtype.exists', "]"] [] ["at", ident H₁, ident H₂],
  choose ["!"] [ident δ₁] [ident Hδ₁] ["using", expr H₁],
  choose ["!"] [ident δ₂] [ident Hδ₂] ["using", expr H₂],
  have [ident ε0'] [] [":=", expr half_pos ε0],
  have [ident H0] [":", expr «expr < »(0, («expr ^ »(2, fintype.card ι) : exprℝ()))] [],
  from [expr pow_pos zero_lt_two _],
  rcases [expr hs.exists_pos_forall_sum_le (div_pos ε0' H0), "with", "⟨", ident εs, ",", ident hεs0, ",", ident hεs, "⟩"],
  simp [] [] ["only"] ["[", expr le_div_iff' H0, ",", expr mul_sum, "]"] [] ["at", ident hεs],
  rcases [expr exists_pos_mul_lt ε0' (B I), "with", "⟨", ident ε', ",", ident ε'0, ",", ident hεI, "⟩"],
  set [] [ident δ] [":", expr «exprℝ≥0»() → «exprℝⁿ»() → Ioi (0 : exprℝ())] [":="] [expr λ
   c x, if «expr ∈ »(x, s) then δ₁ c x (εs x) else δ₂ c x ε'] [],
  refine [expr ⟨δ, λ c, l.r_cond_of_bRiemann_eq_ff hl, _⟩],
  simp [] [] ["only"] ["[", expr set.mem_Union, ",", expr mem_inter_eq, ",", expr mem_set_of_eq, "]"] [] [],
  rintro [ident π, "⟨", ident c, ",", ident hπδ, ",", ident hπp, "⟩"],
  rw ["[", "<-", expr g.sum_partition_boxes le_rfl hπp, ",", expr mem_closed_ball, ",", expr integral_sum, ",", "<-", expr sum_filter_add_sum_filter_not π.boxes (λ
    J, «expr ∈ »(π.tag J, s)), ",", "<-", expr sum_filter_add_sum_filter_not π.boxes (λ
    J, «expr ∈ »(π.tag J, s)), ",", "<-", expr add_halves ε, "]"] [],
  refine [expr dist_add_add_le_of_le _ _],
  { unfreezingI { rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", ident hsne] },
    { simp [] [] [] ["[", expr ε0'.le, "]"] [] [] },
    specialize [expr hlH hsne],
    have [] [":", expr ∀
     J «expr ∈ » π.boxes.filter (λ
      J, «expr ∈ »(π.tag J, s)), «expr ≤ »(dist (vol J «expr $ »(f, π.tag J)) (g J), εs (π.tag J))] [],
    { intros [ident J, ident hJ],
      rw [expr finset.mem_filter] ["at", ident hJ],
      cases [expr hJ] ["with", ident hJ, ident hJs],
      refine [expr Hδ₁ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ (hεs0 _) _ (π.le_of_mem' _ hJ) _ (hπδ.2 hlH J hJ) (λ
        hD, (finset.le_sup hJ).trans (hπδ.3 hD))],
      convert [] [expr hπδ.1 J hJ] [],
      exact [expr (dif_pos hJs).symm] },
    refine [expr (dist_sum_sum_le_of_le _ this).trans _],
    rw [expr sum_comp] [],
    refine [expr (sum_le_sum _).trans (hεs _ _)],
    { rintro [ident b, "-"],
      rw ["[", "<-", expr nat.cast_two, ",", "<-", expr nat.cast_pow, ",", "<-", expr nsmul_eq_mul, "]"] [],
      refine [expr nsmul_le_nsmul (hεs0 _).le _],
      refine [expr (finset.card_le_of_subset _).trans ((hπδ.is_Henstock hlH).card_filter_tag_eq_le b)],
      exact [expr filter_subset_filter _ (filter_subset _ _)] },
    { rw ["[", expr finset.coe_image, ",", expr set.image_subset_iff, "]"] [],
      exact [expr λ J hJ, (finset.mem_filter.1 hJ).2] } },
  have [ident H₂] [":", expr ∀
   J «expr ∈ » π.boxes.filter (λ
    J, «expr ∉ »(π.tag J, s)), «expr ≤ »(dist (vol J «expr $ »(f, π.tag J)) (g J), «expr * »(ε', B J))] [],
  { intros [ident J, ident hJ],
    rw [expr finset.mem_filter] ["at", ident hJ],
    cases [expr hJ] ["with", ident hJ, ident hJs],
    refine [expr Hδ₂ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ ε'0 _ (π.le_of_mem' _ hJ) _ (λ
      hH, hπδ.2 hH J hJ) (λ hD, (finset.le_sup hJ).trans (hπδ.3 hD))],
    convert [] [expr hπδ.1 J hJ] [],
    exact [expr (dif_neg hJs).symm] },
  refine [expr (dist_sum_sum_le_of_le _ H₂).trans ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) _).trans _)],
  { exact [expr λ _ _ _, mul_nonneg ε'0.le (hB0 _)] },
  { rw ["[", "<-", expr mul_sum, ",", expr B.sum_partition_boxes le_rfl hπp, ",", expr mul_comm, "]"] [],
    exact [expr hεI.le] }
end

/-- A function `f` has Henstock (or `⊥`) integral over `I` is equal to the value of a box-additive
function `g` on `I` provided that `vol J (f x)` is sufficiently close to `g J` for sufficiently
small boxes `J ∋ x`. This lemma is useful to prove, e.g., to prove the Divergence theorem for
integral along `⊥`.

Let `l` be either `box_integral.integration_params.Henstock` or `⊥`. Let `g` a box-additive function
on subboxes of `I`. Suppose that there exists a nonnegative box-additive function `B` and a
countable set `s` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `x ∈ J.Icc ⊆ metric.closed_ball x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε` if `x ∈ s` and is less than or equal to `ε * B J` otherwise.

Then `f` is integrable on `I along `l` with integral `g I`. -/
theorem has_integral_of_le_Henstock_of_forall_is_o (hl : l ≤ Henstock) (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J)
  (g : ι →ᵇᵃ[I] F) (s : Set ℝⁿ) (hs : s.countable)
  (H₁ :
    ∀ (c :  ℝ≥0 ) x (_ : x ∈ I.Icc ∩ s) ε (_ : ε > (0 : ℝ)),
      ∃ (δ : _)(_ : δ > 0),
        ∀ J (_ : J ≤ I),
          J.Icc ⊆ Metric.ClosedBall x δ → x ∈ J.Icc → (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
  (H₂ :
    ∀ (c :  ℝ≥0 ) x (_ : x ∈ I.Icc \ s) ε (_ : ε > (0 : ℝ)),
      ∃ (δ : _)(_ : δ > 0),
        ∀ J (_ : J ≤ I),
          J.Icc ⊆ Metric.ClosedBall x δ →
            x ∈ J.Icc → (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε*B J) :
  has_integral I l f vol (g I) :=
  have A : l.bHenstock :=
    hl.2.1.resolve_left
      (by 
        decide)
  has_integral_of_bRiemann_eq_ff_of_forall_is_o
      (hl.1.resolve_right
        (by 
          decide))
      B hB0 _ s hs (fun _ => A) H₁$
    by 
      simpa only [A, true_implies_iff] using H₂

/-- Suppose that there exists a nonnegative box-additive function `B` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `J.Icc ⊆ metric.closed_ball x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε * B J`.

Then `f` is McShane integrable on `I` with integral `g I`. -/
theorem has_integral_McShane_of_forall_is_o (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F)
  (H :
    ∀ (c :  ℝ≥0 ) x (_ : x ∈ I.Icc) ε (_ : ε > (0 : ℝ)),
      ∃ (δ : _)(_ : δ > 0), ∀ J (_ : J ≤ I), J.Icc ⊆ Metric.ClosedBall x δ → dist (vol J (f x)) (g J) ≤ ε*B J) :
  has_integral I McShane f vol (g I) :=
  (has_integral_of_bRiemann_eq_ff_of_forall_is_o rfl B hB0 g ∅ countable_empty (fun ⟨x, hx⟩ => hx.elim)
      fun c x hx => hx.2.elim)$
    by 
      simpa only [McShane, coe_sort_ff, false_implies_iff, true_implies_iff, diff_empty] using H

end BoxIntegral

