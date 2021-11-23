import Mathbin.MeasureTheory.Integral.Lebesgue 
import Mathbin.MeasureTheory.Measure.Regular 
import Mathbin.MeasureTheory.Group.MeasurableEquiv

/-!
# Measures on Groups

We develop some properties of measures on (topological) groups

* We define properties on measures: left and right invariant measures.
* We define the measure `μ.inv : A ↦ μ(A⁻¹)` and show that it is right invariant iff
  `μ` is left invariant.
* We define a class `is_haar_measure μ`, requiring that the measure `μ` is left-invariant, finite
  on compact sets, and positive on open sets.

We also give analogues of all these notions in the additive world.
-/


noncomputable theory

open_locale Ennreal Pointwise BigOperators

open HasInv Set Function MeasureTheory.Measure

namespace MeasureTheory

variable{G : Type _}

section 

variable[MeasurableSpace G][Mul G]

/-- A measure `μ` on a topological group is left invariant
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left multiplication,
  since preimages are nicer to work with than images. -/
@[toAdditive
      "A measure on a topological group is left invariant\n  if the measure of left translations of a set are equal to the measure of the set itself.\n  To left translate sets we use preimage under left addition,\n  since preimages are nicer to work with than images."]
def is_mul_left_invariant (μ : Set G → ℝ≥0∞) : Prop :=
  ∀ g : G {A : Set G} h : MeasurableSet A, μ ((fun h => g*h) ⁻¹' A) = μ A

/-- A measure `μ` on a topological group is right invariant
  if the measure of right translations of a set are equal to the measure of the set itself.
  To right translate sets we use preimage under right multiplication,
  since preimages are nicer to work with than images. -/
@[toAdditive
      "A measure on a topological group is right invariant\n  if the measure of right translations of a set are equal to the measure of the set itself.\n  To right translate sets we use preimage under right addition,\n  since preimages are nicer to work with than images."]
def is_mul_right_invariant (μ : Set G → ℝ≥0∞) : Prop :=
  ∀ g : G {A : Set G} h : MeasurableSet A, μ ((fun h => h*g) ⁻¹' A) = μ A

@[toAdditive MeasureTheory.IsAddLeftInvariant.smul]
theorem is_mul_left_invariant.smul {μ : Measureₓ G} (h : is_mul_left_invariant μ) (c : ℝ≥0∞) :
  is_mul_left_invariant ((c • μ : Measureₓ G) : Set G → ℝ≥0∞) :=
  fun g A hA =>
    by 
      rw [smul_apply, smul_apply, h g hA]

@[toAdditive MeasureTheory.IsAddRightInvariant.smul]
theorem is_mul_right_invariant.smul {μ : Measureₓ G} (h : is_mul_right_invariant μ) (c : ℝ≥0∞) :
  is_mul_right_invariant ((c • μ : Measureₓ G) : Set G → ℝ≥0∞) :=
  fun g A hA =>
    by 
      rw [smul_apply, smul_apply, h g hA]

end 

namespace Measureₓ

variable[MeasurableSpace G]

@[toAdditive]
theorem map_mul_left_eq_self [TopologicalSpace G] [Mul G] [HasContinuousMul G] [BorelSpace G] {μ : Measureₓ G} :
  (∀ g, measure.map ((·*·) g) μ = μ) ↔ is_mul_left_invariant μ :=
  by 
    apply forall_congrₓ 
    intro g 
    rw [measure.ext_iff]
    apply forall_congrₓ 
    intro A 
    apply forall_congrₓ 
    intro hA 
    rw [map_apply (measurable_const_mul g) hA]

@[toAdditive]
theorem _root_.measure_theory.is_mul_left_invariant.measure_preimage_mul [TopologicalSpace G] [Groupₓ G]
  [TopologicalGroup G] [BorelSpace G] {μ : Measureₓ G} (h : is_mul_left_invariant μ) (g : G) (A : Set G) :
  μ ((fun h => g*h) ⁻¹' A) = μ A :=
  calc μ ((fun h => g*h) ⁻¹' A) = measure.map (fun h => g*h) μ A :=
    ((Homeomorph.mulLeft g).toMeasurableEquiv.map_apply A).symm 
    _ = μ A :=
    by 
      rw [map_mul_left_eq_self.2 h g]
    

@[toAdditive]
theorem map_mul_right_eq_self [TopologicalSpace G] [Mul G] [HasContinuousMul G] [BorelSpace G] {μ : Measureₓ G} :
  (∀ g, measure.map (fun h => h*g) μ = μ) ↔ is_mul_right_invariant μ :=
  by 
    apply forall_congrₓ 
    intro g 
    rw [measure.ext_iff]
    apply forall_congrₓ 
    intro A 
    apply forall_congrₓ 
    intro hA 
    rw [map_apply (measurable_mul_const g) hA]

/-- The measure `A ↦ μ (A⁻¹)`, where `A⁻¹` is the pointwise inverse of `A`. -/
@[toAdditive "The measure `A ↦ μ (- A)`, where `- A` is the pointwise negation of `A`."]
protected def inv [HasInv G] (μ : Measureₓ G) : Measureₓ G :=
  measure.map inv μ

variable[Groupₓ G][TopologicalSpace G][TopologicalGroup G][BorelSpace G]

@[toAdditive]
theorem inv_apply (μ : Measureₓ G) (s : Set G) : μ.inv s = μ (s⁻¹) :=
  (MeasurableEquiv.inv G).map_apply s

@[simp, toAdditive]
protected theorem inv_invₓ (μ : Measureₓ G) : μ.inv.inv = μ :=
  (MeasurableEquiv.inv G).map_symm_map

variable{μ : Measureₓ G}

@[toAdditive]
instance regular.inv [T2Space G] [regular μ] : regular μ.inv :=
  regular.map (Homeomorph.inv G)

end Measureₓ

section Inv

variable[MeasurableSpace G][Groupₓ G][TopologicalSpace G][TopologicalGroup G][BorelSpace G]{μ : Measureₓ G}

@[simp, toAdditive]
theorem regular_inv_iff [T2Space G] : μ.inv.regular ↔ μ.regular :=
  by 
    split 
    ·
      intro h 
      rw [←μ.inv_inv]
      exact measure.regular.inv
    ·
      intro h 
      exact measure.regular.inv

@[toAdditive]
theorem is_mul_left_invariant.inv (h : is_mul_left_invariant μ) : is_mul_right_invariant μ.inv :=
  by 
    intro g A hA 
    rw [μ.inv_apply, μ.inv_apply]
    convert h (g⁻¹) (measurable_inv hA) using 2
    simp only [←preimage_comp, ←inv_preimage]
    apply preimage_congr 
    intro h 
    simp only [mul_inv_rev, comp_app, inv_invₓ]

@[toAdditive]
theorem is_mul_right_invariant.inv (h : is_mul_right_invariant μ) : is_mul_left_invariant μ.inv :=
  by 
    intro g A hA 
    rw [μ.inv_apply, μ.inv_apply]
    convert h (g⁻¹) (measurable_inv hA) using 2
    simp only [←preimage_comp, ←inv_preimage]
    apply preimage_congr 
    intro h 
    simp only [mul_inv_rev, comp_app, inv_invₓ]

@[simp, toAdditive]
theorem is_mul_right_invariant_inv : is_mul_right_invariant μ.inv ↔ is_mul_left_invariant μ :=
  ⟨fun h =>
      by 
        rw [←μ.inv_inv]
        exact h.inv,
    fun h => h.inv⟩

@[simp, toAdditive]
theorem is_mul_left_invariant_inv : is_mul_left_invariant μ.inv ↔ is_mul_right_invariant μ :=
  ⟨fun h =>
      by 
        rw [←μ.inv_inv]
        exact h.inv,
    fun h => h.inv⟩

end Inv

section Groupₓ

variable[MeasurableSpace G][TopologicalSpace G][BorelSpace G]{μ : Measureₓ G}

variable[Groupₓ G][TopologicalGroup G]

/-- If a left-invariant measure gives positive mass to a compact set, then
it gives positive mass to any open set. -/
@[toAdditive]
theorem is_mul_left_invariant.measure_pos_of_is_open (hμ : is_mul_left_invariant μ) (K : Set G) (hK : IsCompact K)
  (h : μ K ≠ 0) {U : Set G} (hU : IsOpen U) (h'U : U.nonempty) : 0 < μ U :=
  by 
    contrapose! h 
    rw [←nonpos_iff_eq_zero]
    rw [nonpos_iff_eq_zero] at h 
    rw [←hU.interior_eq] at h'U 
    obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃(g : G)(H : g ∈ t), (fun h : G => g*h) ⁻¹' U :=
      compact_covered_by_mul_left_translates hK h'U 
    calc μ K ≤ μ (⋃(g : G)(H : g ∈ t), (fun h : G => g*h) ⁻¹' U) :=
      measure_mono hKt _ ≤ ∑g in t, μ ((fun h : G => g*h) ⁻¹' U) := measure_bUnion_finset_le _ _ _ = 0 :=
      by 
        simp [hμ _ hU.measurable_set, h]

/-! A nonzero left-invariant regular measure gives positive mass to any open set. -/


@[toAdditive]
theorem is_mul_left_invariant.null_iff_empty [regular μ] (hμ : is_mul_left_invariant μ) (h3μ : μ ≠ 0) {s : Set G}
  (hs : IsOpen s) : μ s = 0 ↔ s = ∅ :=
  by 
    obtain ⟨K, hK, h2K⟩ := regular.exists_compact_not_null.mpr h3μ 
    refine'
      ⟨fun h => _,
        fun h =>
          by 
            simp only [h, measure_empty]⟩
    contrapose h 
    exact (hμ.measure_pos_of_is_open K hK h2K hs (ne_empty_iff_nonempty.mp h)).ne'

@[toAdditive]
theorem is_mul_left_invariant.null_iff [regular μ] (h2μ : is_mul_left_invariant μ) {s : Set G} (hs : IsOpen s) :
  μ s = 0 ↔ s = ∅ ∨ μ = 0 :=
  by 
    byCases' h3μ : μ = 0
    ·
      simp [h3μ]
    simp only [h3μ, or_falseₓ]
    exact h2μ.null_iff_empty h3μ hs

@[toAdditive]
theorem is_mul_left_invariant.measure_ne_zero_iff_nonempty [regular μ] (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0)
  {s : Set G} (hs : IsOpen s) : μ s ≠ 0 ↔ s.nonempty :=
  by 
    simpRw [←ne_empty_iff_nonempty, Ne.def, h2μ.null_iff_empty h3μ hs]

@[toAdditive]
theorem is_mul_left_invariant.measure_pos_iff_nonempty [regular μ] (h2μ : is_mul_left_invariant μ) (h3μ : μ ≠ 0)
  {s : Set G} (hs : IsOpen s) : 0 < μ s ↔ s.nonempty :=
  pos_iff_ne_zero.trans$ h2μ.measure_ne_zero_iff_nonempty h3μ hs

/-- If a left-invariant measure gives finite mass to a nonempty open set, then
it gives finite mass to any compact set. -/
@[toAdditive]
theorem is_mul_left_invariant.measure_lt_top_of_is_compact (hμ : is_mul_left_invariant μ) (U : Set G) (hU : IsOpen U)
  (h'U : U.nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  by 
    rw [←hU.interior_eq] at h'U 
    obtain ⟨t, hKt⟩ : ∃ t : Finset G, K ⊆ ⋃(g : G)(H : g ∈ t), (fun h : G => g*h) ⁻¹' U :=
      compact_covered_by_mul_left_translates hK h'U 
    calc μ K ≤ μ (⋃(g : G)(H : g ∈ t), (fun h : G => g*h) ⁻¹' U) :=
      measure_mono hKt _ ≤ ∑g in t, μ ((fun h : G => g*h) ⁻¹' U) :=
      measure_bUnion_finset_le _ _ _ = Finset.card t*μ U :=
      by 
        simp only [hμ _ hU.measurable_set, Finset.sum_const, nsmul_eq_mul]_ < ∞ :=
      Ennreal.mul_lt_top Ennreal.coe_nat_ne_top h

/-- If a left-invariant measure gives finite mass to a set with nonempty interior, then
it gives finite mass to any compact set. -/
@[toAdditive]
theorem is_mul_left_invariant.measure_lt_top_of_is_compact' (hμ : is_mul_left_invariant μ) (U : Set G)
  (hU : (Interior U).Nonempty) (h : μ U ≠ ∞) {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  hμ.measure_lt_top_of_is_compact (Interior U) is_open_interior hU
    ((measure_mono interior_subset).trans_lt (lt_top_iff_ne_top.2 h)).Ne hK

-- error in MeasureTheory.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For nonzero regular left invariant measures, the integral of a continuous nonnegative function
  `f` is 0 iff `f` is 0. -/
@[to_additive #[]]
theorem lintegral_eq_zero_of_is_mul_left_invariant
[regular μ]
(h2μ : is_mul_left_invariant μ)
(h3μ : «expr ≠ »(μ, 0))
{f : G → «exprℝ≥0∞»()}
(hf : continuous f) : «expr ↔ »(«expr = »(«expr∫⁻ , ∂ »((x), f x, μ), 0), «expr = »(f, 0)) :=
begin
  split,
  swap,
  { rintro [ident rfl],
    simp_rw ["[", expr pi.zero_apply, ",", expr lintegral_zero, "]"] [] },
  intro [ident h],
  contrapose [] [ident h],
  simp_rw ["[", expr funext_iff, ",", expr not_forall, ",", expr pi.zero_apply, "]"] ["at", ident h],
  cases [expr h] ["with", ident x, ident hx],
  obtain ["⟨", ident r, ",", ident h1r, ",", ident h2r, "⟩", ":", expr «expr∃ , »((r : «exprℝ≥0∞»()), «expr ∧ »(«expr < »(0, r), «expr < »(r, f x))), ":=", expr exists_between (pos_iff_ne_zero.mpr hx)],
  have [ident h3r] [] [":=", expr hf.is_open_preimage (Ioi r) is_open_Ioi],
  let [ident s] [] [":=", expr Ioi r],
  rw ["[", "<-", expr ne.def, ",", "<-", expr pos_iff_ne_zero, "]"] [],
  have [] [":", expr «expr < »(0, «expr * »(r, μ «expr ⁻¹' »(f, Ioi r)))] [],
  { have [] [":", expr «expr ⁻¹' »(f, Ioi r).nonempty] [],
    from [expr ⟨x, h2r⟩],
    simpa [] [] [] ["[", expr h1r.ne', ",", expr h2μ.measure_pos_iff_nonempty h3μ h3r, ",", expr h1r, "]"] [] [] },
  refine [expr this.trans_le _],
  rw ["[", "<-", expr set_lintegral_const, ",", "<-", expr lintegral_indicator _ h3r.measurable_set, "]"] [],
  apply [expr lintegral_mono],
  refine [expr indicator_le (λ y, le_of_lt)]
end

end Groupₓ

section Integration

variable[MeasurableSpace G][TopologicalSpace G][BorelSpace G]{μ : Measureₓ G}

variable[Groupₓ G][HasContinuousMul G]

open Measureₓ

-- error in MeasureTheory.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Translating a function by left-multiplication does not change its `lintegral` with respect to
a left-invariant measure. -/
@[to_additive #[]]
theorem lintegral_mul_left_eq_self
(hμ : is_mul_left_invariant μ)
(f : G → «exprℝ≥0∞»())
(g : G) : «expr = »(«expr∫⁻ , ∂ »((x), f «expr * »(g, x), μ), «expr∫⁻ , ∂ »((x), f x, μ)) :=
begin
  have [] [":", expr «expr = »(measure.map (has_mul.mul g) μ, μ)] [],
  { rw ["<-", expr map_mul_left_eq_self] ["at", ident hμ],
    exact [expr hμ g] },
  convert [] [expr (lintegral_map_equiv f (homeomorph.mul_left g).to_measurable_equiv).symm] [],
  simp [] [] [] ["[", expr this, "]"] [] []
end

-- error in MeasureTheory.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Translating a function by right-multiplication does not change its `lintegral` with respect to
a right-invariant measure. -/
@[to_additive #[]]
theorem lintegral_mul_right_eq_self
(hμ : is_mul_right_invariant μ)
(f : G → «exprℝ≥0∞»())
(g : G) : «expr = »(«expr∫⁻ , ∂ »((x), f «expr * »(x, g), μ), «expr∫⁻ , ∂ »((x), f x, μ)) :=
begin
  have [] [":", expr «expr = »(measure.map (homeomorph.mul_right g) μ, μ)] [],
  { rw ["<-", expr map_mul_right_eq_self] ["at", ident hμ],
    exact [expr hμ g] },
  convert [] [expr (lintegral_map_equiv f (homeomorph.mul_right g).to_measurable_equiv).symm] [],
  simp [] [] [] ["[", expr this, "]"] [] []
end

end Integration

section Haar

namespace Measureₓ

/-- A measure on a group is a Haar measure if it is left-invariant, and gives finite mass to compact
sets and positive mass to open sets. -/
class is_haar_measure{G : Type _}[Groupₓ G][TopologicalSpace G][MeasurableSpace G](μ : Measureₓ G) : Prop where 
  left_invariant : is_mul_left_invariant μ 
  compact_lt_top : ∀ K : Set G, IsCompact K → μ K < ∞
  open_pos : ∀ U : Set G, IsOpen U → U.nonempty → 0 < μ U

/-- A measure on an additive group is an additive Haar measure if it is left-invariant, and gives
finite mass to compact sets and positive mass to open sets. -/
class is_add_haar_measure{G : Type _}[AddGroupₓ G][TopologicalSpace G][MeasurableSpace G](μ : Measureₓ G) : Prop where 
  add_left_invariant : is_add_left_invariant μ 
  compact_lt_top : ∀ K : Set G, IsCompact K → μ K < ∞
  open_pos : ∀ U : Set G, IsOpen U → U.nonempty → 0 < μ U

attribute [toAdditive] is_haar_measure

section 

variable[Groupₓ G][MeasurableSpace G][TopologicalSpace G](μ : Measureₓ G)[is_haar_measure μ]

@[toAdditive]
theorem _root_.is_compact.haar_lt_top {K : Set G} (hK : IsCompact K) : μ K < ∞ :=
  is_haar_measure.compact_lt_top K hK

@[toAdditive]
theorem _root_.is_open.haar_pos {U : Set G} (hU : IsOpen U) (h'U : U.nonempty) : 0 < μ U :=
  is_haar_measure.open_pos U hU h'U

@[toAdditive]
theorem haar_pos_of_nonempty_interior {U : Set G} (hU : (Interior U).Nonempty) : 0 < μ U :=
  lt_of_lt_of_leₓ (is_open_interior.haar_pos μ hU) (measure_mono interior_subset)

@[toAdditive]
theorem is_mul_left_invariant_haar : is_mul_left_invariant μ :=
  is_haar_measure.left_invariant

@[simp, toAdditive]
theorem haar_preimage_mul [TopologicalGroup G] [BorelSpace G] (g : G) (A : Set G) : μ ((fun h => g*h) ⁻¹' A) = μ A :=
  (is_mul_left_invariant_haar μ).measure_preimage_mul _ _

@[simp, toAdditive]
theorem haar_singleton [TopologicalGroup G] [BorelSpace G] (g : G) : μ {g} = μ {(1 : G)} :=
  by 
    convert haar_preimage_mul μ (g⁻¹) _ 
    simp only [mul_oneₓ, preimage_mul_left_singleton, inv_invₓ]

@[simp, toAdditive]
theorem haar_preimage_mul_right {G : Type _} [CommGroupₓ G] [MeasurableSpace G] [TopologicalSpace G] (μ : Measureₓ G)
  [is_haar_measure μ] [TopologicalGroup G] [BorelSpace G] (g : G) (A : Set G) : μ ((fun h => h*g) ⁻¹' A) = μ A :=
  by 
    simpRw [mul_commₓ, haar_preimage_mul μ g A]

@[toAdditive MeasureTheory.Measure.IsAddHaarMeasure.smul]
theorem is_haar_measure.smul {c : ℝ≥0∞} (cpos : c ≠ 0) (ctop : c ≠ ∞) : is_haar_measure (c • μ) :=
  { left_invariant := (is_mul_left_invariant_haar μ).smul _,
    compact_lt_top :=
      fun K hK =>
        by 
          change (c*μ K) < ∞
          simp [lt_top_iff_ne_top, (hK.haar_lt_top μ).Ne, cpos, ctop],
    open_pos :=
      fun U U_open U_ne =>
        bot_lt_iff_ne_bot.2$
          by 
            change (c*μ U) ≠ 0
            simp [cpos, (_root_.is_open.haar_pos μ U_open U_ne).ne'] }

/-- If a left-invariant measure gives positive mass to some compact set with nonempty interior, then
it is a Haar measure -/
@[toAdditive]
theorem is_haar_measure_of_is_compact_nonempty_interior [TopologicalGroup G] [BorelSpace G] (μ : Measureₓ G)
  (hμ : is_mul_left_invariant μ) (K : Set G) (hK : IsCompact K) (h'K : (Interior K).Nonempty) (h : μ K ≠ 0)
  (h' : μ K ≠ ∞) : is_haar_measure μ :=
  { left_invariant := hμ, compact_lt_top := fun L hL => hμ.measure_lt_top_of_is_compact' _ h'K h' hL,
    open_pos := fun U hU => hμ.measure_pos_of_is_open K hK h hU }

-- error in MeasureTheory.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The image of a Haar measure under a group homomorphism which is also a homeomorphism is again
a Haar measure. -/
@[to_additive #[]]
theorem is_haar_measure_map
[borel_space G]
[topological_group G]
{H : Type*}
[group H]
[topological_space H]
[measurable_space H]
[borel_space H]
[t2_space H]
[topological_group H]
(f : «expr ≃* »(G, H))
(hf : continuous f)
(hfsymm : continuous f.symm) : is_haar_measure (measure.map f μ) :=
{ left_invariant := begin
    rw ["<-", expr map_mul_left_eq_self] [],
    assume [binders (h)],
    rw [expr map_map (continuous_mul_left h).measurable hf.measurable] [],
    conv_rhs [] [] { rw ["<-", expr map_mul_left_eq_self.2 (is_mul_left_invariant_haar μ) (f.symm h)] },
    rw [expr map_map hf.measurable (continuous_mul_left _).measurable] [],
    congr' [2] [],
    ext [] [ident y] [],
    simp [] [] ["only"] ["[", expr mul_equiv.apply_symm_apply, ",", expr comp_app, ",", expr mul_equiv.map_mul, "]"] [] []
  end,
  compact_lt_top := begin
    assume [binders (K hK)],
    rw [expr map_apply hf.measurable hK.measurable_set] [],
    have [] [":", expr «expr = »(«expr '' »(f.symm, K), «expr ⁻¹' »(f, K))] [":=", expr equiv.image_eq_preimage _ _],
    rw ["<-", expr this] [],
    exact [expr is_compact.haar_lt_top _ (hK.image hfsymm)]
  end,
  open_pos := begin
    assume [binders (U hU h'U)],
    rw [expr map_apply hf.measurable hU.measurable_set] [],
    refine [expr (hU.preimage hf).haar_pos _ _],
    have [] [":", expr «expr = »(«expr '' »(f.symm, U), «expr ⁻¹' »(f, U))] [":=", expr equiv.image_eq_preimage _ _],
    rw ["<-", expr this] [],
    simp [] [] [] ["[", expr h'U, "]"] [] []
  end }

/-- A Haar measure on a sigma-compact space is sigma-finite. -/
@[toAdditive]
instance (priority := 100)is_haar_measure.sigma_finite {G : Type _} [Groupₓ G] [MeasurableSpace G] [TopologicalSpace G]
  [SigmaCompactSpace G] (μ : Measureₓ G) [μ.is_haar_measure] : sigma_finite μ :=
  ⟨⟨{ Set := CompactCovering G, set_mem := fun n => mem_univ _,
        Finite := fun n => IsCompact.haar_lt_top μ$ is_compact_compact_covering G n,
        spanning := Union_compact_covering G }⟩⟩

open_locale TopologicalSpace

open Filter

-- error in MeasureTheory.Group.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the neutral element of a group is not isolated, then a Haar measure on this group has
no atom.

This applies in particular to show that an additive Haar measure on a nontrivial
finite-dimensional real vector space has no atom. -/
@[priority 100, to_additive #[]]
instance is_haar_measure.has_no_atoms
{G : Type*}
[group G]
[measurable_space G]
[topological_space G]
[t1_space G]
[topological_group G]
[locally_compact_space G]
[borel_space G]
[«expr𝓝[ ] »(«expr ᶜ»({(1 : G)}), (1 : G)).ne_bot]
(μ : measure G)
[μ.is_haar_measure] : has_no_atoms μ :=
begin
  suffices [ident H] [":", expr «expr ≤ »(μ {(1 : G)}, 0)],
  by { constructor,
    simp [] [] [] ["[", expr le_bot_iff.1 H, "]"] [] [] },
  obtain ["⟨", ident K, ",", ident K_compact, ",", ident K_int, "⟩", ":", expr «expr∃ , »((K : set G), «expr ∧ »(is_compact K, «expr ∈ »((1 : G), interior K)))],
  { rcases [expr exists_compact_subset is_open_univ (mem_univ (1 : G)), "with", "⟨", ident K, ",", ident hK, "⟩"],
    exact [expr ⟨K, hK.1, hK.2.1⟩] },
  have [ident K_inf] [":", expr set.infinite K] [":=", expr infinite_of_mem_nhds (1 : G) (mem_interior_iff_mem_nhds.1 K_int)],
  have [ident μKlt] [":", expr «expr ≠ »(μ K, «expr∞»())] [":=", expr (K_compact.haar_lt_top μ).ne],
  have [ident I] [":", expr ∀ n : exprℕ(), «expr ≤ »(μ {(1 : G)}, «expr / »(μ K, n))] [],
  { assume [binders (n)],
    obtain ["⟨", ident t, ",", ident tK, ",", ident tn, "⟩", ":", expr «expr∃ , »((t : finset G), «expr ∧ »(«expr ⊆ »(«expr↑ »(t), K), «expr = »(t.card, n))), ":=", expr K_inf.exists_subset_card_eq n],
    have [ident A] [":", expr «expr ≤ »(μ t, μ K)] [":=", expr measure_mono tK],
    have [ident B] [":", expr «expr = »(μ t, «expr * »(n, μ {(1 : G)}))] [],
    { rw ["<-", expr bUnion_of_singleton «expr↑ »(t)] [],
      change [expr «expr = »(μ «expr⋃ , »((x «expr ∈ » t), {x}), «expr * »(n, μ {1}))] [] [],
      rw [expr @measure_bUnion_finset G G _ μ t (λ i, {i})] [],
      { simp [] [] ["only"] ["[", expr tn, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr haar_singleton, "]"] [] [] },
      { assume [binders (x hx y hy xy)],
        simp [] [] ["only"] ["[", expr on_fun, ",", expr xy.symm, ",", expr mem_singleton_iff, ",", expr not_false_iff, ",", expr disjoint_singleton_right, "]"] [] [] },
      { assume [binders (b hb)],
        exact [expr measurable_set_singleton b] } },
    rw [expr B] ["at", ident A],
    rwa ["[", expr ennreal.le_div_iff_mul_le _ (or.inr μKlt), ",", expr mul_comm, "]"] [],
    right,
    apply [expr ne_of_gt (haar_pos_of_nonempty_interior μ ⟨_, K_int⟩)] },
  have [ident J] [":", expr tendsto (λ
    n : exprℕ(), «expr / »(μ K, n)) at_top (expr𝓝() «expr / »(μ K, «expr∞»()))] [":=", expr ennreal.tendsto.const_div ennreal.tendsto_nat_nhds_top (or.inr μKlt)],
  simp [] [] ["only"] ["[", expr ennreal.div_top, "]"] [] ["at", ident J],
  exact [expr ge_of_tendsto' J I]
end

example  {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] (μ : Measureₓ E) [is_add_haar_measure μ] : has_no_atoms μ :=
  by 
    infer_instance

end 

end Measureₓ

end Haar

end MeasureTheory

