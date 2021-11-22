import Mathbin.MeasureTheory.Constructions.BorelSpace

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corrresponding measure, giving mass `f b - f a` to the interval `(a, b]`.

## Main definitions

* `stieltjes_function` is a structure containing a function from `ℝ → ℝ`, together with the
assertions that it is monotone and right-continuous. To `f : stieltjes_function`, one associates
a Borel measure `f.measure`.
* `f.left_lim x` is the limit of `f` to the left of `x`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = of_real (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = of_real (f.left_lim b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
-/


noncomputable theory

open Classical Set Filter

open ennreal(ofReal)

open_locale BigOperators Ennreal Nnreal TopologicalSpace

/-! ### Basic properties of Stieltjes functions -/


/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
structure StieltjesFunction where 
  toFun : ℝ → ℝ 
  mono' : Monotone to_fun 
  right_continuous' : ∀ x, ContinuousWithinAt to_fun (Ici x) x

namespace StieltjesFunction

instance  : CoeFun StieltjesFunction fun _ => ℝ → ℝ :=
  ⟨to_fun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)

variable(f : StieltjesFunction)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

/-- The limit of a Stieltjes function to the left of `x` (it exists by monotonicity). The fact that
it is indeed a left limit is asserted in `tendsto_left_lim` -/
@[irreducible]
def left_lim (x : ℝ) :=
  Sup (f '' Iio x)

theorem tendsto_left_lim (x : ℝ) : tendsto f (𝓝[Iio x] x) (𝓝 (f.left_lim x)) :=
  by 
    rw [left_lim]
    exact f.mono.tendsto_nhds_within_Iio x

theorem left_lim_le {x y : ℝ} (h : x ≤ y) : f.left_lim x ≤ f y :=
  by 
    apply le_of_tendsto (f.tendsto_left_lim x)
    filterUpwards [self_mem_nhds_within]
    intro z hz 
    exact (f.mono (le_of_ltₓ hz)).trans (f.mono h)

theorem le_left_lim {x y : ℝ} (h : x < y) : f x ≤ f.left_lim y :=
  by 
    apply ge_of_tendsto (f.tendsto_left_lim y)
    apply mem_nhds_within_Iio_iff_exists_Ioo_subset.2 ⟨x, h, _⟩
    intro z hz 
    exact f.mono hz.1.le

theorem left_lim_le_left_lim {x y : ℝ} (h : x ≤ y) : f.left_lim x ≤ f.left_lim y :=
  by 
    rcases eq_or_lt_of_le h with (rfl | hxy)
    ·
      exact le_rfl
    ·
      exact (f.left_lim_le le_rfl).trans (f.le_left_lim hxy)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
protected def id : StieltjesFunction :=
  { toFun := id, mono' := fun x y => id, right_continuous' := fun x => continuous_within_at_id }

@[simp]
theorem id_left_lim (x : ℝ) : StieltjesFunction.id.leftLim x = x :=
  tendsto_nhds_unique (StieltjesFunction.id.tendsto_left_lim x)$ continuous_at_id.Tendsto.mono_left nhds_within_le_nhds

instance  : Inhabited StieltjesFunction :=
  ⟨StieltjesFunction.id⟩

/-! ### The outer measure associated to a Stieltjes function -/


/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
def length (s : Set ℝ) : ℝ≥0∞ :=
  ⨅(a b : _)(h : s ⊆ Ioc a b), of_real (f b - f a)

@[simp]
theorem length_empty : f.length ∅ = 0 :=
  nonpos_iff_eq_zero.1$
    infi_le_of_le 0$
      infi_le_of_le 0$
        by 
          simp 

@[simp]
theorem length_Ioc (a b : ℝ) : f.length (Ioc a b) = of_real (f b - f a) :=
  by 
    refine'
      le_antisymmₓ (infi_le_of_le a$ binfi_le b (subset.refl _))
        (le_infi$ fun a' => le_infi$ fun b' => le_infi$ fun h => Ennreal.coe_le_coe.2 _)
    cases' le_or_ltₓ b a with ab ab
    ·
      rw [Real.to_nnreal_of_nonpos (sub_nonpos.2 (f.mono ab))]
      apply zero_le 
    cases' (Ioc_subset_Ioc_iff ab).1 h with h₁ h₂ 
    exact Real.to_nnreal_le_to_nnreal (sub_le_sub (f.mono h₁) (f.mono h₂))

theorem length_mono {s₁ s₂ : Set ℝ} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ :=
  infi_le_infi$ fun a => infi_le_infi$ fun b => infi_le_infi2$ fun h' => ⟨subset.trans h h', le_reflₓ _⟩

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
protected def outer : outer_measure ℝ :=
  outer_measure.of_function f.length f.length_empty

theorem outer_le_length (s : Set ℝ) : f.outer s ≤ f.length s :=
  outer_measure.of_function_le _

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo {a b : ℝ} {c d : ℕ → ℝ} (ss : Icc a b ⊆ ⋃i, Ioo (c i) (d i)) :
  of_real (f b - f a) ≤ ∑'i, of_real (f (d i) - f (c i)) :=
  by 
    suffices  :
      ∀ s : Finset ℕ b cv : Icc a b ⊆ ⋃(i : _)(_ : i ∈ («expr↑ » s : Set ℕ)), Ioo (c i) (d i),
        (of_real (f b - f a) : ℝ≥0∞) ≤ ∑i in s, of_real (f (d i) - f (c i))
    ·
      rcases
        is_compact_Icc.elim_finite_subcover_image (fun i : ℕ _ : i ∈ univ => @is_open_Ioo _ _ _ _ (c i) (d i))
          (by 
            simpa using ss) with
        ⟨s, su, hf, hs⟩
      have e :
        (⋃(i : _)(_ : i ∈ («expr↑ » hf.to_finset : Set ℕ)), Ioo (c i) (d i)) = ⋃(i : _)(_ : i ∈ s), Ioo (c i) (d i)
      ·
        simp only [ext_iff, exists_prop, Finset.set_bUnion_coe, mem_Union, forall_const, iff_selfₓ,
          finite.mem_to_finset]
      rw [Ennreal.tsum_eq_supr_sum]
      refine' le_transₓ _ (le_supr _ hf.to_finset)
      exact
        this hf.to_finset _
          (by 
            simpa only [e])
    clear ss b 
    refine' fun s => Finset.strongInductionOn s fun s IH b cv => _ 
    cases' le_totalₓ b a with ab ab
    ·
      rw [Ennreal.of_real_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
      exact zero_le _ 
    have  := cv ⟨ab, le_reflₓ _⟩
    simp  at this 
    rcases this with ⟨i, is, cb, bd⟩
    rw [←Finset.insert_erase is] at cv⊢
    rw [Finset.coe_insert, bUnion_insert] at cv 
    rw [Finset.sum_insert (Finset.not_mem_erase _ _)]
    refine' le_transₓ _ (add_le_add_left (IH _ (Finset.erase_ssubset is) (c i) _) _)
    ·
      refine' le_transₓ (Ennreal.of_real_le_of_real _) Ennreal.of_real_add_le 
      rw [sub_add_sub_cancel]
      exact sub_le_sub_right (f.mono bd.le) _
    ·
      rintro x ⟨h₁, h₂⟩
      refine' (cv ⟨h₁, le_transₓ h₂ (le_of_ltₓ cb)⟩).resolve_left (mt And.left (not_lt_of_le h₂))

@[simp]
theorem outer_Ioc (a b : ℝ) : f.outer (Ioc a b) = of_real (f b - f a) :=
  by 
    refine'
      le_antisymmₓ
        (by 
          rw [←f.length_Ioc]
          apply outer_le_length)
        (le_binfi$ fun s hs => Ennreal.le_of_forall_pos_le_add$ fun ε εpos h => _)
    let δ := ε / 2
    have δpos : 0 < (δ : ℝ≥0∞)
    ·
      simpa using εpos.ne' 
    rcases Ennreal.exists_pos_sum_of_encodable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
    obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a'
    ·
      have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a
      ·
        refine' ContinuousWithinAt.sub _ continuous_within_at_const 
        exact (f.right_continuous a).mono Ioi_subset_Ici_self 
      have B : f a - f a < δ
      ·
        rwa [sub_self, Nnreal.coe_pos, ←Ennreal.coe_pos]
      exact (((tendsto_order.1 A).2 _ B).And self_mem_nhds_within).exists 
    have  : ∀ i, ∃ p : ℝ × ℝ, s i ⊆ Ioo p.1 p.2 ∧ (of_real (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i)+ε' i
    ·
      intro i 
      have  := Ennreal.lt_add_right ((Ennreal.le_tsum i).trans_lt h).Ne (Ennreal.coe_ne_zero.2 (ε'0 i).ne')
      conv  at this => toLHS rw [length]
      simp only [infi_lt_iff, exists_prop] at this 
      rcases this with ⟨p, q', spq, hq'⟩
      have  : ContinuousWithinAt (fun r => of_real (f r - f p)) (Ioi q') q'
      ·
        apply ennreal.continuous_of_real.continuous_at.comp_continuous_within_at 
        refine' ContinuousWithinAt.sub _ continuous_within_at_const 
        exact (f.right_continuous q').mono Ioi_subset_Ici_self 
      rcases(((tendsto_order.1 this).2 _ hq').And self_mem_nhds_within).exists with ⟨q, hq, q'q⟩
      exact ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩
    choose g hg using this 
    have I_subset : Icc a' b ⊆ ⋃i, Ioo (g i).1 (g i).2 :=
      calc Icc a' b ⊆ Ioc a b := fun x hx => ⟨aa'.trans_le hx.1, hx.2⟩
        _ ⊆ ⋃i, s i := hs 
        _ ⊆ ⋃i, Ioo (g i).1 (g i).2 := Union_subset_Union fun i => (hg i).1
        
    calc of_real (f b - f a) = of_real ((f b - f a')+f a' - f a) :=
      by 
        rw [sub_add_sub_cancel]_ ≤ of_real (f b - f a')+of_real (f a' - f a) :=
      Ennreal.of_real_add_le _ ≤ (∑'i, of_real (f (g i).2 - f (g i).1))+of_real δ :=
      add_le_add (f.length_subadditive_Icc_Ioo I_subset)
        (Ennreal.of_real_le_of_real ha'.le)_ ≤ (∑'i, f.length (s i)+ε' i)+δ :=
      add_le_add (Ennreal.tsum_le_tsum fun i => (hg i).2.le)
        (by 
          simp only [Ennreal.of_real_coe_nnreal, le_rfl])_ = ((∑'i, f.length (s i))+∑'i, ε' i)+δ :=
      by 
        rw [Ennreal.tsum_add]_ ≤ ((∑'i, f.length (s i))+δ)+δ :=
      add_le_add (add_le_add le_rfl hε.le) le_rfl _ = (∑'i : ℕ, f.length (s i))+ε :=
      by 
        simp [add_assocₓ, Ennreal.add_halves]

theorem measurable_set_Ioi {c : ℝ} : f.outer.caratheodory.measurable_set' (Ioi c) :=
  by 
    apply outer_measure.of_function_caratheodory fun t => _ 
    refine' le_infi fun a => le_infi fun b => le_infi fun h => _ 
    refine'
      le_transₓ (add_le_add (f.length_mono$ inter_subset_inter_left _ h) (f.length_mono$ diff_subset_diff_left h)) _ 
    cases' le_totalₓ a c with hac hac <;> cases' le_totalₓ b c with hbc hbc
    ·
      simp only [Ioc_inter_Ioi, f.length_Ioc, hac, sup_eq_max, hbc, le_reflₓ, Ioc_eq_empty, max_eq_rightₓ, min_eq_leftₓ,
        Ioc_diff_Ioi, f.length_empty, zero_addₓ, not_ltₓ]
    ·
      simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_rightₓ, sup_eq_max, ←Ennreal.of_real_add,
        f.mono hac, f.mono hbc, sub_nonneg, sub_add_sub_cancel, le_reflₓ, max_eq_rightₓ]
    ·
      simp only [hbc, le_reflₓ, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_leftₓ, Ioc_diff_Ioi, f.length_empty, zero_addₓ,
        or_trueₓ, le_sup_iff, f.length_Ioc, not_ltₓ]
    ·
      simp only [hac, hbc, Ioc_inter_Ioi, Ioc_diff_Ioi, f.length_Ioc, min_eq_rightₓ, sup_eq_max, le_reflₓ, Ioc_eq_empty,
        add_zeroₓ, max_eq_leftₓ, f.length_empty, not_ltₓ]

theorem outer_trim : f.outer.trim = f.outer :=
  by 
    refine' le_antisymmₓ (fun s => _) (outer_measure.le_trim _)
    rw [outer_measure.trim_eq_infi]
    refine' le_infi fun t => le_infi$ fun ht => Ennreal.le_of_forall_pos_le_add$ fun ε ε0 h => _ 
    rcases Ennreal.exists_pos_sum_of_encodable (Ennreal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
    refine' le_transₓ _ (add_le_add_left (le_of_ltₓ hε) _)
    rw [←Ennreal.tsum_add]
    choose g hg using
      show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i)+of_real (ε' i)by 
        intro i 
        have  := Ennreal.lt_add_right ((Ennreal.le_tsum i).trans_lt h).Ne (Ennreal.coe_pos.2 (ε'0 i)).ne' 
        conv  at this => toLHS rw [length]
        simp only [infi_lt_iff] at this 
        rcases this with ⟨a, b, h₁, h₂⟩
        rw [←f.outer_Ioc] at h₂ 
        exact
          ⟨_, h₁, measurable_set_Ioc,
            le_of_ltₓ$
              by 
                simpa using h₂⟩
    simp  at hg 
    apply infi_le_of_le (Union g) _ 
    apply infi_le_of_le (subset.trans ht$ Union_subset_Union fun i => (hg i).1) _ 
    apply infi_le_of_le (MeasurableSet.Union fun i => (hg i).2.1) _ 
    exact le_transₓ (f.outer.Union _) (Ennreal.tsum_le_tsum$ fun i => (hg i).2.2)

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem borel_le_measurable : «expr ≤ »(borel exprℝ(), f.outer.caratheodory) :=
begin
  rw [expr borel_eq_generate_from_Ioi] [],
  refine [expr measurable_space.generate_from_le _],
  simp [] [] [] ["[", expr f.measurable_set_Ioi, "]"] [] [] { contextual := tt }
end

/-! ### The measure associated to a Stieltjes function -/


/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
@[irreducible]
protected def Measureₓ : Measureₓ ℝ :=
  { toOuterMeasure := f.outer,
    m_Union := fun s hs => f.outer.Union_eq_of_caratheodory$ fun i => f.borel_le_measurable _ (hs i),
    trimmed := f.outer_trim }

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = of_real (f b - f a) :=
  by 
    rw [StieltjesFunction.measure]
    exact f.outer_Ioc a b

@[simp]
theorem measure_singleton (a : ℝ) : f.measure {a} = of_real (f a - f.left_lim a) :=
  by 
    obtain ⟨u, u_mono, u_lt_a, u_lim⟩ : ∃ u : ℕ → ℝ, StrictMono u ∧ (∀ n : ℕ, u n < a) ∧ tendsto u at_top (𝓝 a) :=
      exists_seq_strict_mono_tendsto a 
    have A : {a} = ⋂n, Ioc (u n) a
    ·
      refine'
        subset.antisymm
          (fun x hx =>
            by 
              simp [mem_singleton_iff.1 hx, u_lt_a])
          fun x hx => _ 
      simp  at hx 
      have  : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le 
      simp [le_antisymmₓ this (hx 0).2]
    have L1 : tendsto (fun n => f.measure (Ioc (u n) a)) at_top (𝓝 (f.measure {a}))
    ·
      rw [A]
      refine' tendsto_measure_Inter (fun n => measurable_set_Ioc) (fun m n hmn => _) _
      ·
        exact Ioc_subset_Ioc (u_mono.monotone hmn) le_rfl
      ·
        exact
          ⟨0,
            by 
              simpa only [measure_Ioc] using Ennreal.of_real_ne_top⟩
    have L2 : tendsto (fun n => f.measure (Ioc (u n) a)) at_top (𝓝 (of_real (f a - f.left_lim a)))
    ·
      simp only [measure_Ioc]
      have  : tendsto (fun n => f (u n)) at_top (𝓝 (f.left_lim a))
      ·
        apply (f.tendsto_left_lim a).comp 
        exact tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ u_lim (eventually_of_forall fun n => u_lt_a n)
      exact ennreal.continuous_of_real.continuous_at.tendsto.comp (tendsto_const_nhds.sub this)
    exact tendsto_nhds_unique L1 L2

@[simp]
theorem measure_Icc (a b : ℝ) : f.measure (Icc a b) = of_real (f b - f.left_lim a) :=
  by 
    rcases le_or_ltₓ a b with (hab | hab)
    ·
      have A : Disjoint {a} (Ioc a b)
      ·
        simp 
      simp [←Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ←Ennreal.of_real_add, f.left_lim_le,
        measure_union A (measurable_set_singleton a) measurable_set_Ioc, f.mono hab]
    ·
      simp only [hab, measure_empty, Icc_eq_empty, not_leₓ]
      symm 
      simp [Ennreal.of_real_eq_zero, f.le_left_lim hab]

@[simp]
theorem measure_Ioo {a b : ℝ} : f.measure (Ioo a b) = of_real (f.left_lim b - f a) :=
  by 
    rcases le_or_ltₓ b a with (hab | hab)
    ·
      simp only [hab, measure_empty, Ioo_eq_empty, not_ltₓ]
      symm 
      simp [Ennreal.of_real_eq_zero, f.left_lim_le hab]
    ·
      have A : Disjoint (Ioo a b) {b}
      ·
        simp 
      have D : f b - f a = (f b - f.left_lim b)+f.left_lim b - f a
      ·
        abel 
      have  := f.measure_Ioc a b 
      simp only [←Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
        measure_union A measurable_set_Ioo (measurable_set_singleton b), Icc_self] at this 
      rw [D, Ennreal.of_real_add, add_commₓ] at this
      ·
        simpa only [Ennreal.add_right_inj Ennreal.of_real_ne_top]
      ·
        simp only [f.left_lim_le, sub_nonneg]
      ·
        simp only [f.le_left_lim hab, sub_nonneg]

@[simp]
theorem measure_Ico (a b : ℝ) : f.measure (Ico a b) = of_real (f.left_lim b - f.left_lim a) :=
  by 
    rcases le_or_ltₓ b a with (hab | hab)
    ·
      simp only [hab, measure_empty, Ico_eq_empty, not_ltₓ]
      symm 
      simp [Ennreal.of_real_eq_zero, f.left_lim_le_left_lim hab]
    ·
      have A : Disjoint {a} (Ioo a b) :=
        by 
          simp 
      simp [←Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, hab.ne, f.left_lim_le,
        measure_union A (measurable_set_singleton a) measurable_set_Ioo, f.le_left_lim hab, ←Ennreal.of_real_add]

end StieltjesFunction

