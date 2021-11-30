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

instance : CoeFun StieltjesFunction fun _ => ℝ → ℝ :=
  ⟨to_fun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)

variable (f : StieltjesFunction)

theorem mono : Monotone f :=
  f.mono'

theorem right_continuous (x : ℝ) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

/-- The limit of a Stieltjes function to the left of `x` (it exists by monotonicity). The fact that
it is indeed a left limit is asserted in `tendsto_left_lim` -/
irreducible_def left_lim (x : ℝ) :=
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

instance : Inhabited StieltjesFunction :=
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

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set. -/
theorem length_subadditive_Icc_Ioo
{a b : exprℝ()}
{c d : exprℕ() → exprℝ()}
(ss : «expr ⊆ »(Icc a b, «expr⋃ , »((i), Ioo (c i) (d i)))) : «expr ≤ »(of_real «expr - »(f b, f a), «expr∑' , »((i), of_real «expr - »(f (d i), f (c i)))) :=
begin
  suffices [] [":", expr ∀
   (s : finset exprℕ())
   (b)
   (cv : «expr ⊆ »(Icc a b, «expr⋃ , »((i «expr ∈ » («expr↑ »(s) : set exprℕ())), Ioo (c i) (d i)))), «expr ≤ »((of_real «expr - »(f b, f a) : «exprℝ≥0∞»()), «expr∑ in , »((i), s, of_real «expr - »(f (d i), f (c i))))],
  { rcases [expr is_compact_Icc.elim_finite_subcover_image (λ
      (i : exprℕ())
      (_ : «expr ∈ »(i, univ)), @is_open_Ioo _ _ _ _ (c i) (d i)) (by simpa [] [] [] [] [] ["using", expr ss]), "with", "⟨", ident s, ",", ident su, ",", ident hf, ",", ident hs, "⟩"],
    have [ident e] [":", expr «expr = »(«expr⋃ , »((i «expr ∈ » («expr↑ »(hf.to_finset) : set exprℕ())), Ioo (c i) (d i)), «expr⋃ , »((i «expr ∈ » s), Ioo (c i) (d i)))] [],
    by simp [] [] ["only"] ["[", expr ext_iff, ",", expr exists_prop, ",", expr finset.set_bUnion_coe, ",", expr mem_Union, ",", expr forall_const, ",", expr iff_self, ",", expr finite.mem_to_finset, "]"] [] [],
    rw [expr ennreal.tsum_eq_supr_sum] [],
    refine [expr le_trans _ (le_supr _ hf.to_finset)],
    exact [expr this hf.to_finset _ (by simpa [] [] ["only"] ["[", expr e, "]"] [] [])] },
  clear [ident ss, ident b],
  refine [expr λ s, finset.strong_induction_on s (λ s IH b cv, _)],
  cases [expr le_total b a] ["with", ident ab, ident ab],
  { rw [expr ennreal.of_real_eq_zero.2 (sub_nonpos.2 (f.mono ab))] [],
    exact [expr zero_le _] },
  have [] [] [":=", expr cv ⟨ab, le_refl _⟩],
  simp [] [] [] [] [] ["at", ident this],
  rcases [expr this, "with", "⟨", ident i, ",", ident is, ",", ident cb, ",", ident bd, "⟩"],
  rw ["[", "<-", expr finset.insert_erase is, "]"] ["at", ident cv, "⊢"],
  rw ["[", expr finset.coe_insert, ",", expr bUnion_insert, "]"] ["at", ident cv],
  rw ["[", expr finset.sum_insert (finset.not_mem_erase _ _), "]"] [],
  refine [expr le_trans _ (add_le_add_left (IH _ (finset.erase_ssubset is) (c i) _) _)],
  { refine [expr le_trans (ennreal.of_real_le_of_real _) ennreal.of_real_add_le],
    rw [expr sub_add_sub_cancel] [],
    exact [expr sub_le_sub_right (f.mono bd.le) _] },
  { rintro [ident x, "⟨", ident h₁, ",", ident h₂, "⟩"],
    refine [expr (cv ⟨h₁, le_trans h₂ (le_of_lt cb)⟩).resolve_left (mt and.left (not_lt_of_le h₂))] }
end

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem outer_Ioc (a b : exprℝ()) : «expr = »(f.outer (Ioc a b), of_real «expr - »(f b, f a)) :=
begin
  refine [expr le_antisymm (by { rw ["<-", expr f.length_Ioc] [],
      apply [expr outer_le_length] }) «expr $ »(le_binfi, λ
    s hs, «expr $ »(ennreal.le_of_forall_pos_le_add, λ ε εpos h, _))],
  let [ident δ] [] [":=", expr «expr / »(ε, 2)],
  have [ident δpos] [":", expr «expr < »(0, (δ : «exprℝ≥0∞»()))] [],
  by simpa [] [] [] [] [] ["using", expr εpos.ne'],
  rcases [expr ennreal.exists_pos_sum_of_encodable δpos.ne' exprℕ(), "with", "⟨", ident ε', ",", ident ε'0, ",", ident hε, "⟩"],
  obtain ["⟨", ident a', ",", ident ha', ",", ident aa', "⟩", ":", expr «expr∃ , »((a'), «expr ∧ »(«expr < »(«expr - »(f a', f a), δ), «expr < »(a, a')))],
  { have [ident A] [":", expr continuous_within_at (λ r, «expr - »(f r, f a)) (Ioi a) a] [],
    { refine [expr continuous_within_at.sub _ continuous_within_at_const],
      exact [expr (f.right_continuous a).mono Ioi_subset_Ici_self] },
    have [ident B] [":", expr «expr < »(«expr - »(f a, f a), δ)] [],
    by rwa ["[", expr sub_self, ",", expr nnreal.coe_pos, ",", "<-", expr ennreal.coe_pos, "]"] [],
    exact [expr (((tendsto_order.1 A).2 _ B).and self_mem_nhds_within).exists] },
  have [] [":", expr ∀
   i, «expr∃ , »((p : «expr × »(exprℝ(), exprℝ())), «expr ∧ »(«expr ⊆ »(s i, Ioo p.1 p.2), «expr < »((of_real «expr - »(f p.2, f p.1) : «exprℝ≥0∞»()), «expr + »(f.length (s i), ε' i))))] [],
  { intro [ident i],
    have [] [] [":=", expr ennreal.lt_add_right ((ennreal.le_tsum i).trans_lt h).ne (ennreal.coe_ne_zero.2 (ε'0 i).ne')],
    conv ["at", ident this] [] { to_lhs,
      rw [expr length] },
    simp [] [] ["only"] ["[", expr infi_lt_iff, ",", expr exists_prop, "]"] [] ["at", ident this],
    rcases [expr this, "with", "⟨", ident p, ",", ident q', ",", ident spq, ",", ident hq', "⟩"],
    have [] [":", expr continuous_within_at (λ r, of_real «expr - »(f r, f p)) (Ioi q') q'] [],
    { apply [expr ennreal.continuous_of_real.continuous_at.comp_continuous_within_at],
      refine [expr continuous_within_at.sub _ continuous_within_at_const],
      exact [expr (f.right_continuous q').mono Ioi_subset_Ici_self] },
    rcases [expr (((tendsto_order.1 this).2 _ hq').and self_mem_nhds_within).exists, "with", "⟨", ident q, ",", ident hq, ",", ident q'q, "⟩"],
    exact [expr ⟨⟨p, q⟩, spq.trans (Ioc_subset_Ioo_right q'q), hq⟩] },
  choose [] [ident g] [ident hg] ["using", expr this],
  have [ident I_subset] [":", expr «expr ⊆ »(Icc a' b, «expr⋃ , »((i), Ioo (g i).1 (g i).2))] [":=", expr calc
     «expr ⊆ »(Icc a' b, Ioc a b) : λ x hx, ⟨aa'.trans_le hx.1, hx.2⟩
     «expr ⊆ »(..., «expr⋃ , »((i), s i)) : hs
     «expr ⊆ »(..., «expr⋃ , »((i), Ioo (g i).1 (g i).2)) : Union_subset_Union (λ i, (hg i).1)],
  calc
    «expr = »(of_real «expr - »(f b, f a), of_real «expr + »(«expr - »(f b, f a'), «expr - »(f a', f a))) : by rw [expr sub_add_sub_cancel] []
    «expr ≤ »(..., «expr + »(of_real «expr - »(f b, f a'), of_real «expr - »(f a', f a))) : ennreal.of_real_add_le
    «expr ≤ »(..., «expr + »(«expr∑' , »((i), of_real «expr - »(f (g i).2, f (g i).1)), of_real δ)) : add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ennreal.of_real_le_of_real ha'.le)
    «expr ≤ »(..., «expr + »(«expr∑' , »((i), «expr + »(f.length (s i), ε' i)), δ)) : add_le_add (ennreal.tsum_le_tsum (λ
      i, (hg i).2.le)) (by simp [] [] ["only"] ["[", expr ennreal.of_real_coe_nnreal, ",", expr le_rfl, "]"] [] [])
    «expr = »(..., «expr + »(«expr + »(«expr∑' , »((i), f.length (s i)), «expr∑' , »((i), ε' i)), δ)) : by rw ["[", expr ennreal.tsum_add, "]"] []
    «expr ≤ »(..., «expr + »(«expr + »(«expr∑' , »((i), f.length (s i)), δ), δ)) : add_le_add (add_le_add le_rfl hε.le) le_rfl
    «expr = »(..., «expr + »(«expr∑' , »((i : exprℕ()), f.length (s i)), ε)) : by simp [] [] [] ["[", expr add_assoc, ",", expr ennreal.add_halves, "]"] [] []
end

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

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem outer_trim : «expr = »(f.outer.trim, f.outer) :=
begin
  refine [expr le_antisymm (λ s, _) (outer_measure.le_trim _)],
  rw [expr outer_measure.trim_eq_infi] [],
  refine [expr le_infi (λ t, «expr $ »(le_infi, λ ht, «expr $ »(ennreal.le_of_forall_pos_le_add, λ ε ε0 h, _)))],
  rcases [expr ennreal.exists_pos_sum_of_encodable (ennreal.coe_pos.2 ε0).ne' exprℕ(), "with", "⟨", ident ε', ",", ident ε'0, ",", ident hε, "⟩"],
  refine [expr le_trans _ (add_le_add_left (le_of_lt hε) _)],
  rw ["<-", expr ennreal.tsum_add] [],
  choose [] [ident g] [ident hg] ["using", expr show ∀
   i, «expr∃ , »((s), «expr ∧ »(«expr ⊆ »(t i, s), «expr ∧ »(measurable_set s, «expr ≤ »(f.outer s, «expr + »(f.length (t i), of_real (ε' i)))))), { intro [ident i],
     have [] [] [":=", expr ennreal.lt_add_right ((ennreal.le_tsum i).trans_lt h).ne (ennreal.coe_pos.2 (ε'0 i)).ne'],
     conv ["at", ident this] [] { to_lhs,
       rw [expr length] },
     simp [] [] ["only"] ["[", expr infi_lt_iff, "]"] [] ["at", ident this],
     rcases [expr this, "with", "⟨", ident a, ",", ident b, ",", ident h₁, ",", ident h₂, "⟩"],
     rw ["<-", expr f.outer_Ioc] ["at", ident h₂],
     exact [expr ⟨_, h₁, measurable_set_Ioc, «expr $ »(le_of_lt, by simpa [] [] [] [] [] ["using", expr h₂])⟩] }],
  simp [] [] [] [] [] ["at", ident hg],
  apply [expr infi_le_of_le (Union g) _],
  apply [expr infi_le_of_le «expr $ »(subset.trans ht, Union_subset_Union (λ i, (hg i).1)) _],
  apply [expr infi_le_of_le (measurable_set.Union (λ i, (hg i).2.1)) _],
  exact [expr le_trans (f.outer.Union _) «expr $ »(ennreal.tsum_le_tsum, λ i, (hg i).2.2)]
end

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem borel_le_measurable : «expr ≤ »(borel exprℝ(), f.outer.caratheodory) :=
begin
  rw [expr borel_eq_generate_from_Ioi] [],
  refine [expr measurable_space.generate_from_le _],
  simp [] [] [] ["[", expr f.measurable_set_Ioi, "]"] [] [] { contextual := tt }
end

/-! ### The measure associated to a Stieltjes function -/


/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. -/
protected irreducible_def Measureₓ : Measureₓ ℝ :=
  { toOuterMeasure := f.outer,
    m_Union := fun s hs => f.outer.Union_eq_of_caratheodory$ fun i => f.borel_le_measurable _ (hs i),
    trimmed := f.outer_trim }

@[simp]
theorem measure_Ioc (a b : ℝ) : f.measure (Ioc a b) = of_real (f b - f a) :=
  by 
    rw [StieltjesFunction.measure]
    exact f.outer_Ioc a b

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem measure_singleton (a : exprℝ()) : «expr = »(f.measure {a}, of_real «expr - »(f a, f.left_lim a)) :=
begin
  obtain ["⟨", ident u, ",", ident u_mono, ",", ident u_lt_a, ",", ident u_lim, "⟩", ":", expr «expr∃ , »((u : exprℕ() → exprℝ()), «expr ∧ »(strict_mono u, «expr ∧ »(∀
      n : exprℕ(), «expr < »(u n, a), tendsto u at_top (expr𝓝() a)))), ":=", expr exists_seq_strict_mono_tendsto a],
  have [ident A] [":", expr «expr = »({a}, «expr⋂ , »((n), Ioc (u n) a))] [],
  { refine [expr subset.antisymm (λ
      x hx, by simp [] [] [] ["[", expr mem_singleton_iff.1 hx, ",", expr u_lt_a, "]"] [] []) (λ x hx, _)],
    simp [] [] [] [] [] ["at", ident hx],
    have [] [":", expr «expr ≤ »(a, x)] [":=", expr le_of_tendsto' u_lim (λ n, (hx n).1.le)],
    simp [] [] [] ["[", expr le_antisymm this (hx 0).2, "]"] [] [] },
  have [ident L1] [":", expr tendsto (λ n, f.measure (Ioc (u n) a)) at_top (expr𝓝() (f.measure {a}))] [],
  { rw [expr A] [],
    refine [expr tendsto_measure_Inter (λ n, measurable_set_Ioc) (λ m n hmn, _) _],
    { exact [expr Ioc_subset_Ioc (u_mono.monotone hmn) le_rfl] },
    { exact [expr ⟨0, by simpa [] [] ["only"] ["[", expr measure_Ioc, "]"] [] ["using", expr ennreal.of_real_ne_top]⟩] } },
  have [ident L2] [":", expr tendsto (λ
    n, f.measure (Ioc (u n) a)) at_top (expr𝓝() (of_real «expr - »(f a, f.left_lim a)))] [],
  { simp [] [] ["only"] ["[", expr measure_Ioc, "]"] [] [],
    have [] [":", expr tendsto (λ n, f (u n)) at_top (expr𝓝() (f.left_lim a))] [],
    { apply [expr (f.tendsto_left_lim a).comp],
      exact [expr tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ u_lim (eventually_of_forall (λ
         n, u_lt_a n))] },
    exact [expr ennreal.continuous_of_real.continuous_at.tendsto.comp (tendsto_const_nhds.sub this)] },
  exact [expr tendsto_nhds_unique L1 L2]
end

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem measure_Icc (a b : exprℝ()) : «expr = »(f.measure (Icc a b), of_real «expr - »(f b, f.left_lim a)) :=
begin
  rcases [expr le_or_lt a b, "with", ident hab, "|", ident hab],
  { have [ident A] [":", expr disjoint {a} (Ioc a b)] [],
    by simp [] [] [] [] [] [],
    simp [] [] [] ["[", "<-", expr Icc_union_Ioc_eq_Icc le_rfl hab, ",", "-", ident singleton_union, ",", "<-", expr ennreal.of_real_add, ",", expr f.left_lim_le, ",", expr measure_union A (measurable_set_singleton a) measurable_set_Ioc, ",", expr f.mono hab, "]"] [] [] },
  { simp [] [] ["only"] ["[", expr hab, ",", expr measure_empty, ",", expr Icc_eq_empty, ",", expr not_le, "]"] [] [],
    symmetry,
    simp [] [] [] ["[", expr ennreal.of_real_eq_zero, ",", expr f.le_left_lim hab, "]"] [] [] }
end

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem measure_Ioo {a b : exprℝ()} : «expr = »(f.measure (Ioo a b), of_real «expr - »(f.left_lim b, f a)) :=
begin
  rcases [expr le_or_lt b a, "with", ident hab, "|", ident hab],
  { simp [] [] ["only"] ["[", expr hab, ",", expr measure_empty, ",", expr Ioo_eq_empty, ",", expr not_lt, "]"] [] [],
    symmetry,
    simp [] [] [] ["[", expr ennreal.of_real_eq_zero, ",", expr f.left_lim_le hab, "]"] [] [] },
  { have [ident A] [":", expr disjoint (Ioo a b) {b}] [],
    by simp [] [] [] [] [] [],
    have [ident D] [":", expr «expr = »(«expr - »(f b, f a), «expr + »(«expr - »(f b, f.left_lim b), «expr - »(f.left_lim b, f a)))] [],
    by abel [] [] [],
    have [] [] [":=", expr f.measure_Ioc a b],
    simp [] [] ["only"] ["[", "<-", expr Ioo_union_Icc_eq_Ioc hab le_rfl, ",", expr measure_singleton, ",", expr measure_union A measurable_set_Ioo (measurable_set_singleton b), ",", expr Icc_self, "]"] [] ["at", ident this],
    rw ["[", expr D, ",", expr ennreal.of_real_add, ",", expr add_comm, "]"] ["at", ident this],
    { simpa [] [] ["only"] ["[", expr ennreal.add_right_inj ennreal.of_real_ne_top, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr f.left_lim_le, ",", expr sub_nonneg, "]"] [] [] },
    { simp [] [] ["only"] ["[", expr f.le_left_lim hab, ",", expr sub_nonneg, "]"] [] [] } }
end

-- error in MeasureTheory.Measure.Stieltjes: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem measure_Ico (a b : exprℝ()) : «expr = »(f.measure (Ico a b), of_real «expr - »(f.left_lim b, f.left_lim a)) :=
begin
  rcases [expr le_or_lt b a, "with", ident hab, "|", ident hab],
  { simp [] [] ["only"] ["[", expr hab, ",", expr measure_empty, ",", expr Ico_eq_empty, ",", expr not_lt, "]"] [] [],
    symmetry,
    simp [] [] [] ["[", expr ennreal.of_real_eq_zero, ",", expr f.left_lim_le_left_lim hab, "]"] [] [] },
  { have [ident A] [":", expr disjoint {a} (Ioo a b)] [":=", expr by simp [] [] [] [] [] []],
    simp [] [] [] ["[", "<-", expr Icc_union_Ioo_eq_Ico le_rfl hab, ",", "-", ident singleton_union, ",", expr hab.ne, ",", expr f.left_lim_le, ",", expr measure_union A (measurable_set_singleton a) measurable_set_Ioo, ",", expr f.le_left_lim hab, ",", "<-", expr ennreal.of_real_add, "]"] [] [] }
end

end StieltjesFunction

