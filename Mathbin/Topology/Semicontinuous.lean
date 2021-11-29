import Mathbin.Algebra.IndicatorFunction 
import Mathbin.Topology.Algebra.Group 
import Mathbin.Topology.ContinuousOn 
import Mathbin.Topology.Instances.Ennreal

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it can not jump down.

Upper semicontinuous functions are defined similarly.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 definitions related to lower semicontinuity:
* `lower_semicontinuous_within_at f s x`
* `lower_semicontinuous_at f x`
* `lower_semicontinuous_on f s`
* `lower_semicontinuous f`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are lower semicontinuous;
* `indicator s (λ _, y)` is lower semicontinuous when `s` is open and `0 ≤ y`, or when `s` is closed
  and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `order_dual`.

-/


open_locale TopologicalSpace BigOperators Ennreal

open Set

variable{α : Type _}[TopologicalSpace α]{β : Type _}[Preorderₓ β]{f g : α → β}{x : α}{s t : Set α}{y z : β}

/-! ### Main definitions -/


/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y (_ : y < f x), ∀ᶠx' in 𝓝[s] x, y < f x'

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`.-/
def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x (_ : x ∈ s), LowerSemicontinuousWithinAt f s x

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y (_ : y < f x), ∀ᶠx' in 𝓝 x, y < f x'

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠx' in 𝓝[s] x, f x' < y

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x (_ : x ∈ s), UpperSemicontinuousWithinAt f s x

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠx' in 𝓝 x, f x' < y

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x

/-!
### Lower semicontinuous functions
-/


/-! #### Basic dot notation interface for lower semicontinuity -/


theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
  LowerSemicontinuousWithinAt f t x :=
  fun y hy => Filter.Eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

theorem lower_semicontinuous_within_at_univ_iff : LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x :=
  by 
    simp [LowerSemicontinuousWithinAt, LowerSemicontinuousAt, nhds_within_univ]

theorem LowerSemicontinuousAt.lower_semicontinuous_within_at (s : Set α) (h : LowerSemicontinuousAt f x) :
  LowerSemicontinuousWithinAt f s x :=
  fun y hy => Filter.Eventually.filter_mono nhds_within_le_nhds (h y hy)

theorem LowerSemicontinuousOn.lower_semicontinuous_within_at (h : LowerSemicontinuousOn f s) (hx : x ∈ s) :
  LowerSemicontinuousWithinAt f s x :=
  h x hx

theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) : LowerSemicontinuousOn f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem lower_semicontinuous_on_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f :=
  by 
    simp [LowerSemicontinuousOn, LowerSemicontinuous, lower_semicontinuous_within_at_univ_iff]

theorem LowerSemicontinuous.lower_semicontinuous_at (h : LowerSemicontinuous f) (x : α) : LowerSemicontinuousAt f x :=
  h x

theorem LowerSemicontinuous.lower_semicontinuous_within_at (h : LowerSemicontinuous f) (s : Set α) (x : α) :
  LowerSemicontinuousWithinAt f s x :=
  (h x).LowerSemicontinuousWithinAt s

theorem LowerSemicontinuous.lower_semicontinuous_on (h : LowerSemicontinuous f) (s : Set α) :
  LowerSemicontinuousOn f s :=
  fun x hx => h.lower_semicontinuous_within_at s x

/-! #### Constants -/


theorem lower_semicontinuous_within_at_const : LowerSemicontinuousWithinAt (fun x => z) s x :=
  fun y hy => Filter.eventually_of_forall fun x => hy

theorem lower_semicontinuous_at_const : LowerSemicontinuousAt (fun x => z) x :=
  fun y hy => Filter.eventually_of_forall fun x => hy

theorem lower_semicontinuous_on_const : LowerSemicontinuousOn (fun x => z) s :=
  fun x hx => lower_semicontinuous_within_at_const

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem lower_semicontinuous_const : lower_semicontinuous (λ x : α, z) := λ x, lower_semicontinuous_at_const

/-! #### Indicators -/


section 

variable[HasZero β]

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_open.lower_semicontinuous_indicator
(hs : is_open s)
(hy : «expr ≤ »(0, y)) : lower_semicontinuous (indicator s (λ x, y)) :=
begin
  assume [binders (x z hz)],
  by_cases [expr h, ":", expr «expr ∈ »(x, s)]; simp [] [] [] ["[", expr h, "]"] [] ["at", ident hz],
  { filter_upwards ["[", expr hs.mem_nhds h, "]"] [],
    simp [] [] [] ["[", expr hz, "]"] [] [] { contextual := tt } },
  { apply [expr filter.eventually_of_forall (λ x', _)],
    by_cases [expr h', ":", expr «expr ∈ »(x', s)]; simp [] [] [] ["[", expr h', ",", expr hz.trans_le hy, ",", expr hz, "]"] [] [] }
end

theorem IsOpen.lower_semicontinuous_on_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
  LowerSemicontinuousOn (indicator s fun x => y) t :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousOn t

theorem IsOpen.lower_semicontinuous_at_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
  LowerSemicontinuousAt (indicator s fun x => y) x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousAt x

theorem IsOpen.lower_semicontinuous_within_at_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
  LowerSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousWithinAt t x

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_closed.lower_semicontinuous_indicator
(hs : is_closed s)
(hy : «expr ≤ »(y, 0)) : lower_semicontinuous (indicator s (λ x, y)) :=
begin
  assume [binders (x z hz)],
  by_cases [expr h, ":", expr «expr ∈ »(x, s)]; simp [] [] [] ["[", expr h, "]"] [] ["at", ident hz],
  { apply [expr filter.eventually_of_forall (λ x', _)],
    by_cases [expr h', ":", expr «expr ∈ »(x', s)]; simp [] [] [] ["[", expr h', ",", expr hz, ",", expr hz.trans_le hy, "]"] [] [] },
  { filter_upwards ["[", expr hs.is_open_compl.mem_nhds h, "]"] [],
    simp [] [] [] ["[", expr hz, "]"] [] [] { contextual := tt } }
end

theorem IsClosed.lower_semicontinuous_on_indicator (hs : IsClosed s) (hy : y ≤ 0) :
  LowerSemicontinuousOn (indicator s fun x => y) t :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousOn t

theorem IsClosed.lower_semicontinuous_at_indicator (hs : IsClosed s) (hy : y ≤ 0) :
  LowerSemicontinuousAt (indicator s fun x => y) x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousAt x

theorem IsClosed.lower_semicontinuous_within_at_indicator (hs : IsClosed s) (hy : y ≤ 0) :
  LowerSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.lower_semicontinuous_indicator hy).LowerSemicontinuousWithinAt t x

end 

/-! #### Relationship with continuity -/


theorem lower_semicontinuous_iff_is_open : LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => is_open_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt => IsOpen.mem_nhds (H y) y_lt⟩

theorem LowerSemicontinuous.is_open_preimage (hf : LowerSemicontinuous f) (y : β) : IsOpen (f ⁻¹' Ioi y) :=
  lower_semicontinuous_iff_is_open.1 hf y

section 

variable{γ : Type _}[LinearOrderₓ γ][TopologicalSpace γ][OrderTopology γ]

theorem ContinuousWithinAt.lower_semicontinuous_within_at {f : α → γ} (h : ContinuousWithinAt f s x) :
  LowerSemicontinuousWithinAt f s x :=
  fun y hy => h (Ioi_mem_nhds hy)

theorem ContinuousAt.lower_semicontinuous_at {f : α → γ} (h : ContinuousAt f x) : LowerSemicontinuousAt f x :=
  fun y hy => h (Ioi_mem_nhds hy)

theorem ContinuousOn.lower_semicontinuous_on {f : α → γ} (h : ContinuousOn f s) : LowerSemicontinuousOn f s :=
  fun x hx => (h x hx).LowerSemicontinuousWithinAt

theorem Continuous.lower_semicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun x => h.continuous_at.lower_semicontinuous_at

end 

/-! ### Composition -/


section 

variable{γ : Type _}[LinearOrderₓ γ][TopologicalSpace γ][OrderTopology γ]

variable{δ : Type _}[LinearOrderₓ δ][TopologicalSpace δ][OrderTopology δ]

theorem ContinuousAt.comp_lower_semicontinuous_within_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) : LowerSemicontinuousWithinAt (g ∘ f) s x :=
  by 
    intro y hy 
    byCases' h : ∃ l, l < f x
    ·
      obtain ⟨z, zlt, hz⟩ : ∃ (z : _)(_ : z < f x), Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
        exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h 
      filterUpwards [hf z zlt]
      intro a ha 
      calc y < g (min (f x) (f a)) :=
        hz
          (by 
            simp [zlt, ha, le_reflₓ])_ ≤ g (f a) :=
        gmon (min_le_rightₓ _ _)
    ·
      simp only [not_exists, not_ltₓ] at h 
      exact Filter.eventually_of_forall fun a => hy.trans_le (gmon (h (f a)))

theorem ContinuousAt.comp_lower_semicontinuous_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x :=
  by 
    simp only [←lower_semicontinuous_within_at_univ_iff] at hf⊢
    exact hg.comp_lower_semicontinuous_within_at hf gmon

theorem Continuous.comp_lower_semicontinuous_on {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuous_at.comp_lower_semicontinuous_within_at (hf x hx) gmon

theorem Continuous.comp_lower_semicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g) (hf : LowerSemicontinuous f)
  (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) :=
  fun x => hg.continuous_at.comp_lower_semicontinuous_at (hf x) gmon

theorem ContinuousAt.comp_lower_semicontinuous_within_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) : UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lower_semicontinuous_within_at α _ x s γ _ _ _ (OrderDual δ) _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_lower_semicontinuous_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lower_semicontinuous_at α _ x γ _ _ _ (OrderDual δ) _ _ _ g f hg hf gmon

theorem Continuous.comp_lower_semicontinuous_on_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuous_at.comp_lower_semicontinuous_within_at_antitone (hf x hx) gmon

theorem Continuous.comp_lower_semicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) :=
  fun x => hg.continuous_at.comp_lower_semicontinuous_at_antitone (hf x) gmon

end 

/-! #### Addition -/


section 

variable{ι : Type _}{γ : Type _}[LinearOrderedAddCommMonoid γ][TopologicalSpace γ][OrderTopology γ]

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem lower_semicontinuous_within_at.add'
{f g : α → γ}
(hf : lower_semicontinuous_within_at f s x)
(hg : lower_semicontinuous_within_at g s x)
(hcont : continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : lower_semicontinuous_within_at (λ
 z, «expr + »(f z, g z)) s x :=
begin
  assume [binders (y hy)],
  obtain ["⟨", ident u, ",", ident v, ",", ident u_open, ",", ident xu, ",", ident v_open, ",", ident xv, ",", ident h, "⟩", ":", expr «expr∃ , »((u
     v : set γ), «expr ∧ »(is_open u, «expr ∧ »(«expr ∈ »(f x, u), «expr ∧ »(is_open v, «expr ∧ »(«expr ∈ »(g x, v), «expr ⊆ »(u.prod v, {p : «expr × »(γ, γ) | «expr < »(y, «expr + »(p.fst, p.snd))})))))), ":=", expr mem_nhds_prod_iff'.1 (hcont (is_open_Ioi.mem_nhds hy))],
  by_cases [expr hx₁, ":", expr «expr∃ , »((l), «expr < »(l, f x))],
  { obtain ["⟨", ident z₁, ",", ident z₁lt, ",", ident h₁, "⟩", ":", expr «expr∃ , »((z₁ «expr < » f x), «expr ⊆ »(Ioc z₁ (f x), u)), ":=", expr exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁],
    by_cases [expr hx₂, ":", expr «expr∃ , »((l), «expr < »(l, g x))],
    { obtain ["⟨", ident z₂, ",", ident z₂lt, ",", ident h₂, "⟩", ":", expr «expr∃ , »((z₂ «expr < » g x), «expr ⊆ »(Ioc z₂ (g x), v)), ":=", expr exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂],
      filter_upwards ["[", expr hf z₁ z₁lt, ",", expr hg z₂ z₂lt, "]"] [],
      assume [binders (z h₁z h₂z)],
      have [ident A1] [":", expr «expr ∈ »(min (f z) (f x), u)] [],
      { by_cases [expr H, ":", expr «expr ≤ »(f z, f x)],
        { simp [] [] [] ["[", expr H, "]"] [] [],
          exact [expr h₁ ⟨h₁z, H⟩] },
        { simp [] [] [] ["[", expr le_of_not_le H, "]"] [] [],
          exact [expr h₁ ⟨z₁lt, le_refl _⟩] } },
      have [ident A2] [":", expr «expr ∈ »(min (g z) (g x), v)] [],
      { by_cases [expr H, ":", expr «expr ≤ »(g z, g x)],
        { simp [] [] [] ["[", expr H, "]"] [] [],
          exact [expr h₂ ⟨h₂z, H⟩] },
        { simp [] [] [] ["[", expr le_of_not_le H, "]"] [] [],
          exact [expr h₂ ⟨z₂lt, le_refl _⟩] } },
      have [] [":", expr «expr ∈ »((min (f z) (f x), min (g z) (g x)), u.prod v)] [":=", expr ⟨A1, A2⟩],
      calc
        «expr < »(y, «expr + »(min (f z) (f x), min (g z) (g x))) : h this
        «expr ≤ »(..., «expr + »(f z, g z)) : add_le_add (min_le_left _ _) (min_le_left _ _) },
    { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident hx₂],
      filter_upwards ["[", expr hf z₁ z₁lt, "]"] [],
      assume [binders (z h₁z)],
      have [ident A1] [":", expr «expr ∈ »(min (f z) (f x), u)] [],
      { by_cases [expr H, ":", expr «expr ≤ »(f z, f x)],
        { simp [] [] [] ["[", expr H, "]"] [] [],
          exact [expr h₁ ⟨h₁z, H⟩] },
        { simp [] [] [] ["[", expr le_of_not_le H, "]"] [] [],
          exact [expr h₁ ⟨z₁lt, le_refl _⟩] } },
      have [] [":", expr «expr ∈ »((min (f z) (f x), g x), u.prod v)] [":=", expr ⟨A1, xv⟩],
      calc
        «expr < »(y, «expr + »(min (f z) (f x), g x)) : h this
        «expr ≤ »(..., «expr + »(f z, g z)) : add_le_add (min_le_left _ _) (hx₂ (g z)) } },
  { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident hx₁],
    by_cases [expr hx₂, ":", expr «expr∃ , »((l), «expr < »(l, g x))],
    { obtain ["⟨", ident z₂, ",", ident z₂lt, ",", ident h₂, "⟩", ":", expr «expr∃ , »((z₂ «expr < » g x), «expr ⊆ »(Ioc z₂ (g x), v)), ":=", expr exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂],
      filter_upwards ["[", expr hg z₂ z₂lt, "]"] [],
      assume [binders (z h₂z)],
      have [ident A2] [":", expr «expr ∈ »(min (g z) (g x), v)] [],
      { by_cases [expr H, ":", expr «expr ≤ »(g z, g x)],
        { simp [] [] [] ["[", expr H, "]"] [] [],
          exact [expr h₂ ⟨h₂z, H⟩] },
        { simp [] [] [] ["[", expr le_of_not_le H, "]"] [] [],
          exact [expr h₂ ⟨z₂lt, le_refl _⟩] } },
      have [] [":", expr «expr ∈ »((f x, min (g z) (g x)), u.prod v)] [":=", expr ⟨xu, A2⟩],
      calc
        «expr < »(y, «expr + »(f x, min (g z) (g x))) : h this
        «expr ≤ »(..., «expr + »(f z, g z)) : add_le_add (hx₁ (f z)) (min_le_left _ _) },
    { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident hx₁, ident hx₂],
      apply [expr filter.eventually_of_forall],
      assume [binders (z)],
      have [] [":", expr «expr ∈ »((f x, g x), u.prod v)] [":=", expr ⟨xu, xv⟩],
      calc
        «expr < »(y, «expr + »(f x, g x)) : h this
        «expr ≤ »(..., «expr + »(f z, g z)) : add_le_add (hx₁ (f z)) (hx₂ (g z)) } }
end

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem lower_semicontinuous_at.add'
{f g : α → γ}
(hf : lower_semicontinuous_at f x)
(hg : lower_semicontinuous_at g x)
(hcont : continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : lower_semicontinuous_at (λ z, «expr + »(f z, g z)) x :=
by { simp_rw ["[", "<-", expr lower_semicontinuous_within_at_univ_iff, "]"] ["at", "*"],
  exact [expr hf.add' hg hcont] }

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem lower_semicontinuous_on.add'
{f g : α → γ}
(hf : lower_semicontinuous_on f s)
(hg : lower_semicontinuous_on g s)
(hcont : ∀
 x «expr ∈ » s, continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : lower_semicontinuous_on (λ z, «expr + »(f z, g z)) s :=
λ x hx, (hf x hx).add' (hg x hx) (hcont x hx)

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem lower_semicontinuous.add'
{f g : α → γ}
(hf : lower_semicontinuous f)
(hg : lower_semicontinuous g)
(hcont : ∀
 x, continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : lower_semicontinuous (λ z, «expr + »(f z, g z)) :=
λ x, (hf x).add' (hg x) (hcont x)

variable[HasContinuousAdd γ]

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
  (hg : LowerSemicontinuousWithinAt g s x) : LowerSemicontinuousWithinAt (fun z => f z+g z) s x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x) (hg : LowerSemicontinuousAt g x) :
  LowerSemicontinuousAt (fun z => f z+g z) x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
  LowerSemicontinuousOn (fun z => f z+g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt

/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
  LowerSemicontinuous fun z => f z+g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt

theorem lower_semicontinuous_within_at_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), LowerSemicontinuousWithinAt (f i) s x) :
  LowerSemicontinuousWithinAt (fun z => ∑i in a, f i z) s x :=
  by 
    classical 
    induction' a using Finset.induction_on with i a ia IH generalizing ha
    ·
      exact lower_semicontinuous_within_at_const
    ·
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self i a))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))

theorem lower_semicontinuous_at_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), LowerSemicontinuousAt (f i) x) : LowerSemicontinuousAt (fun z => ∑i in a, f i z) x :=
  by 
    simpRw [←lower_semicontinuous_within_at_univ_iff]  at *
    exact lower_semicontinuous_within_at_sum ha

theorem lower_semicontinuous_on_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), LowerSemicontinuousOn (f i) s) : LowerSemicontinuousOn (fun z => ∑i in a, f i z) s :=
  fun x hx => lower_semicontinuous_within_at_sum fun i hi => ha i hi x hx

theorem lower_semicontinuous_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀ i (_ : i ∈ a), LowerSemicontinuous (f i)) :
  LowerSemicontinuous fun z => ∑i in a, f i z :=
  fun x => lower_semicontinuous_at_sum fun i hi => ha i hi x

end 

/-! #### Supremum -/


section 

variable{ι : Sort _}{δ : Type _}[CompleteLinearOrder δ]

theorem lower_semicontinuous_within_at_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
  LowerSemicontinuousWithinAt (fun x' => ⨆i, f i x') s x :=
  by 
    intro y hy 
    rcases lt_supr_iff.1 hy with ⟨i, hi⟩
    filterUpwards [h i y hi]
    intro x' hx' 
    exact lt_supr_iff.2 ⟨i, hx'⟩

theorem lower_semicontinuous_within_at_bsupr {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
  LowerSemicontinuousWithinAt (fun x' => ⨆i hi, f i hi x') s x :=
  lower_semicontinuous_within_at_supr$ fun i => lower_semicontinuous_within_at_supr$ fun hi => h i hi

theorem lower_semicontinuous_at_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
  LowerSemicontinuousAt (fun x' => ⨆i, f i x') x :=
  by 
    simpRw [←lower_semicontinuous_within_at_univ_iff]  at *
    exact lower_semicontinuous_within_at_supr h

theorem lower_semicontinuous_at_bsupr {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) : LowerSemicontinuousAt (fun x' => ⨆i hi, f i hi x') x :=
  lower_semicontinuous_at_supr$ fun i => lower_semicontinuous_at_supr$ fun hi => h i hi

theorem lower_semicontinuous_on_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
  LowerSemicontinuousOn (fun x' => ⨆i, f i x') s :=
  fun x hx => lower_semicontinuous_within_at_supr fun i => h i x hx

theorem lower_semicontinuous_on_bsupr {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) : LowerSemicontinuousOn (fun x' => ⨆i hi, f i hi x') s :=
  lower_semicontinuous_on_supr$ fun i => lower_semicontinuous_on_supr$ fun hi => h i hi

theorem lower_semicontinuous_supr {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
  LowerSemicontinuous fun x' => ⨆i, f i x' :=
  fun x => lower_semicontinuous_at_supr fun i => h i x

theorem lower_semicontinuous_bsupr {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, LowerSemicontinuous (f i hi)) : LowerSemicontinuous fun x' => ⨆i hi, f i hi x' :=
  lower_semicontinuous_supr$ fun i => lower_semicontinuous_supr$ fun hi => h i hi

end 

/-! #### Infinite sums -/


section 

variable{ι : Type _}

theorem lower_semicontinuous_within_at_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
  LowerSemicontinuousWithinAt (fun x' => ∑'i, f i x') s x :=
  by 
    simpRw [Ennreal.tsum_eq_supr_sum]
    apply lower_semicontinuous_within_at_supr fun b => _ 
    exact lower_semicontinuous_within_at_sum fun i hi => h i

theorem lower_semicontinuous_at_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
  LowerSemicontinuousAt (fun x' => ∑'i, f i x') x :=
  by 
    simpRw [←lower_semicontinuous_within_at_univ_iff]  at *
    exact lower_semicontinuous_within_at_tsum h

theorem lower_semicontinuous_on_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
  LowerSemicontinuousOn (fun x' => ∑'i, f i x') s :=
  fun x hx => lower_semicontinuous_within_at_tsum fun i => h i x hx

theorem lower_semicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
  LowerSemicontinuous fun x' => ∑'i, f i x' :=
  fun x => lower_semicontinuous_at_tsum fun i => h i x

end 

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
  UpperSemicontinuousWithinAt f t x :=
  fun y hy => Filter.Eventually.filter_mono (nhds_within_mono _ hst) (h y hy)

theorem upper_semicontinuous_within_at_univ_iff : UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x :=
  by 
    simp [UpperSemicontinuousWithinAt, UpperSemicontinuousAt, nhds_within_univ]

theorem UpperSemicontinuousAt.upper_semicontinuous_within_at (s : Set α) (h : UpperSemicontinuousAt f x) :
  UpperSemicontinuousWithinAt f s x :=
  fun y hy => Filter.Eventually.filter_mono nhds_within_le_nhds (h y hy)

theorem UpperSemicontinuousOn.upper_semicontinuous_within_at (h : UpperSemicontinuousOn f s) (hx : x ∈ s) :
  UpperSemicontinuousWithinAt f s x :=
  h x hx

theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) : UpperSemicontinuousOn f t :=
  fun x hx => (h x (hst hx)).mono hst

theorem upper_semicontinuous_on_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f :=
  by 
    simp [UpperSemicontinuousOn, UpperSemicontinuous, upper_semicontinuous_within_at_univ_iff]

theorem UpperSemicontinuous.upper_semicontinuous_at (h : UpperSemicontinuous f) (x : α) : UpperSemicontinuousAt f x :=
  h x

theorem UpperSemicontinuous.upper_semicontinuous_within_at (h : UpperSemicontinuous f) (s : Set α) (x : α) :
  UpperSemicontinuousWithinAt f s x :=
  (h x).UpperSemicontinuousWithinAt s

theorem UpperSemicontinuous.upper_semicontinuous_on (h : UpperSemicontinuous f) (s : Set α) :
  UpperSemicontinuousOn f s :=
  fun x hx => h.upper_semicontinuous_within_at s x

/-! #### Constants -/


theorem upper_semicontinuous_within_at_const : UpperSemicontinuousWithinAt (fun x => z) s x :=
  fun y hy => Filter.eventually_of_forall fun x => hy

theorem upper_semicontinuous_at_const : UpperSemicontinuousAt (fun x => z) x :=
  fun y hy => Filter.eventually_of_forall fun x => hy

theorem upper_semicontinuous_on_const : UpperSemicontinuousOn (fun x => z) s :=
  fun x hx => upper_semicontinuous_within_at_const

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem upper_semicontinuous_const : upper_semicontinuous (λ x : α, z) := λ x, upper_semicontinuous_at_const

/-! #### Indicators -/


section 

variable[HasZero β]

theorem IsOpen.upper_semicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
  UpperSemicontinuous (indicator s fun x => y) :=
  @IsOpen.lower_semicontinuous_indicator α _ (OrderDual β) _ s y _ hs hy

theorem IsOpen.upper_semicontinuous_on_indicator (hs : IsOpen s) (hy : y ≤ 0) :
  UpperSemicontinuousOn (indicator s fun x => y) t :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousOn t

theorem IsOpen.upper_semicontinuous_at_indicator (hs : IsOpen s) (hy : y ≤ 0) :
  UpperSemicontinuousAt (indicator s fun x => y) x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousAt x

theorem IsOpen.upper_semicontinuous_within_at_indicator (hs : IsOpen s) (hy : y ≤ 0) :
  UpperSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousWithinAt t x

theorem IsClosed.upper_semicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
  UpperSemicontinuous (indicator s fun x => y) :=
  @IsClosed.lower_semicontinuous_indicator α _ (OrderDual β) _ s y _ hs hy

theorem IsClosed.upper_semicontinuous_on_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
  UpperSemicontinuousOn (indicator s fun x => y) t :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousOn t

theorem IsClosed.upper_semicontinuous_at_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
  UpperSemicontinuousAt (indicator s fun x => y) x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousAt x

theorem IsClosed.upper_semicontinuous_within_at_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
  UpperSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.upper_semicontinuous_indicator hy).UpperSemicontinuousWithinAt t x

end 

/-! #### Relationship with continuity -/


theorem upper_semicontinuous_iff_is_open : UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => is_open_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt => IsOpen.mem_nhds (H y) y_lt⟩

theorem UpperSemicontinuous.is_open_preimage (hf : UpperSemicontinuous f) (y : β) : IsOpen (f ⁻¹' Iio y) :=
  upper_semicontinuous_iff_is_open.1 hf y

section 

variable{γ : Type _}[LinearOrderₓ γ][TopologicalSpace γ][OrderTopology γ]

theorem ContinuousWithinAt.upper_semicontinuous_within_at {f : α → γ} (h : ContinuousWithinAt f s x) :
  UpperSemicontinuousWithinAt f s x :=
  fun y hy => h (Iio_mem_nhds hy)

theorem ContinuousAt.upper_semicontinuous_at {f : α → γ} (h : ContinuousAt f x) : UpperSemicontinuousAt f x :=
  fun y hy => h (Iio_mem_nhds hy)

theorem ContinuousOn.upper_semicontinuous_on {f : α → γ} (h : ContinuousOn f s) : UpperSemicontinuousOn f s :=
  fun x hx => (h x hx).UpperSemicontinuousWithinAt

theorem Continuous.upper_semicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun x => h.continuous_at.upper_semicontinuous_at

end 

/-! ### Composition -/


section 

variable{γ : Type _}[LinearOrderₓ γ][TopologicalSpace γ][OrderTopology γ]

variable{δ : Type _}[LinearOrderₓ δ][TopologicalSpace δ][OrderTopology δ]

theorem ContinuousAt.comp_upper_semicontinuous_within_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) : UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lower_semicontinuous_within_at α _ x s (OrderDual γ) _ _ _ (OrderDual δ) _ _ _ g f hg hf
    fun x y hxy => gmon hxy

theorem ContinuousAt.comp_upper_semicontinuous_at {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lower_semicontinuous_at α _ x (OrderDual γ) _ _ _ (OrderDual δ) _ _ _ g f hg hf
    fun x y hxy => gmon hxy

theorem Continuous.comp_upper_semicontinuous_on {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuous_at.comp_upper_semicontinuous_within_at (hf x hx) gmon

theorem Continuous.comp_upper_semicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g) (hf : UpperSemicontinuous f)
  (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) :=
  fun x => hg.continuous_at.comp_upper_semicontinuous_at (hf x) gmon

theorem ContinuousAt.comp_upper_semicontinuous_within_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) : LowerSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_upper_semicontinuous_within_at α _ x s γ _ _ _ (OrderDual δ) _ _ _ g f hg hf gmon

theorem ContinuousAt.comp_upper_semicontinuous_at_antitone {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
  (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) : LowerSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_upper_semicontinuous_at α _ x γ _ _ _ (OrderDual δ) _ _ _ g f hg hf gmon

theorem Continuous.comp_upper_semicontinuous_on_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuous_at.comp_upper_semicontinuous_within_at_antitone (hf x hx) gmon

theorem Continuous.comp_upper_semicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
  (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) :=
  fun x => hg.continuous_at.comp_upper_semicontinuous_at_antitone (hf x) gmon

end 

/-! #### Addition -/


section 

variable{ι : Type _}{γ : Type _}[LinearOrderedAddCommMonoid γ][TopologicalSpace γ][OrderTopology γ]

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem upper_semicontinuous_within_at.add'
{f g : α → γ}
(hf : upper_semicontinuous_within_at f s x)
(hg : upper_semicontinuous_within_at g s x)
(hcont : continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : upper_semicontinuous_within_at (λ
 z, «expr + »(f z, g z)) s x :=
@lower_semicontinuous_within_at.add' α _ x s (order_dual γ) _ _ _ _ _ hf hg hcont

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem upper_semicontinuous_at.add'
{f g : α → γ}
(hf : upper_semicontinuous_at f x)
(hg : upper_semicontinuous_at g x)
(hcont : continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : upper_semicontinuous_at (λ z, «expr + »(f z, g z)) x :=
by { simp_rw ["[", "<-", expr upper_semicontinuous_within_at_univ_iff, "]"] ["at", "*"],
  exact [expr hf.add' hg hcont] }

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem upper_semicontinuous_on.add'
{f g : α → γ}
(hf : upper_semicontinuous_on f s)
(hg : upper_semicontinuous_on g s)
(hcont : ∀
 x «expr ∈ » s, continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : upper_semicontinuous_on (λ z, «expr + »(f z, g z)) s :=
λ x hx, (hf x hx).add' (hg x hx) (hcont x hx)

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem upper_semicontinuous.add'
{f g : α → γ}
(hf : upper_semicontinuous f)
(hg : upper_semicontinuous g)
(hcont : ∀
 x, continuous_at (λ
  p : «expr × »(γ, γ), «expr + »(p.1, p.2)) (f x, g x)) : upper_semicontinuous (λ z, «expr + »(f z, g z)) :=
λ x, (hf x).add' (hg x) (hcont x)

variable[HasContinuousAdd γ]

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
  (hg : UpperSemicontinuousWithinAt g s x) : UpperSemicontinuousWithinAt (fun z => f z+g z) s x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x) (hg : UpperSemicontinuousAt g x) :
  UpperSemicontinuousAt (fun z => f z+g z) x :=
  hf.add' hg continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
  UpperSemicontinuousOn (fun z => f z+g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt

/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
  UpperSemicontinuous fun z => f z+g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt

theorem upper_semicontinuous_within_at_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), UpperSemicontinuousWithinAt (f i) s x) :
  UpperSemicontinuousWithinAt (fun z => ∑i in a, f i z) s x :=
  @lower_semicontinuous_within_at_sum α _ x s ι (OrderDual γ) _ _ _ _ f a ha

theorem upper_semicontinuous_at_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), UpperSemicontinuousAt (f i) x) : UpperSemicontinuousAt (fun z => ∑i in a, f i z) x :=
  by 
    simpRw [←upper_semicontinuous_within_at_univ_iff]  at *
    exact upper_semicontinuous_within_at_sum ha

theorem upper_semicontinuous_on_sum {f : ι → α → γ} {a : Finset ι}
  (ha : ∀ i (_ : i ∈ a), UpperSemicontinuousOn (f i) s) : UpperSemicontinuousOn (fun z => ∑i in a, f i z) s :=
  fun x hx => upper_semicontinuous_within_at_sum fun i hi => ha i hi x hx

theorem upper_semicontinuous_sum {f : ι → α → γ} {a : Finset ι} (ha : ∀ i (_ : i ∈ a), UpperSemicontinuous (f i)) :
  UpperSemicontinuous fun z => ∑i in a, f i z :=
  fun x => upper_semicontinuous_at_sum fun i hi => ha i hi x

end 

/-! #### Infimum -/


section 

variable{ι : Sort _}{δ : Type _}[CompleteLinearOrder δ]

theorem upper_semicontinuous_within_at_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
  UpperSemicontinuousWithinAt (fun x' => ⨅i, f i x') s x :=
  @lower_semicontinuous_within_at_supr α _ x s ι (OrderDual δ) _ f h

theorem upper_semicontinuous_within_at_binfi {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
  UpperSemicontinuousWithinAt (fun x' => ⨅i hi, f i hi x') s x :=
  upper_semicontinuous_within_at_infi$ fun i => upper_semicontinuous_within_at_infi$ fun hi => h i hi

theorem upper_semicontinuous_at_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
  UpperSemicontinuousAt (fun x' => ⨅i, f i x') x :=
  @lower_semicontinuous_at_supr α _ x ι (OrderDual δ) _ f h

theorem upper_semicontinuous_at_binfi {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) : UpperSemicontinuousAt (fun x' => ⨅i hi, f i hi x') x :=
  upper_semicontinuous_at_infi$ fun i => upper_semicontinuous_at_infi$ fun hi => h i hi

theorem upper_semicontinuous_on_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
  UpperSemicontinuousOn (fun x' => ⨅i, f i x') s :=
  fun x hx => upper_semicontinuous_within_at_infi fun i => h i x hx

theorem upper_semicontinuous_on_binfi {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) : UpperSemicontinuousOn (fun x' => ⨅i hi, f i hi x') s :=
  upper_semicontinuous_on_infi$ fun i => upper_semicontinuous_on_infi$ fun hi => h i hi

theorem upper_semicontinuous_infi {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
  UpperSemicontinuous fun x' => ⨅i, f i x' :=
  fun x => upper_semicontinuous_at_infi fun i => h i x

theorem upper_semicontinuous_binfi {p : ι → Prop} {f : ∀ i (h : p i), α → δ}
  (h : ∀ i hi, UpperSemicontinuous (f i hi)) : UpperSemicontinuous fun x' => ⨅i hi, f i hi x' :=
  upper_semicontinuous_infi$ fun i => upper_semicontinuous_infi$ fun hi => h i hi

end 

section 

variable{γ : Type _}[LinearOrderₓ γ][TopologicalSpace γ][OrderTopology γ]

-- error in Topology.Semicontinuous: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_within_at_iff_lower_upper_semicontinuous_within_at
{f : α → γ} : «expr ↔ »(continuous_within_at f s x, «expr ∧ »(lower_semicontinuous_within_at f s x, upper_semicontinuous_within_at f s x)) :=
begin
  refine [expr ⟨λ h, ⟨h.lower_semicontinuous_within_at, h.upper_semicontinuous_within_at⟩, _⟩],
  rintros ["⟨", ident h₁, ",", ident h₂, "⟩"],
  assume [binders (v hv)],
  simp [] [] ["only"] ["[", expr filter.mem_map, "]"] [] [],
  by_cases [expr Hl, ":", expr «expr∃ , »((l), «expr < »(l, f x))],
  { rcases [expr exists_Ioc_subset_of_mem_nhds hv Hl, "with", "⟨", ident l, ",", ident lfx, ",", ident hl, "⟩"],
    by_cases [expr Hu, ":", expr «expr∃ , »((u), «expr < »(f x, u))],
    { rcases [expr exists_Ico_subset_of_mem_nhds hv Hu, "with", "⟨", ident u, ",", ident fxu, ",", ident hu, "⟩"],
      filter_upwards ["[", expr h₁ l lfx, ",", expr h₂ u fxu, "]"] [],
      assume [binders (a lfa fau)],
      cases [expr le_or_gt (f a) (f x)] ["with", ident h, ident h],
      { exact [expr hl ⟨lfa, h⟩] },
      { exact [expr hu ⟨le_of_lt h, fau⟩] } },
    { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident Hu],
      filter_upwards ["[", expr h₁ l lfx, "]"] [],
      assume [binders (a lfa)],
      exact [expr hl ⟨lfa, Hu (f a)⟩] } },
  { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident Hl],
    by_cases [expr Hu, ":", expr «expr∃ , »((u), «expr < »(f x, u))],
    { rcases [expr exists_Ico_subset_of_mem_nhds hv Hu, "with", "⟨", ident u, ",", ident fxu, ",", ident hu, "⟩"],
      filter_upwards ["[", expr h₂ u fxu, "]"] [],
      assume [binders (a lfa)],
      apply [expr hu],
      exact [expr ⟨Hl (f a), lfa⟩] },
    { simp [] [] ["only"] ["[", expr not_exists, ",", expr not_lt, "]"] [] ["at", ident Hu],
      apply [expr filter.eventually_of_forall],
      assume [binders (a)],
      have [] [":", expr «expr = »(f a, f x)] [":=", expr le_antisymm (Hu _) (Hl _)],
      rw [expr this] [],
      exact [expr mem_of_mem_nhds hv] } }
end

theorem continuous_at_iff_lower_upper_semicontinuous_at {f : α → γ} :
  ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x :=
  by 
    simpRw [←continuous_within_at_univ, ←lower_semicontinuous_within_at_univ_iff,
      ←upper_semicontinuous_within_at_univ_iff, continuous_within_at_iff_lower_upper_semicontinuous_within_at]

theorem continuous_on_iff_lower_upper_semicontinuous_on {f : α → γ} :
  ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s :=
  by 
    simp only [ContinuousOn, continuous_within_at_iff_lower_upper_semicontinuous_within_at]
    exact ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

theorem continuous_iff_lower_upper_semicontinuous {f : α → γ} :
  Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f :=
  by 
    simpRw [continuous_iff_continuous_on_univ, continuous_on_iff_lower_upper_semicontinuous_on,
      lower_semicontinuous_on_univ_iff, upper_semicontinuous_on_univ_iff]

end 

