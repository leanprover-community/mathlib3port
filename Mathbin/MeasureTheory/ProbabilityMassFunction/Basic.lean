import Mathbin.Topology.Instances.Ennreal 
import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0` such that the values have (infinite) sum `1`.

This file features the monadic structure of `pmf`,
other constructions of `pmf`s are found in `probability_mass_function/constructions.lean`

Given `p : pmf α`, `pmf.to_outer_measure` constructs an `outer_measure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `measure` on `α`, see `pmf.to_measure`.
`pmf.to_measure.is_probability_measure` shows this associated measure is a probability measure.

## Tags

probability mass function, discrete probability measure
-/


noncomputable theory

variable{α : Type _}{β : Type _}{γ : Type _}

open_locale Classical BigOperators Nnreal Ennreal

/-- A probability mass function, or discrete probability measures is a function `α → ℝ≥0` such that
  the values have (infinite) sum `1`. -/
def Pmf.{u} (α : Type u) : Type u :=
  { f : α →  ℝ≥0  // HasSum f 1 }

namespace Pmf

instance  : CoeFun (Pmf α) fun p => α →  ℝ≥0  :=
  ⟨fun p a => p.1 a⟩

@[ext]
protected theorem ext : ∀ {p q : Pmf α}, (∀ a, p a = q a) → p = q
| ⟨f, hf⟩, ⟨g, hg⟩, Eq => Subtype.eq$ funext Eq

theorem has_sum_coe_one (p : Pmf α) : HasSum p 1 :=
  p.2

theorem summable_coe (p : Pmf α) : Summable p :=
  p.has_sum_coe_one.Summable

@[simp]
theorem tsum_coe (p : Pmf α) : (∑'a, p a) = 1 :=
  p.has_sum_coe_one.tsum_eq

/-- The support of a `pmf` is the set where it is nonzero. -/
def support (p : Pmf α) : Set α :=
  Function.Support p

@[simp]
theorem mem_support_iff (p : Pmf α) (a : α) : a ∈ p.support ↔ p a ≠ 0 :=
  Iff.rfl

theorem apply_eq_zero_iff (p : Pmf α) (a : α) : p a = 0 ↔ a ∉ p.support :=
  by 
    rw [mem_support_iff, not_not]

theorem coe_le_one (p : Pmf α) (a : α) : p a ≤ 1 :=
  has_sum_le
    (by 
      intro b 
      splitIfs <;> simp only [h, zero_le'])
    (has_sum_ite_eq a (p a)) (has_sum_coe_one p)

section Pure

/-- The pure `pmf` is the `pmf` where all the mass lies in one point.
  The value of `pure a` is `1` at `a` and `0` elsewhere. -/
def pure (a : α) : Pmf α :=
  ⟨fun a' => if a' = a then 1 else 0, has_sum_ite_eq _ _⟩

@[simp]
theorem pure_apply (a a' : α) : pure a a' = if a' = a then 1 else 0 :=
  rfl

theorem mem_support_pure_iff (a a' : α) : a' ∈ (pure a).Support ↔ a' = a :=
  by 
    simp 

instance  [Inhabited α] : Inhabited (Pmf α) :=
  ⟨pure (default α)⟩

end Pure

section Bind

-- error in MeasureTheory.ProbabilityMassFunction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
protected theorem bind.summable (p : pmf α) (f : α → pmf β) (b : β) : summable (λ a : α, «expr * »(p a, f a b)) :=
begin
  refine [expr nnreal.summable_of_le (assume a, _) p.summable_coe],
  suffices [] [":", expr «expr ≤ »(«expr * »(p a, f a b), «expr * »(p a, 1))],
  { simpa [] [] [] [] [] [] },
  exact [expr mul_le_mul_of_nonneg_left ((f a).coe_le_one _) (p a).2]
end

/-- The monadic bind operation for `pmf`. -/
def bind (p : Pmf α) (f : α → Pmf β) : Pmf β :=
  ⟨fun b => ∑'a, p a*f a b,
    by 
      apply Ennreal.has_sum_coe.1
      simp only [Ennreal.coe_tsum (bind.summable p f _)]
      rw [ennreal.summable.has_sum_iff, Ennreal.tsum_comm]
      simp [Ennreal.tsum_mul_left, (Ennreal.coe_tsum (f _).summable_coe).symm, (Ennreal.coe_tsum p.summable_coe).symm]⟩

@[simp]
theorem bind_apply (p : Pmf α) (f : α → Pmf β) (b : β) : p.bind f b = ∑'a, p a*f a b :=
  rfl

theorem coe_bind_apply (p : Pmf α) (f : α → Pmf β) (b : β) : (p.bind f b : ℝ≥0∞) = ∑'a, p a*f a b :=
  Eq.trans (Ennreal.coe_tsum$ bind.summable p f b)$
    by 
      simp 

@[simp]
theorem pure_bind (a : α) (f : α → Pmf β) : (pure a).bind f = f a :=
  have  : ∀ b a', (ite (a' = a) 1 0*f a' b) = ite (a' = a) (f a b) 0 :=
    fun b a' =>
      by 
        splitIfs <;> simp  <;> subst h <;> simp 
  by 
    ext b <;> simp [this]

@[simp]
theorem bind_pureₓ (p : Pmf α) : p.bind pure = p :=
  have  : ∀ a a', (p a*ite (a' = a) 1 0) = ite (a = a') (p a') 0 :=
    fun a a' =>
      by 
        splitIfs <;>
          try 
              subst a <;>
            try 
                subst a' <;>
              simp_all 
  by 
    ext b <;> simp [this]

@[simp]
theorem bind_bind (p : Pmf α) (f : α → Pmf β) (g : β → Pmf γ) : (p.bind f).bind g = p.bind fun a => (f a).bind g :=
  by 
    ext1 b 
    simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
    rw [Ennreal.tsum_comm]
    simp [mul_assocₓ, mul_left_commₓ, mul_commₓ]

theorem bind_comm (p : Pmf α) (q : Pmf β) (f : α → β → Pmf γ) :
  (p.bind fun a => q.bind (f a)) = q.bind fun b => p.bind fun a => f a b :=
  by 
    ext1 b 
    simp only [ennreal.coe_eq_coe.symm, coe_bind_apply, ennreal.tsum_mul_left.symm, ennreal.tsum_mul_right.symm]
    rw [Ennreal.tsum_comm]
    simp [mul_assocₓ, mul_left_commₓ, mul_commₓ]

end Bind

instance  : Monadₓ Pmf :=
  { pure := fun A a => pure a, bind := fun A B pa pb => pa.bind pb }

section OuterMeasure

open MeasureTheory MeasureTheory.OuterMeasure

-- error in MeasureTheory.ProbabilityMassFunction.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Construct an `outer_measure` from a `pmf`, by assigning measure to each set `s : set α` equal
  to the sum of `p x` for for each `x ∈ α` -/ def to_outer_measure (p : pmf α) : outer_measure α :=
outer_measure.sum (λ x : α, «expr • »(p x, dirac x))

theorem to_outer_measure_apply (p : Pmf α) (s : Set α) :
  p.to_outer_measure s = ∑'x, s.indicator (fun x => (p x : ℝ≥0∞)) x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

theorem to_outer_measure_apply' (p : Pmf α) (s : Set α) : p.to_outer_measure s = «expr↑ » (∑'x : α, s.indicator p x) :=
  by 
    simp only [Ennreal.coe_tsum (Nnreal.indicator_summable (summable_coe p) s), Ennreal.coe_indicator,
      to_outer_measure_apply]

@[simp]
theorem to_outer_measure_apply_finset (p : Pmf α) (s : Finset α) : p.to_outer_measure s = ∑x in s, (p x : ℝ≥0∞) :=
  by 
    refine' (to_outer_measure_apply p s).trans ((@tsum_eq_sum _ _ _ _ _ _ s _).trans _)
    ·
      exact fun x hx => Set.indicator_of_not_mem hx _
    ·
      exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem hx _

@[simp]
theorem to_outer_measure_apply_fintype [Fintype α] (p : Pmf α) (s : Set α) :
  p.to_outer_measure s = ∑x, s.indicator (fun x => (p x : ℝ≥0∞)) x :=
  (p.to_outer_measure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

theorem to_outer_measure_apply_eq_zero_iff (p : Pmf α) (s : Set α) : p.to_outer_measure s = 0 ↔ Disjoint p.support s :=
  by 
    rw [to_outer_measure_apply', Ennreal.coe_eq_zero, tsum_eq_zero_iff (Nnreal.indicator_summable (summable_coe p) s)]
    exact function.funext_iff.symm.trans Set.indicator_eq_zero'

@[simp]
theorem to_outer_measure_caratheodory (p : Pmf α) : (to_outer_measure p).caratheodory = ⊤ :=
  by 
    refine' eq_top_iff.2$ le_transₓ (le_Inf$ fun x hx => _) (le_sum_caratheodory _)
    obtain ⟨y, hy⟩ := hx 
    exact ((le_of_eqₓ (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eqₓ hy)

end OuterMeasure

section Measureₓ

open MeasureTheory

/-- Since every set is Carathéodory-measurable under `pmf.to_outer_measure`,
  we can further extend this `outer_measure` to a `measure` on `α` -/
def to_measure [MeasurableSpace α] (p : Pmf α) : Measureₓ α :=
  p.to_outer_measure.to_measure ((to_outer_measure_caratheodory p).symm ▸ le_top)

variable[MeasurableSpace α]

theorem to_measure_apply_eq_to_outer_measure_apply (p : Pmf α) (s : Set α) (hs : MeasurableSet s) :
  p.to_measure s = p.to_outer_measure s :=
  to_measure_apply p.to_outer_measure _ hs

theorem to_outer_measure_apply_le_to_measure_apply (p : Pmf α) (s : Set α) : p.to_outer_measure s ≤ p.to_measure s :=
  le_to_measure_apply p.to_outer_measure _ s

theorem to_measure_apply (p : Pmf α) (s : Set α) (hs : MeasurableSet s) :
  p.to_measure s = ∑'x, s.indicator (fun x => (p x : ℝ≥0∞)) x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply s)

theorem to_measure_apply' (p : Pmf α) (s : Set α) (hs : MeasurableSet s) :
  p.to_measure s = «expr↑ » (∑'x, s.indicator p x) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs).trans (p.to_outer_measure_apply' s)

@[simp]
theorem to_measure_apply_finset [MeasurableSingletonClass α] (p : Pmf α) (s : Finset α) :
  p.to_measure s = ∑x in s, (p x : ℝ≥0∞) :=
  (p.to_measure_apply_eq_to_outer_measure_apply s s.measurable_set).trans (p.to_outer_measure_apply_finset s)

theorem to_measure_apply_of_finite [MeasurableSingletonClass α] (p : Pmf α) (s : Set α) (hs : s.finite) :
  p.to_measure s = ∑'x, s.indicator (fun x => (p x : ℝ≥0∞)) x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s hs.measurable_set).trans (p.to_outer_measure_apply s)

@[simp]
theorem to_measure_apply_fintype [MeasurableSingletonClass α] [Fintype α] (p : Pmf α) (s : Set α) :
  p.to_measure s = ∑x, s.indicator (fun x => (p x : ℝ≥0∞)) x :=
  (p.to_measure_apply_eq_to_outer_measure_apply s (Set.Finite.of_fintype s).MeasurableSet).trans
    (p.to_outer_measure_apply_fintype s)

/-- The measure associated to a `pmf` by `to_measure` is a probability measure -/
instance to_measure.is_probability_measure (p : Pmf α) : is_probability_measure p.to_measure :=
  ⟨by 
      simpa only [MeasurableSet.univ, to_measure_apply_eq_to_outer_measure_apply, Set.indicator_univ,
        to_outer_measure_apply', Ennreal.coe_eq_one] using tsum_coe p⟩

end Measureₓ

end Pmf

