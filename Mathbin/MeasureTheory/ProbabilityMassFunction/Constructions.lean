import Mathbin.MeasureTheory.ProbabilityMassFunction.Basic

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `pmf` constructions for common probability distributions.

`map` and `seq` allow pushing a `pmf α` along a function `f : α → β` (or distribution of
functions `f : pmf (α → β)`) to get a `pmf β`

`of_finset` and `of_fintype` simplify the construction of a `pmf α` from a function `f : α → ℝ≥0`,
by allowing the "sum equals 1" constraint to be in terms of `finset.sum` instead of `tsum`.
`of_multiset`, `uniform_of_finset`, and `uniform_of_fintype` construct probability mass functions
from the corresponding object, with proportional weighting for each element of the object.

`normalize` constructs a `pmf α` by normalizing a function `f : α → ℝ≥0` by its sum,
and `filter` uses this to filter the support of a `pmf` and re-normalize the new distribution.

`bind_on_support` generalizes `bind` to allow binding to a partial function,
so that the second argument only needs to be defined on the support of the first argument.

`bernoulli` represents the bernoulli distribution on `bool`

-/


namespace Pmf

noncomputable theory

variable{α : Type _}{β : Type _}{γ : Type _}

open_locale Classical BigOperators Nnreal Ennreal

section Map

/-- The functorial action of a function on a `pmf`. -/
def map (f : α → β) (p : Pmf α) : Pmf β :=
  bind p (pure ∘ f)

theorem bind_pure_comp (f : α → β) (p : Pmf α) : bind p (pure ∘ f) = map f p :=
  rfl

theorem map_id (p : Pmf α) : map id p = p :=
  by 
    simp [map]

theorem map_comp (p : Pmf α) (f : α → β) (g : β → γ) : (p.map f).map g = p.map (g ∘ f) :=
  by 
    simp [map]

theorem pure_map (a : α) (f : α → β) : (pure a).map f = pure (f a) :=
  by 
    simp [map]

end Map

section Seq

/-- The monadic sequencing operation for `pmf`. -/
def seq (f : Pmf (α → β)) (p : Pmf α) : Pmf β :=
  f.bind fun m => p.bind$ fun a => pure (m a)

end Seq

section OfFinite

/-- Given a finset `s` and a function `f : α → ℝ≥0` with sum `1` on `s`,
  such that `f x = 0` for `x ∉ s`, we get a `pmf` -/
def of_finset (f : α →  ℝ≥0 ) (s : Finset α) (h : (∑x in s, f x) = 1) (h' : ∀ x _ : x ∉ s, f x = 0) : Pmf α :=
  ⟨f, h ▸ has_sum_sum_of_ne_finset_zero h'⟩

@[simp]
theorem of_finset_apply {f : α →  ℝ≥0 } {s : Finset α} (h : (∑x in s, f x) = 1) (h' : ∀ x _ : x ∉ s, f x = 0) (a : α) :
  of_finset f s h h' a = f a :=
  rfl

theorem of_finset_apply_of_not_mem {f : α →  ℝ≥0 } {s : Finset α} (h : (∑x in s, f x) = 1) (h' : ∀ x _ : x ∉ s, f x = 0)
  {a : α} (ha : a ∉ s) : of_finset f s h h' a = 0 :=
  h' a ha

/-- Given a finite type `α` and a function `f : α → ℝ≥0` with sum 1, we get a `pmf`. -/
def of_fintype [Fintype α] (f : α →  ℝ≥0 ) (h : (∑x, f x) = 1) : Pmf α :=
  of_finset f Finset.univ h fun x hx => absurd (Finset.mem_univ x) hx

@[simp]
theorem of_fintype_apply [Fintype α] {f : α →  ℝ≥0 } (h : (∑x, f x) = 1) (a : α) : of_fintype f h a = f a :=
  rfl

-- error in MeasureTheory.ProbabilityMassFunction.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a non-empty multiset `s` we construct the `pmf` which sends `a` to the fraction of
  elements in `s` that are `a`. -/ def of_multiset (s : multiset α) (hs : «expr ≠ »(s, 0)) : pmf α :=
⟨λ
 a, «expr / »(s.count a, s.card), have «expr = »(«expr∑ in , »((a), s.to_finset, «expr / »((s.count a : exprℝ()), s.card)), 1), by simp [] [] [] ["[", expr div_eq_inv_mul, ",", expr finset.mul_sum.symm, ",", expr (nat.cast_sum _ _).symm, ",", expr hs, "]"] [] [],
 have «expr = »(«expr∑ in , »((a), s.to_finset, «expr / »((s.count a : «exprℝ≥0»()), s.card)), 1), by rw ["[", "<-", expr nnreal.eq_iff, ",", expr nnreal.coe_one, ",", "<-", expr this, ",", expr nnreal.coe_sum, "]"] []; simp [] [] [] [] [] [],
 begin
   rw ["<-", expr this] [],
   apply [expr has_sum_sum_of_ne_finset_zero],
   simp [] [] [] [] [] [] { contextual := tt }
 end⟩

@[simp]
theorem of_multiset_apply {s : Multiset α} (hs : s ≠ 0) (a : α) : of_multiset s hs a = s.count a / s.card :=
  rfl

theorem of_multiset_apply_of_not_mem {s : Multiset α} (hs : s ≠ 0) {a : α} (ha : a ∉ s) : of_multiset s hs a = 0 :=
  div_eq_zero_iff.2 (Or.inl$ Nat.cast_eq_zero.2$ Multiset.count_eq_zero_of_not_mem ha)

end OfFinite

section Uniform

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s` -/
def uniform_of_finset (s : Finset α) (hs : s.nonempty) : Pmf α :=
  of_finset (fun a => if a ∈ s then (s.card :  ℝ≥0 )⁻¹ else 0) s
    (Exists.rec_on hs
      fun x hx =>
        calc (∑a : α in s, ite (a ∈ s) ((s.card :  ℝ≥0 )⁻¹) 0) = ∑a : α in s, (s.card :  ℝ≥0 )⁻¹ :=
          Finset.sum_congr rfl
            fun x hx =>
              by 
                simp [hx]
          _ = s.card • (s.card :  ℝ≥0 )⁻¹ := Finset.sum_const _ 
          _ = (s.card :  ℝ≥0 )*(s.card :  ℝ≥0 )⁻¹ :=
          by 
            rw [nsmul_eq_mul]
          _ = 1 := div_self (Nat.cast_ne_zero.2$ Finset.card_ne_zero_of_mem hx)
          )
    fun x hx =>
      by 
        simp only [hx, if_false]

@[simp]
theorem uniform_of_finset_apply {s : Finset α} (hs : s.nonempty) (a : α) :
  uniform_of_finset s hs a = if a ∈ s then (s.card :  ℝ≥0 )⁻¹ else 0 :=
  rfl

theorem uniform_of_finset_apply_of_mem {s : Finset α} (hs : s.nonempty) {a : α} (ha : a ∈ s) :
  uniform_of_finset s hs a = s.card⁻¹ :=
  by 
    simp [ha]

theorem uniform_of_finset_apply_of_not_mem {s : Finset α} (hs : s.nonempty) {a : α} (ha : a ∉ s) :
  uniform_of_finset s hs a = 0 :=
  by 
    simp [ha]

/-- The uniform pmf taking the same uniform value on all of the fintype `α` -/
def uniform_of_fintype (α : Type _) [Fintype α] [Nonempty α] : Pmf α :=
  uniform_of_finset Finset.univ Finset.univ_nonempty

@[simp]
theorem uniform_of_fintype_apply [Fintype α] [Nonempty α] (a : α) : uniform_of_fintype α a = Fintype.card α⁻¹ :=
  by 
    simpa only [uniform_of_fintype, Finset.mem_univ, if_true, uniform_of_finset_apply]

end Uniform

section Normalize

/-- Given a `f` with non-zero sum, we get a `pmf` by normalizing `f` by it's `tsum` -/
def normalize (f : α →  ℝ≥0 ) (hf0 : tsum f ≠ 0) : Pmf α :=
  ⟨fun a => f a*(∑'x, f x)⁻¹,
    mul_inv_cancel hf0 ▸
      HasSum.mul_right ((∑'x, f x)⁻¹) (not_not.mp (mt tsum_eq_zero_of_not_summable hf0 : ¬¬Summable f)).HasSum⟩

theorem normalize_apply {f : α →  ℝ≥0 } (hf0 : tsum f ≠ 0) (a : α) : (normalize f hf0) a = f a*(∑'x, f x)⁻¹ :=
  rfl

end Normalize

section Filter

/-- Create new `pmf` by filtering on a set with non-zero measure and normalizing -/
def Filter (p : Pmf α) (s : Set α) (h : ∃ (a : _)(_ : a ∈ s), p a ≠ 0) : Pmf α :=
  Pmf.normalize (s.indicator p)$ Nnreal.tsum_indicator_ne_zero p.2.Summable h

theorem filter_apply (p : Pmf α) {s : Set α} (h : ∃ (a : _)(_ : a ∈ s), p a ≠ 0) {a : α} :
  (p.filter s h) a = s.indicator p a*(∑'x, (s.indicator p) x)⁻¹ :=
  by 
    rw [Filter, normalize_apply]

theorem filter_apply_eq_zero_of_not_mem (p : Pmf α) {s : Set α} (h : ∃ (a : _)(_ : a ∈ s), p a ≠ 0) {a : α}
  (ha : a ∉ s) : (p.filter s h) a = 0 :=
  by 
    rw [filter_apply, set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha, zero_mul]

theorem filter_apply_eq_zero_iff (p : Pmf α) {s : Set α} (h : ∃ (a : _)(_ : a ∈ s), p a ≠ 0) (a : α) :
  (p.filter s h) a = 0 ↔ a ∉ p.support ∩ s :=
  by 
    rw [Set.mem_inter_iff, p.mem_support_iff, not_and_distrib, not_not]
    split  <;> intro ha
    ·
      rw [filter_apply, mul_eq_zero] at ha 
      refine'
        ha.by_cases (fun ha => (em (a ∈ s)).byCases (fun h => Or.inl ((set.indicator_apply_eq_zero.mp ha) h)) Or.inr)
          fun ha => absurd (inv_eq_zero.1 ha) (Nnreal.tsum_indicator_ne_zero p.2.Summable h)
    ·
      rw [filter_apply, Set.indicator_apply_eq_zero.2 fun h => ha.by_cases id (absurd h), zero_mul]

theorem filter_apply_ne_zero_iff (p : Pmf α) {s : Set α} (h : ∃ (a : _)(_ : a ∈ s), p a ≠ 0) (a : α) :
  (p.filter s h) a ≠ 0 ↔ a ∈ p.support ∩ s :=
  by 
    rw [←not_iff, filter_apply_eq_zero_iff, not_iff, not_not]

end Filter

section Bernoulli

/-- A `pmf` which assigns probability `p` to `tt` and `1 - p` to `ff`. -/
def bernoulli (p :  ℝ≥0 ) (h : p ≤ 1) : Pmf Bool :=
  of_fintype (fun b => cond b p (1 - p))
    (Nnreal.eq$
      by 
        simp [h])

@[simp]
theorem bernuolli_apply {p :  ℝ≥0 } (h : p ≤ 1) (b : Bool) : bernoulli p h b = cond b p (1 - p) :=
  rfl

end Bernoulli

section BindOnSupport

protected theorem bind_on_support.summable (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β) (b : β) :
  Summable fun a : α => p a*if h : p a = 0 then 0 else f a h b :=
  by 
    refine' Nnreal.summable_of_le (fun a => _) p.summable_coe 
    splitIfs
    ·
      refine' (mul_zero (p a)).symm ▸ le_of_eqₓ h.symm
    ·
      suffices  : (p a*f a h b) ≤ p a*1
      ·
        simpa 
      exact mul_le_mul_of_nonneg_left ((f a h).coe_le_one _) (p a).2

-- error in MeasureTheory.ProbabilityMassFunction.Constructions: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Generalized version of `bind` allowing `f` to only be defined on the support of `p`.
  `p.bind f` is equivalent to `p.bind_on_support (λ a _, f a)`, see `bind_on_support_eq_bind` -/
def bind_on_support (p : pmf α) (f : ∀ a «expr ∈ » p.support, pmf β) : pmf β :=
⟨λ
 b, «expr∑' , »((a), «expr * »(p a, if h : «expr = »(p a, 0) then 0 else f a h b)), ennreal.has_sum_coe.1 (begin
    simp [] [] ["only"] ["[", expr ennreal.coe_tsum (bind_on_support.summable p f _), "]"] [] [],
    rw ["[", expr ennreal.summable.has_sum_iff, ",", expr ennreal.tsum_comm, "]"] [],
    simp [] [] ["only"] ["[", expr ennreal.coe_mul, ",", expr ennreal.coe_one, ",", expr ennreal.tsum_mul_left, "]"] [] [],
    have [] [":", expr «expr = »(«expr∑' , »((a : α), (p a : ennreal)), 1)] [":=", expr by simp [] [] ["only"] ["[", "<-", expr ennreal.coe_tsum p.summable_coe, ",", expr ennreal.coe_one, ",", expr tsum_coe, "]"] [] []],
    refine [expr trans (tsum_congr (λ a, _)) this],
    split_ifs [] ["with", ident h],
    { simp [] [] [] ["[", expr h, "]"] [] [] },
    { simp [] [] [] ["[", "<-", expr ennreal.coe_tsum (f a h).summable_coe, ",", expr (f a h).tsum_coe, "]"] [] [] }
  end)⟩

@[simp]
theorem bind_on_support_apply (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β) (b : β) :
  p.bind_on_support f b = ∑'a, p a*if h : p a = 0 then 0 else f a h b :=
  rfl

/-- `bind_on_support` reduces to `bind` if `f` doesn't depend on the additional hypothesis -/
@[simp]
theorem bind_on_support_eq_bind (p : Pmf α) (f : α → Pmf β) : (p.bind_on_support fun a _ => f a) = p.bind f :=
  by 
    ext b 
    simp only [p.bind_on_support_apply fun a _ => f a, p.bind_apply f, dite_eq_ite, Nnreal.coe_eq, mul_ite, mul_zero]
    refine' congr_argₓ _ (funext fun a => _)
    splitIfs with h <;> simp [h]

theorem coe_bind_on_support_apply (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β) (b : β) :
  (p.bind_on_support f b : ℝ≥0∞) = ∑'a, p a*if h : p a = 0 then 0 else f a h b :=
  by 
    simp only [bind_on_support_apply, Ennreal.coe_tsum (bind_on_support.summable p f b), dite_cast, Ennreal.coe_mul,
      Ennreal.coe_zero]

@[simp]
theorem mem_support_bind_on_support_iff (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β) (b : β) :
  b ∈ (p.bind_on_support f).Support ↔ ∃ (a : _)(ha : p a ≠ 0), b ∈ (f a ha).Support :=
  by 
    simp only [mem_support_iff, bind_on_support_apply, tsum_ne_zero_iff (bind_on_support.summable p f b),
      mul_ne_zero_iff]
    split  <;>
      ·
        rintro ⟨a, ha, haf⟩
        refine' ⟨a, ha, ne_of_eq_of_ne _ haf⟩
        simp [ha]

theorem bind_on_support_eq_zero_iff (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β) (b : β) :
  p.bind_on_support f b = 0 ↔ ∀ a ha : p a ≠ 0, f a ha b = 0 :=
  by 
    simp only [bind_on_support_apply, tsum_eq_zero_iff (bind_on_support.summable p f b), mul_eq_zero,
      or_iff_not_imp_left]
    exact ⟨fun h a ha => trans (dif_neg ha).symm (h a ha), fun h a ha => trans (dif_neg ha) (h a ha)⟩

@[simp]
theorem pure_bind_on_support (a : α) (f : ∀ a' : α ha : a' ∈ (pure a).Support, Pmf β) :
  (pure a).bindOnSupport f = f a ((mem_support_pure_iff a a).mpr rfl) :=
  by 
    refine' Pmf.ext fun b => _ 
    simp only [Nnreal.coe_eq, bind_on_support_apply, pure_apply]
    refine' trans (tsum_congr fun a' => _) (tsum_ite_eq a _)
    byCases' h : a' = a <;> simp [h]

theorem bind_on_support_pure (p : Pmf α) : (p.bind_on_support fun a _ => pure a) = p :=
  by 
    simp only [Pmf.bind_pure, Pmf.bind_on_support_eq_bind]

@[simp]
theorem bind_on_support_bind_on_support (p : Pmf α) (f : ∀ a _ : a ∈ p.support, Pmf β)
  (g : ∀ b _ : b ∈ (p.bind_on_support f).Support, Pmf γ) :
  (p.bind_on_support f).bindOnSupport g =
    p.bind_on_support
      fun a ha => (f a ha).bindOnSupport fun b hb => g b ((p.mem_support_bind_on_support_iff f b).mpr ⟨a, ha, hb⟩) :=
  by 
    refine' Pmf.ext fun a => _ 
    simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ←tsum_dite_right, ennreal.tsum_mul_left.symm,
      ennreal.tsum_mul_right.symm]
    refine' trans Ennreal.tsum_comm (tsum_congr fun a' => _)
    splitIfs with h
    ·
      simp only [h, Ennreal.coe_zero, zero_mul, tsum_zero]
    ·
      simp only [←Ennreal.tsum_mul_left, ←mul_assocₓ]
      refine' tsum_congr fun b => _ 
      splitIfs with h1 h2 h2 
      any_goals 
        ring1
      ·
        rw [bind_on_support_eq_zero_iff] at h1 
        simp only [h1 a' h, Ennreal.coe_zero, zero_mul, mul_zero]
      ·
        simp only [h2, Ennreal.coe_zero, mul_zero, zero_mul]

theorem bind_on_support_comm (p : Pmf α) (q : Pmf β) (f : ∀ a _ : a ∈ p.support b _ : b ∈ q.support, Pmf γ) :
  (p.bind_on_support fun a ha => q.bind_on_support (f a ha)) =
    q.bind_on_support fun b hb => p.bind_on_support fun a ha => f a ha b hb :=
  by 
    apply Pmf.ext 
    rintro c 
    simp only [ennreal.coe_eq_coe.symm, coe_bind_on_support_apply, ←tsum_dite_right, ennreal.tsum_mul_left.symm,
      ennreal.tsum_mul_right.symm]
    refine' trans Ennreal.tsum_comm (tsum_congr fun b => tsum_congr fun a => _)
    splitIfs with h1 h2 h2 <;> ring

end BindOnSupport

end Pmf

