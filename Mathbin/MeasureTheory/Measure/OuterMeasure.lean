import Mathbin.Analysis.SpecificLimits 
import Mathbin.MeasureTheory.PiSystem 
import Mathbin.Data.Fin.VecNotation 
import Mathbin.Topology.Algebra.InfiniteSum

/-!
# Outer Measures

An outer measure is a function `μ : set α → ℝ≥0∞`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

The outer measures on a type `α` form a complete lattice.

Given an arbitrary function `m : set α → ℝ≥0∞` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.
We also define this for functions `m` defined on a subset of `set α`, by treating the function as
having value `∞` outside its domain.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `outer_measure.bounded_by` is the greatest outer measure that is at most the given function.
  If you know that the given functions sends `∅` to `0`, then `outer_measure.of_function` is a
  special case.
* `caratheodory` is the Carathéodory-measurable space of an outer measure.
* `Inf_eq_of_function_Inf_gen` is a characterization of the infimum of outer measures.
* `induced_outer_measure` is the measure induced by a function on a subset of `set α`

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion
-/


noncomputable theory

open Set Finset Function Filter Encodable

open_locale Classical BigOperators Nnreal TopologicalSpace Ennreal

namespace MeasureTheory

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure outer_measure(α : Type _) where 
  measureOf : Set α → ℝ≥0∞
  Empty : measure_of ∅ = 0
  mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂ 
  Union_nat : ∀ s : ℕ → Set α, measure_of (⋃i, s i) ≤ ∑'i, measure_of (s i)

namespace OuterMeasure

section Basic

variable{α : Type _}{β : Type _}{ms : Set (outer_measure α)}{m : outer_measure α}

instance  : CoeFun (outer_measure α) fun _ => Set α → ℝ≥0∞ :=
  ⟨fun m => m.measure_of⟩

@[simp]
theorem measure_of_eq_coe (m : outer_measure α) : m.measure_of = m :=
  rfl

@[simp]
theorem empty' (m : outer_measure α) : m ∅ = 0 :=
  m.empty

theorem mono' (m : outer_measure α) {s₁ s₂} (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ :=
  m.mono h

protected theorem Union (m : outer_measure α) {β} [Encodable β] (s : β → Set α) : m (⋃i, s i) ≤ ∑'i, m (s i) :=
  rel_supr_tsum m m.empty (· ≤ ·) m.Union_nat s

theorem Union_null (m : outer_measure α) {β} [Encodable β] {s : β → Set α} (h : ∀ i, m (s i) = 0) : m (⋃i, s i) = 0 :=
  by 
    simpa [h] using m.Union s

protected theorem Union_finset (m : outer_measure α) (s : β → Set α) (t : Finset β) :
  m (⋃(i : _)(_ : i ∈ t), s i) ≤ ∑i in t, m (s i) :=
  rel_supr_sum m m.empty (· ≤ ·) m.Union_nat s t

protected theorem union (m : outer_measure α) (s₁ s₂ : Set α) : m (s₁ ∪ s₂) ≤ m s₁+m s₂ :=
  rel_sup_add m m.empty (· ≤ ·) m.Union_nat s₁ s₂

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `s : ι → set α` is a sequence of sets, `S = ⋃ n, s n`, and `m (S \ s n)` tends to zero along
some nontrivial filter (usually `at_top` on `α = ℕ`), then `m S = ⨆ n, m (s n)`. -/
theorem Union_of_tendsto_zero
{ι}
(m : outer_measure α)
{s : ι → set α}
(l : filter ι)
[ne_bot l]
(h0 : tendsto (λ
  k, m «expr \ »(«expr⋃ , »((n), s n), s k)) l (expr𝓝() 0)) : «expr = »(m «expr⋃ , »((n), s n), «expr⨆ , »((n), m (s n))) :=
begin
  set [] [ident S] [] [":="] [expr «expr⋃ , »((n), s n)] [],
  set [] [ident M] [] [":="] [expr «expr⨆ , »((n), m (s n))] [],
  have [ident hsS] [":", expr ∀ {k}, «expr ⊆ »(s k, S)] [],
  from [expr λ k, subset_Union _ _],
  refine [expr le_antisymm _ «expr $ »(supr_le, λ n, m.mono hsS)],
  have [ident A] [":", expr ∀ k, «expr ≤ »(m S, «expr + »(M, m «expr \ »(S, s k)))] [],
  from [expr λ k, calc
     «expr = »(m S, m «expr ∪ »(s k, «expr \ »(S, s k))) : by rw ["[", expr union_diff_self, ",", expr union_eq_self_of_subset_left hsS, "]"] []
     «expr ≤ »(..., «expr + »(m (s k), m «expr \ »(S, s k))) : m.union _ _
     «expr ≤ »(..., «expr + »(M, m «expr \ »(S, s k))) : add_le_add_right (le_supr _ k) _],
  have [ident B] [":", expr tendsto (λ k, «expr + »(M, m «expr \ »(S, s k))) l (expr𝓝() «expr + »(M, 0))] [],
  from [expr tendsto_const_nhds.add h0],
  rw [expr add_zero] ["at", ident B],
  exact [expr ge_of_tendsto' B A]
end

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `s : ℕ → set α` is a monotone sequence of sets such that `∑' k, m (s (k + 1) \ s k) ≠ ∞`,
then `m (⋃ n, s n) = ⨆ n, m (s n)`. -/
theorem Union_nat_of_monotone_of_tsum_ne_top
(m : outer_measure α)
{s : exprℕ() → set α}
(h_mono : ∀ n, «expr ⊆ »(s n, s «expr + »(n, 1)))
(h0 : «expr ≠ »(«expr∑' , »((k), m «expr \ »(s «expr + »(k, 1), s k)), «expr∞»())) : «expr = »(m «expr⋃ , »((n), s n), «expr⨆ , »((n), m (s n))) :=
begin
  refine [expr m.Union_of_tendsto_zero at_top _],
  refine [expr tendsto_nhds_bot_mono' (ennreal.tendsto_sum_nat_add _ h0) (λ n, _)],
  refine [expr (m.mono _).trans (m.Union _)],
  have [ident h'] [":", expr monotone s] [":=", expr @monotone_nat_of_le_succ (set α) _ _ h_mono],
  simp [] [] ["only"] ["[", expr diff_subset_iff, ",", expr Union_subset_iff, "]"] [] [],
  intros [ident i, ident x, ident hx],
  rcases [expr nat.find_x ⟨i, hx⟩, "with", "⟨", ident j, ",", ident hj, ",", ident hlt, "⟩"],
  clear [ident hx, ident i],
  cases [expr le_or_lt j n] ["with", ident hjn, ident hnj],
  { exact [expr or.inl (h' hjn hj)] },
  have [] [":", expr «expr = »(«expr + »(«expr + »(«expr - »(j, «expr + »(n, 1)), n), 1), j)] [],
  by rw ["[", expr add_assoc, ",", expr tsub_add_cancel_of_le hnj.nat_succ_le, "]"] [],
  refine [expr or.inr (mem_Union.2 ⟨«expr - »(j, «expr + »(n, 1)), _, hlt _ _⟩)],
  { rwa [expr this] [] },
  { rw ["[", "<-", expr nat.succ_le_iff, ",", expr nat.succ_eq_add_one, ",", expr this, "]"] [] }
end

theorem le_inter_add_diff {m : outer_measure α} {t : Set α} (s : Set α) : m t ≤ m (t ∩ s)+m (t \ s) :=
  by 
    convert m.union _ _ 
    rw [inter_union_diff t s]

theorem diff_null (m : outer_measure α) (s : Set α) {t : Set α} (ht : m t = 0) : m (s \ t) = m s :=
  by 
    refine' le_antisymmₓ (m.mono$ diff_subset _ _) _ 
    calc m s ≤ m (s ∩ t)+m (s \ t) := le_inter_add_diff _ _ ≤ m t+m (s \ t) :=
      add_le_add_right (m.mono$ inter_subset_right _ _) _ _ = m (s \ t) :=
      by 
        rw [ht, zero_addₓ]

theorem union_null (m : outer_measure α) {s₁ s₂ : Set α} (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) : m (s₁ ∪ s₂) = 0 :=
  by 
    simpa [h₁, h₂] using m.union s₁ s₂

theorem coe_fn_injective : injective fun μ : outer_measure α s : Set α => μ s :=
  fun μ₁ μ₂ h =>
    by 
      cases μ₁ 
      cases μ₂ 
      congr 
      exact h

@[ext]
theorem ext {μ₁ μ₂ : outer_measure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  coe_fn_injective$ funext h

/-- A version of `measure_theory.outer_measure.ext` that assumes `μ₁ s = μ₂ s` on all *nonempty*
sets `s`, and gets `μ₁ ∅ = μ₂ ∅` from `measure_theory.outer_measure.empty'`. -/
theorem ext_nonempty {μ₁ μ₂ : outer_measure α} (h : ∀ s : Set α, s.nonempty → μ₁ s = μ₂ s) : μ₁ = μ₂ :=
  ext$
    fun s =>
      s.eq_empty_or_nonempty.elim
        (fun he =>
          by 
            rw [he, empty', empty'])
        (h s)

instance  : HasZero (outer_measure α) :=
  ⟨{ measureOf := fun _ => 0, Empty := rfl, mono := fun _ _ _ => le_reflₓ 0, Union_nat := fun s => zero_le _ }⟩

@[simp]
theorem coe_zero : «expr⇑ » (0 : outer_measure α) = 0 :=
  rfl

instance  : Inhabited (outer_measure α) :=
  ⟨0⟩

instance  : Add (outer_measure α) :=
  ⟨fun m₁ m₂ =>
      { measureOf := fun s => m₁ s+m₂ s,
        Empty :=
          show (m₁ ∅+m₂ ∅) = 0 by 
            simp [outer_measure.empty],
        mono := fun s₁ s₂ h => add_le_add (m₁.mono h) (m₂.mono h),
        Union_nat :=
          fun s =>
            calc (m₁ (⋃i, s i)+m₂ (⋃i, s i)) ≤ (∑'i, m₁ (s i))+∑'i, m₂ (s i) :=
              add_le_add (m₁.Union_nat s) (m₂.Union_nat s)
              _ = _ := Ennreal.tsum_add.symm
               }⟩

@[simp]
theorem coe_add (m₁ m₂ : outer_measure α) : «expr⇑ » (m₁+m₂) = m₁+m₂ :=
  rfl

theorem add_apply (m₁ m₂ : outer_measure α) (s : Set α) : (m₁+m₂) s = m₁ s+m₂ s :=
  rfl

instance AddCommMonoidₓ : AddCommMonoidₓ (outer_measure α) :=
  { injective.add_comm_monoid (show outer_measure α → Set α → ℝ≥0∞ from coeFn) coe_fn_injective rfl fun _ _ => rfl with
    zero := 0, add := ·+· }

instance  : HasScalar ℝ≥0∞ (outer_measure α) :=
  ⟨fun c m =>
      { measureOf := fun s => c*m s,
        Empty :=
          by 
            simp ,
        mono := fun s t h => Ennreal.mul_left_mono$ m.mono h,
        Union_nat :=
          fun s =>
            by 
              rw [Ennreal.tsum_mul_left]
              exact Ennreal.mul_left_mono (m.Union _) }⟩

@[simp]
theorem coe_smul (c : ℝ≥0∞) (m : outer_measure α) : «expr⇑ » (c • m) = c • m :=
  rfl

theorem smul_apply (c : ℝ≥0∞) (m : outer_measure α) (s : Set α) : (c • m) s = c*m s :=
  rfl

instance  : Module ℝ≥0∞ (outer_measure α) :=
  { injective.module ℝ≥0∞ ⟨show outer_measure α → Set α → ℝ≥0∞ from coeFn, coe_zero, coe_add⟩ coe_fn_injective
      coe_smul with
    smul := · • · }

instance  : HasBot (outer_measure α) :=
  ⟨0⟩

@[simp]
theorem coe_bot : (⊥ : outer_measure α) = 0 :=
  rfl

instance outer_measure.partial_order : PartialOrderₓ (outer_measure α) :=
  { le := fun m₁ m₂ => ∀ s, m₁ s ≤ m₂ s, le_refl := fun a s => le_reflₓ _,
    le_trans := fun a b c hab hbc s => le_transₓ (hab s) (hbc s),
    le_antisymm := fun a b hab hba => ext$ fun s => le_antisymmₓ (hab s) (hba s) }

instance outer_measure.order_bot : OrderBot (outer_measure α) :=
  { outer_measure.has_bot with
    bot_le :=
      fun a s =>
        by 
          simp only [coe_zero, Pi.zero_apply, coe_bot, zero_le] }

section Supremum

instance  : HasSupₓ (outer_measure α) :=
  ⟨fun ms =>
      { measureOf := fun s => ⨆(m : _)(_ : m ∈ ms), (m : outer_measure α) s,
        Empty := nonpos_iff_eq_zero.1$ bsupr_le$ fun m h => le_of_eqₓ m.empty,
        mono := fun s₁ s₂ hs => bsupr_le_bsupr$ fun m hm => m.mono hs,
        Union_nat :=
          fun f =>
            bsupr_le$
              fun m hm =>
                calc m (⋃i, f i) ≤ ∑'i : ℕ, m (f i) := m.Union_nat _ 
                  _ ≤ ∑'i, ⨆(m : _)(_ : m ∈ ms), (m : outer_measure α) (f i) :=
                  Ennreal.tsum_le_tsum$ fun i => le_bsupr m hm
                   }⟩

instance  : CompleteLattice (outer_measure α) :=
  { outer_measure.order_bot,
    completeLatticeOfSup (outer_measure α)
      fun ms => ⟨fun m hm s => le_bsupr m hm, fun m hm s => bsupr_le fun m' hm' => hm hm' s⟩ with
     }

@[simp]
theorem Sup_apply (ms : Set (outer_measure α)) (s : Set α) :
  (Sup ms) s = ⨆(m : _)(_ : m ∈ ms), (m : outer_measure α) s :=
  rfl

@[simp]
theorem supr_apply {ι} (f : ι → outer_measure α) (s : Set α) : (⨆i : ι, f i) s = ⨆i, f i s :=
  by 
    rw [supr, Sup_apply, supr_range, supr]

@[normCast]
theorem coe_supr {ι} (f : ι → outer_measure α) : «expr⇑ » (⨆i, f i) = ⨆i, f i :=
  funext$
    fun s =>
      by 
        rw [supr_apply, _root_.supr_apply]

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem sup_apply (m₁ m₂ : outer_measure α) (s : set α) : «expr = »(«expr ⊔ »(m₁, m₂) s, «expr ⊔ »(m₁ s, m₂ s)) :=
by have [] [] [":=", expr supr_apply (λ
  b, cond b m₁ m₂) s]; rwa ["[", expr supr_bool_eq, ",", expr supr_bool_eq, "]"] ["at", ident this]

theorem smul_supr {ι} (f : ι → outer_measure α) (c : ℝ≥0∞) : (c • ⨆i, f i) = ⨆i, c • f i :=
  ext$
    fun s =>
      by 
        simp only [smul_apply, supr_apply, Ennreal.mul_supr]

end Supremum

@[mono]
theorem mono'' {m₁ m₂ : outer_measure α} {s₁ s₂ : Set α} (hm : m₁ ≤ m₂) (hs : s₁ ⊆ s₂) : m₁ s₁ ≤ m₂ s₂ :=
  (hm s₁).trans (m₂.mono hs)

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {β} (f : α → β) : outer_measure α →ₗ[ℝ≥0∞] outer_measure β :=
  { toFun :=
      fun m =>
        { measureOf := fun s => m (f ⁻¹' s), Empty := m.empty, mono := fun s t h => m.mono (preimage_mono h),
          Union_nat :=
            fun s =>
              by 
                rw [preimage_Union] <;> exact m.Union_nat fun i => f ⁻¹' s i },
    map_add' := fun m₁ m₂ => coe_fn_injective rfl, map_smul' := fun c m => coe_fn_injective rfl }

@[simp]
theorem map_apply {β} (f : α → β) (m : outer_measure α) (s : Set β) : map f m s = m (f ⁻¹' s) :=
  rfl

@[simp]
theorem map_id (m : outer_measure α) : map id m = m :=
  ext$ fun s => rfl

@[simp]
theorem map_map {β γ} (f : α → β) (g : β → γ) (m : outer_measure α) : map g (map f m) = map (g ∘ f) m :=
  ext$ fun s => rfl

@[mono]
theorem map_mono {β} (f : α → β) : Monotone (map f) :=
  fun m m' h s => h _

@[simp]
theorem map_sup {β} (f : α → β) (m m' : outer_measure α) : map f (m⊔m') = map f m⊔map f m' :=
  ext$
    fun s =>
      by 
        simp only [map_apply, sup_apply]

@[simp]
theorem map_supr {β ι} (f : α → β) (m : ι → outer_measure α) : map f (⨆i, m i) = ⨆i, map f (m i) :=
  ext$
    fun s =>
      by 
        simp only [map_apply, supr_apply]

instance  : Functor outer_measure :=
  { map := fun α β f => map f }

instance  : IsLawfulFunctor outer_measure :=
  { id_map := fun α => map_id, comp_map := fun α β γ f g m => (map_map f g m).symm }

/-- The dirac outer measure. -/
def dirac (a : α) : outer_measure α :=
  { measureOf := fun s => indicator s (fun _ => 1) a,
    Empty :=
      by 
        simp ,
    mono := fun s t h => indicator_le_indicator_of_subset h (fun _ => zero_le _) a,
    Union_nat :=
      fun s =>
        if hs : a ∈ ⋃n, s n then
          let ⟨i, hi⟩ := mem_Union.1 hs 
          calc indicator (⋃n, s n) (fun _ => (1 : ℝ≥0∞)) a = 1 := indicator_of_mem hs _ 
            _ = indicator (s i) (fun _ => 1) a := (indicator_of_mem hi _).symm 
            _ ≤ ∑'n, indicator (s n) (fun _ => 1) a := Ennreal.le_tsum _
            
        else
          by 
            simp only [indicator_of_not_mem hs, zero_le] }

@[simp]
theorem dirac_apply (a : α) (s : Set α) : dirac a s = indicator s (fun _ => 1) a :=
  rfl

/-- The sum of an (arbitrary) collection of outer measures. -/
def Sum {ι} (f : ι → outer_measure α) : outer_measure α :=
  { measureOf := fun s => ∑'i, f i s,
    Empty :=
      by 
        simp ,
    mono := fun s t h => Ennreal.tsum_le_tsum fun i => (f i).mono' h,
    Union_nat :=
      fun s =>
        by 
          rw [Ennreal.tsum_comm] <;> exact Ennreal.tsum_le_tsum fun i => (f i).Union_nat _ }

@[simp]
theorem sum_apply {ι} (f : ι → outer_measure α) (s : Set α) : Sum f s = ∑'i, f i s :=
  rfl

theorem smul_dirac_apply (a : ℝ≥0∞) (b : α) (s : Set α) : (a • dirac b) s = indicator s (fun _ => a) b :=
  by 
    simp only [smul_apply, dirac_apply, ←indicator_mul_right _ fun _ => a, mul_oneₓ]

/-- Pullback of an `outer_measure`: `comap f μ s = μ (f '' s)`. -/
def comap {β} (f : α → β) : outer_measure β →ₗ[ℝ≥0∞] outer_measure α :=
  { toFun :=
      fun m =>
        { measureOf := fun s => m (f '' s),
          Empty :=
            by 
              simp ,
          mono := fun s t h => m.mono$ image_subset f h,
          Union_nat :=
            fun s =>
              by 
                rw [image_Union]
                apply m.Union_nat },
    map_add' := fun m₁ m₂ => rfl, map_smul' := fun c m => rfl }

@[simp]
theorem comap_apply {β} (f : α → β) (m : outer_measure β) (s : Set α) : comap f m s = m (f '' s) :=
  rfl

@[mono]
theorem comap_mono {β} (f : α → β) : Monotone (comap f) :=
  fun m m' h s => h _

@[simp]
theorem comap_supr {β ι} (f : α → β) (m : ι → outer_measure β) : comap f (⨆i, m i) = ⨆i, comap f (m i) :=
  ext$
    fun s =>
      by 
        simp only [comap_apply, supr_apply]

/-- Restrict an `outer_measure` to a set. -/
def restrict (s : Set α) : outer_measure α →ₗ[ℝ≥0∞] outer_measure α :=
  (map coeₓ).comp (comap (coeₓ : s → α))

@[simp]
theorem restrict_apply (s t : Set α) (m : outer_measure α) : restrict s m t = m (t ∩ s) :=
  by 
    simp [restrict]

@[mono]
theorem restrict_mono {s t : Set α} (h : s ⊆ t) {m m' : outer_measure α} (hm : m ≤ m') : restrict s m ≤ restrict t m' :=
  fun u =>
    by 
      simp only [restrict_apply]
      exact (hm _).trans (m'.mono$ inter_subset_inter_right _ h)

@[simp]
theorem restrict_univ (m : outer_measure α) : restrict univ m = m :=
  ext$
    fun s =>
      by 
        simp 

@[simp]
theorem restrict_empty (m : outer_measure α) : restrict ∅ m = 0 :=
  ext$
    fun s =>
      by 
        simp 

@[simp]
theorem restrict_supr {ι} (s : Set α) (m : ι → outer_measure α) : restrict s (⨆i, m i) = ⨆i, restrict s (m i) :=
  by 
    simp [restrict]

theorem map_comap {β} (f : α → β) (m : outer_measure β) : map f (comap f m) = restrict (range f) m :=
  ext$
    fun s =>
      congr_argₓ m$
        by 
          simp only [image_preimage_eq_inter_range, Subtype.range_coe]

theorem map_comap_le {β} (f : α → β) (m : outer_measure β) : map f (comap f m) ≤ m :=
  fun s => m.mono$ image_preimage_subset _ _

theorem restrict_le_self (m : outer_measure α) (s : Set α) : restrict s m ≤ m :=
  map_comap_le _ _

@[simp]
theorem map_le_restrict_range {β} {ma : outer_measure α} {mb : outer_measure β} {f : α → β} :
  map f ma ≤ restrict (range f) mb ↔ map f ma ≤ mb :=
  ⟨fun h => h.trans (restrict_le_self _ _),
    fun h s =>
      by 
        simpa using h (s ∩ range f)⟩

theorem map_comap_of_surjective {β} {f : α → β} (hf : surjective f) (m : outer_measure β) : map f (comap f m) = m :=
  ext$
    fun s =>
      by 
        rw [map_apply, comap_apply, hf.image_preimage]

theorem le_comap_map {β} (f : α → β) (m : outer_measure α) : m ≤ comap f (map f m) :=
  fun s => m.mono$ subset_preimage_image _ _

theorem comap_map {β} {f : α → β} (hf : injective f) (m : outer_measure α) : comap f (map f m) = m :=
  ext$
    fun s =>
      by 
        rw [comap_apply, map_apply, hf.preimage_image]

@[simp]
theorem top_apply {s : Set α} (h : s.nonempty) : (⊤ : outer_measure α) s = ∞ :=
  let ⟨a, as⟩ := h 
  top_unique$
    le_transₓ
      (by 
        simp [smul_dirac_apply, as])
      (le_bsupr (∞ • dirac a) trivialₓ)

theorem top_apply' (s : Set α) : (⊤ : outer_measure α) s = ⨅h : s = ∅, 0 :=
  s.eq_empty_or_nonempty.elim
    (fun h =>
      by 
        simp [h])
    fun h =>
      by 
        simp [h, h.ne_empty]

@[simp]
theorem comap_top (f : α → β) : comap f ⊤ = ⊤ :=
  ext_nonempty$
    fun s hs =>
      by 
        rw [comap_apply, top_apply hs, top_apply (hs.image _)]

theorem map_top (f : α → β) : map f ⊤ = restrict (range f) ⊤ :=
  ext$
    fun s =>
      by 
        rw [map_apply, restrict_apply, ←image_preimage_eq_inter_range, top_apply', top_apply', Set.image_eq_empty]

theorem map_top_of_surjective (f : α → β) (hf : surjective f) : map f ⊤ = ⊤ :=
  by 
    rw [map_top, hf.range_eq, restrict_univ]

end Basic

section OfFunction

set_option eqn_compiler.zeta true

variable{α : Type _}(m : Set α → ℝ≥0∞)(m_empty : m ∅ = 0)

include m_empty

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected
def of_function : outer_measure α :=
let μ := λ s, «expr⨅ , »({f : exprℕ() → set α} (h : «expr ⊆ »(s, «expr⋃ , »((i), f i))), «expr∑' , »((i), m (f i))) in
{ measure_of := μ,
  empty := le_antisymm «expr $ »(infi_le_of_le (λ
    _, «expr∅»()), «expr $ »(infi_le_of_le (empty_subset _), by simp [] [] [] ["[", expr m_empty, "]"] [] [])) (zero_le _),
  mono := assume
  s₁ s₂ hs, «expr $ »(infi_le_infi, assume f, «expr $ »(infi_le_infi2, assume hb, ⟨subset.trans hs hb, le_refl _⟩)),
  Union_nat := assume
  s, «expr $ »(ennreal.le_of_forall_pos_le_add, begin
     assume [binders (ε hε) (hb : «expr < »(«expr∑' , »((i), μ (s i)), «expr∞»()))],
     rcases [expr ennreal.exists_pos_sum_of_encodable (ennreal.coe_pos.2 hε).ne' exprℕ(), "with", "⟨", ident ε', ",", ident hε', ",", ident hl, "⟩"],
     refine [expr le_trans _ (add_le_add_left (le_of_lt hl) _)],
     rw ["<-", expr ennreal.tsum_add] [],
     choose [] [ident f] [ident hf] ["using", expr show ∀
      i, «expr∃ , »((f : exprℕ() → set α), «expr ∧ »(«expr ⊆ »(s i, «expr⋃ , »((i), f i)), «expr < »(«expr∑' , »((i), m (f i)), «expr + »(μ (s i), ε' i)))), { intro [],
        have [] [":", expr «expr < »(μ (s i), «expr + »(μ (s i), ε' i))] [":=", expr ennreal.lt_add_right «expr $ »(ne_top_of_le_ne_top hb.ne, ennreal.le_tsum _) (by simpa [] [] [] [] [] ["using", expr (hε' i).ne'])],
        simpa [] [] [] ["[", expr μ, ",", expr infi_lt_iff, "]"] [] [] }],
     refine [expr le_trans _ «expr $ »(ennreal.tsum_le_tsum, λ i, le_of_lt (hf i).2)],
     rw ["[", "<-", expr ennreal.tsum_prod, ",", "<-", expr equiv.nat_prod_nat_equiv_nat.symm.tsum_eq, "]"] [],
     swap,
     { apply_instance },
     refine [expr infi_le_of_le _ (infi_le _ _)],
     exact [expr Union_subset (λ
       i, «expr $ »(subset.trans (hf i).1, «expr $ »(Union_subset, λ
         j, «expr $ »(subset.trans (by simp [] [] [] [] [] []), «expr $ »(subset_Union _, equiv.nat_prod_nat_equiv_nat (i, j))))))]
   end) }

theorem of_function_apply (s : Set α) :
  outer_measure.of_function m m_empty s = ⨅(t : ℕ → Set α)(h : s ⊆ Union t), ∑'n, m (t n) :=
  rfl

variable{m m_empty}

theorem of_function_le (s : Set α) : outer_measure.of_function m m_empty s ≤ m s :=
  let f : ℕ → Set α := fun i => Nat.casesOn i s fun _ => ∅
  infi_le_of_le f$
    infi_le_of_le (subset_Union f 0)$
      le_of_eqₓ$
        tsum_eq_single 0$
          by 
            rintro (_ | i) <;> simp [f, m_empty]

theorem of_function_eq (s : Set α) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ s : ℕ → Set α, m (⋃i, s i) ≤ ∑'i, m (s i)) : outer_measure.of_function m m_empty s = m s :=
  le_antisymmₓ (of_function_le s)$ le_infi$ fun f => le_infi$ fun hf => le_transₓ (m_mono hf) (m_subadd f)

theorem le_of_function {μ : outer_measure α} : μ ≤ outer_measure.of_function m m_empty ↔ ∀ s, μ s ≤ m s :=
  ⟨fun H s => le_transₓ (H s) (of_function_le s),
    fun H s =>
      le_infi$
        fun f => le_infi$ fun hs => le_transₓ (μ.mono hs)$ le_transₓ (μ.Union f)$ Ennreal.tsum_le_tsum$ fun i => H _⟩

theorem is_greatest_of_function :
  IsGreatest { μ:outer_measure α | ∀ s, μ s ≤ m s } (outer_measure.of_function m m_empty) :=
  ⟨fun s => of_function_le _, fun μ => le_of_function.2⟩

theorem of_function_eq_Sup : outer_measure.of_function m m_empty = Sup { μ | ∀ s, μ s ≤ m s } :=
  (@is_greatest_of_function α m m_empty).IsLub.Sup_eq.symm

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.of_function m m_empty`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem of_function_union_of_top_of_nonempty_inter
{s t : set α}
(h : ∀
 u, «expr ∩ »(s, u).nonempty → «expr ∩ »(t, u).nonempty → «expr = »(m u, «expr∞»())) : «expr = »(outer_measure.of_function m m_empty «expr ∪ »(s, t), «expr + »(outer_measure.of_function m m_empty s, outer_measure.of_function m m_empty t)) :=
begin
  refine [expr le_antisymm (outer_measure.union _ _ _) «expr $ »(le_infi, λ f, «expr $ »(le_infi, λ hf, _))],
  set [] [ident μ] [] [":="] [expr outer_measure.of_function m m_empty] [],
  rcases [expr em «expr∃ , »((i), «expr ∧ »(«expr ∩ »(s, f i).nonempty, «expr ∩ »(t, f i).nonempty)), "with", "⟨", ident i, ",", ident hs, ",", ident ht, "⟩", "|", ident he],
  { calc
      «expr ≤ »(«expr + »(μ s, μ t), «expr∞»()) : le_top
      «expr = »(..., m (f i)) : (h (f i) hs ht).symm
      «expr ≤ »(..., «expr∑' , »((i), m (f i))) : ennreal.le_tsum i },
  set [] [ident I] [] [":="] [expr λ s, {i : exprℕ() | «expr ∩ »(s, f i).nonempty}] [],
  have [ident hd] [":", expr disjoint (I s) (I t)] [],
  from [expr λ i hi, he ⟨i, hi⟩],
  have [ident hI] [":", expr ∀ u «expr ⊆ » «expr ∪ »(s, t), «expr ≤ »(μ u, «expr∑' , »((i : I u), μ (f i)))] [],
  from [expr λ u hu, calc
     «expr ≤ »(μ u, μ «expr⋃ , »((i : I u), f i)) : μ.mono (λ x hx, let ⟨i, hi⟩ := mem_Union.1 (hf (hu hx)) in
      mem_Union.2 ⟨⟨i, ⟨x, hx, hi⟩⟩, hi⟩)
     «expr ≤ »(..., «expr∑' , »((i : I u), μ (f i))) : μ.Union _],
  calc
    «expr ≤ »(«expr + »(μ s, μ t), «expr + »(«expr∑' , »((i : I s), μ (f i)), «expr∑' , »((i : I t), μ (f i)))) : add_le_add «expr $ »(hI _, subset_union_left _ _) «expr $ »(hI _, subset_union_right _ _)
    «expr = »(..., «expr∑' , »((i : «expr ∪ »(I s, I t)), μ (f i))) : (@tsum_union_disjoint _ _ _ _ _ (λ
      i, μ (f i)) _ _ _ hd ennreal.summable ennreal.summable).symm
    «expr ≤ »(..., «expr∑' , »((i), μ (f i))) : tsum_le_tsum_of_inj coe subtype.coe_injective (λ
     _ _, zero_le _) (λ _, le_rfl) ennreal.summable ennreal.summable
    «expr ≤ »(..., «expr∑' , »((i), m (f i))) : ennreal.tsum_le_tsum (λ i, of_function_le _)
end

theorem comap_of_function {β} (f : β → α) (h : Monotone m ∨ surjective f) :
  comap f (outer_measure.of_function m m_empty) =
    outer_measure.of_function (fun s => m (f '' s))
      (by 
        rwa [Set.image_empty]) :=
  by 
    refine' le_antisymmₓ (le_of_function.2$ fun s => _) fun s => _
    ·
      rw [comap_apply]
      apply of_function_le
    ·
      rw [comap_apply, of_function_apply, of_function_apply]
      refine' infi_le_infi2 fun t => ⟨fun k => f ⁻¹' t k, _⟩
      refine' infi_le_infi2 fun ht => _ 
      rw [Set.image_subset_iff, preimage_Union] at ht 
      refine' ⟨ht, Ennreal.tsum_le_tsum$ fun n => _⟩
      cases h 
      exacts[h (image_preimage_subset _ _), (congr_argₓ m (h.image_preimage (t n))).le]

theorem map_of_function_le {β} (f : α → β) :
  map f (outer_measure.of_function m m_empty) ≤ outer_measure.of_function (fun s => m (f ⁻¹' s)) m_empty :=
  le_of_function.2$
    fun s =>
      by 
        rw [map_apply]
        apply of_function_le

theorem map_of_function {β} {f : α → β} (hf : injective f) :
  map f (outer_measure.of_function m m_empty) = outer_measure.of_function (fun s => m (f ⁻¹' s)) m_empty :=
  by 
    refine' (map_of_function_le _).antisymm fun s => _ 
    simp only [of_function_apply, map_apply, le_infi_iff]
    intro t ht 
    refine' infi_le_of_le (fun n => «expr ᶜ» (range f) ∪ f '' t n) (infi_le_of_le _ _)
    ·
      rw [←union_Union, ←inter_subset, ←image_preimage_eq_inter_range, ←image_Union]
      exact image_subset _ ht
    ·
      refine' Ennreal.tsum_le_tsum fun n => le_of_eqₓ _ 
      simp [hf.preimage_image]

theorem restrict_of_function (s : Set α) (hm : Monotone m) :
  restrict s (outer_measure.of_function m m_empty) =
    outer_measure.of_function (fun t => m (t ∩ s))
      (by 
        rwa [Set.empty_inter]) :=
  by 
    simp only [restrict, LinearMap.comp_apply, comap_of_function _ (Or.inl hm), map_of_function Subtype.coe_injective,
      Subtype.image_preimage_coe]

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem smul_of_function
{c : «exprℝ≥0∞»()}
(hc : «expr ≠ »(c, «expr∞»())) : «expr = »(«expr • »(c, outer_measure.of_function m m_empty), outer_measure.of_function «expr • »(c, m) (by simp [] [] [] ["[", expr m_empty, "]"] [] [])) :=
begin
  ext1 [] [ident s],
  haveI [] [":", expr nonempty {t : exprℕ() → set α // «expr ⊆ »(s, «expr⋃ , »((i), t i))}] [":=", expr ⟨⟨λ
     _, s, subset_Union (λ _, s) 0⟩⟩],
  simp [] [] ["only"] ["[", expr smul_apply, ",", expr of_function_apply, ",", expr ennreal.tsum_mul_left, ",", expr pi.smul_apply, ",", expr smul_eq_mul, ",", expr infi_subtype', ",", expr ennreal.infi_mul_left (λ
    h, (hc h).elim), "]"] [] []
end

end OfFunction

section BoundedBy

variable{α : Type _}(m : Set α → ℝ≥0∞)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by : outer_measure α :=
  outer_measure.of_function (fun s => ⨆h : s.nonempty, m s)
    (by 
      simp [empty_not_nonempty])

variable{m}

theorem bounded_by_le (s : Set α) : bounded_by m s ≤ m s :=
  (of_function_le _).trans supr_const_le

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem bounded_by_eq_of_function
(m_empty : «expr = »(m «expr∅»(), 0))
(s : set α) : «expr = »(bounded_by m s, outer_measure.of_function m m_empty s) :=
begin
  have [] [":", expr «expr = »(λ s : set α, «expr⨆ , »((h : s.nonempty), m s), m)] [],
  { ext1 [] [ident t],
    cases [expr t.eq_empty_or_nonempty] ["with", ident h, ident h]; simp [] [] [] ["[", expr h, ",", expr empty_not_nonempty, ",", expr m_empty, "]"] [] [] },
  simp [] [] [] ["[", expr bounded_by, ",", expr this, "]"] [] []
end

theorem bounded_by_apply (s : Set α) :
  bounded_by m s = ⨅(t : ℕ → Set α)(h : s ⊆ Union t), ∑'n, ⨆h : (t n).Nonempty, m (t n) :=
  by 
    simp [bounded_by, of_function_apply]

theorem bounded_by_eq (s : Set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : Set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ s : ℕ → Set α, m (⋃i, s i) ≤ ∑'i, m (s i)) : bounded_by m s = m s :=
  by 
    rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]

@[simp]
theorem bounded_by_eq_self (m : outer_measure α) : bounded_by m = m :=
  ext$ fun s => bounded_by_eq _ m.empty' (fun t ht => m.mono' ht) m.Union

theorem le_bounded_by {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s, μ s ≤ m s :=
  by 
    rw [bounded_by, le_of_function, forall_congrₓ]
    intro s 
    cases' s.eq_empty_or_nonempty with h h <;> simp [h, empty_not_nonempty]

theorem le_bounded_by' {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s : Set α, s.nonempty → μ s ≤ m s :=
  by 
    rw [le_bounded_by, forall_congrₓ]
    intro s 
    cases' s.eq_empty_or_nonempty with h h <;> simp [h]

theorem smul_bounded_by {c : ℝ≥0∞} (hc : c ≠ ∞) : c • bounded_by m = bounded_by (c • m) :=
  by 
    simp only [bounded_by, smul_of_function hc]
    congr 1 with s : 1
    rcases s.eq_empty_or_nonempty with (rfl | hs) <;> simp 

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem comap_bounded_by
{β}
(f : β → α)
(h : «expr ∨ »(monotone (λ
   s : {s : set α // s.nonempty}, m s), surjective f)) : «expr = »(comap f (bounded_by m), bounded_by (λ
  s, m «expr '' »(f, s))) :=
begin
  refine [expr (comap_of_function _ _).trans _],
  { refine [expr h.imp (λ H s t hst, «expr $ »(supr_le, λ hs, _)) id],
    have [ident ht] [":", expr t.nonempty] [":=", expr hs.mono hst],
    exact [expr (@H ⟨s, hs⟩ ⟨t, ht⟩ hst).trans (le_supr (λ h : t.nonempty, m t) ht)] },
  { dunfold [ident bounded_by] [],
    congr' [] ["with", ident s, ":", 1],
    rw [expr nonempty_image_iff] [] }
end

/-- If `m u = ∞` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = measure_theory.outer_measure.bounded_by m`.

E.g., if `α` is an (e)metric space and `m u = ∞` on any set of diameter `≥ r`, then this lemma
implies that `μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s`
and `y ∈ t`.  -/
theorem bounded_by_union_of_top_of_nonempty_inter {s t : Set α}
  (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → m u = ∞) : bounded_by m (s ∪ t) = bounded_by m s+bounded_by m t :=
  of_function_union_of_top_of_nonempty_inter$
    fun u hs ht => top_unique$ (h u hs ht).Ge.trans$ le_supr (fun h => m u) (hs.mono$ inter_subset_right s u)

end BoundedBy

section CaratheodoryMeasurable

universe u

parameter {α : Type u}(m : outer_measure α)

include m

attribute [local simp] Set.inter_comm Set.inter_left_comm Set.inter_assoc

variable{s s₁ s₂ : Set α}

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def is_caratheodory (s : Set α) : Prop :=
  ∀ t, m t = m (t ∩ s)+m (t \ s)

theorem is_caratheodory_iff_le' {s : Set α} : is_caratheodory s ↔ ∀ t, (m (t ∩ s)+m (t \ s)) ≤ m t :=
  forall_congrₓ$ fun t => le_antisymm_iffₓ.trans$ and_iff_right$ le_inter_add_diff _

@[simp]
theorem is_caratheodory_empty : is_caratheodory ∅ :=
  by 
    simp [is_caratheodory, m.empty, diff_empty]

theorem is_caratheodory_compl : is_caratheodory s₁ → is_caratheodory («expr ᶜ» s₁) :=
  by 
    simp [is_caratheodory, diff_eq, add_commₓ]

@[simp]
theorem is_caratheodory_compl_iff : is_caratheodory («expr ᶜ» s) ↔ is_caratheodory s :=
  ⟨fun h =>
      by 
        simpa using is_caratheodory_compl m h,
    is_caratheodory_compl⟩

theorem is_caratheodory_union (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) : is_caratheodory (s₁ ∪ s₂) :=
  fun t =>
    by 
      rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)), inter_diff_assoc _ _ s₁, Set.inter_assoc _ _ s₁,
        inter_eq_self_of_subset_right (Set.subset_union_left _ _), union_diff_left, h₂ (t ∩ s₁)]
      simp [diff_eq, add_assocₓ]

theorem measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : is_caratheodory s₁) {t : Set α} :
  m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁)+m (t ∩ s₂) :=
  by 
    rw [h₁, Set.inter_assoc, Set.union_inter_cancel_left, inter_diff_assoc, union_diff_cancel_left h]

theorem is_caratheodory_Union_lt {s : ℕ → Set α} :
  ∀ {n : ℕ}, (∀ i _ : i < n, is_caratheodory (s i)) → is_caratheodory (⋃(i : _)(_ : i < n), s i)
| 0, h =>
  by 
    simp [Nat.not_lt_zeroₓ]
| n+1, h =>
  by 
    rw [bUnion_lt_succ] <;>
      exact
        is_caratheodory_union m (is_caratheodory_Union_lt$ fun i hi => h i$ lt_of_lt_of_leₓ hi$ Nat.le_succₓ _)
          (h n (le_reflₓ (n+1)))

theorem is_caratheodory_inter (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) : is_caratheodory (s₁ ∩ s₂) :=
  by 
    rw [←is_caratheodory_compl_iff, compl_inter]
    exact is_caratheodory_union _ (is_caratheodory_compl _ h₁) (is_caratheodory_compl _ h₂)

theorem is_caratheodory_sum {s : ℕ → Set α} (h : ∀ i, is_caratheodory (s i)) (hd : Pairwise (Disjoint on s))
  {t : Set α} : ∀ {n}, (∑i in Finset.range n, m (t ∩ s i)) = m (t ∩ ⋃(i : _)(_ : i < n), s i)
| 0 =>
  by 
    simp [Nat.not_lt_zeroₓ, m.empty]
| Nat.succ n =>
  by 
    rw [bUnion_lt_succ, Finset.sum_range_succ, Set.union_comm, is_caratheodory_sum, m.measure_inter_union _ (h n),
      add_commₓ]
    intro a 
    simpa using fun h₁ : a ∈ s n i hi : i < n h₂ => hd _ _ (ne_of_gtₓ hi) ⟨h₁, h₂⟩

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem is_caratheodory_Union_nat
{s : exprℕ() → set α}
(h : ∀ i, is_caratheodory (s i))
(hd : pairwise «expr on »(disjoint, s)) : is_caratheodory «expr⋃ , »((i), s i) :=
«expr $ »(is_caratheodory_iff_le'.2, λ t, begin
   have [ident hp] [":", expr «expr ≤ »(m «expr ∩ »(t, «expr⋃ , »((i), s i)), «expr⨆ , »((n), m «expr ∩ »(t, «expr⋃ , »((i «expr < » n), s i))))] [],
   { convert [] [expr m.Union (λ i, «expr ∩ »(t, s i))] [],
     { rw [expr inter_Union] [] },
     { simp [] [] [] ["[", expr ennreal.tsum_eq_supr_nat, ",", expr is_caratheodory_sum m h hd, "]"] [] [] } },
   refine [expr le_trans (add_le_add_right hp _) _],
   rw [expr ennreal.supr_add] [],
   refine [expr supr_le (λ n, le_trans (add_le_add_left _ _) (ge_of_eq (is_caratheodory_Union_lt m (λ i _, h i) _)))],
   refine [expr m.mono (diff_subset_diff_right _)],
   exact [expr bUnion_subset (λ i _, subset_Union _ i)]
 end)

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem f_Union
{s : exprℕ() → set α}
(h : ∀ i, is_caratheodory (s i))
(hd : pairwise «expr on »(disjoint, s)) : «expr = »(m «expr⋃ , »((i), s i), «expr∑' , »((i), m (s i))) :=
begin
  refine [expr le_antisymm (m.Union_nat s) _],
  rw [expr ennreal.tsum_eq_supr_nat] [],
  refine [expr supr_le (λ n, _)],
  have [] [] [":=", expr @is_caratheodory_sum _ m _ h hd univ n],
  simp [] [] [] [] [] ["at", ident this],
  simp [] [] [] ["[", expr this, "]"] [] [],
  exact [expr m.mono (bUnion_subset (λ i _, subset_Union _ i))]
end

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.  -/
def caratheodory_dynkin : MeasurableSpace.DynkinSystem α :=
  { Has := is_caratheodory, has_empty := is_caratheodory_empty, HasCompl := fun s => is_caratheodory_compl,
    has_Union_nat := fun f hf hn => is_caratheodory_Union_nat hn hf }

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : MeasurableSpace α :=
  caratheodory_dynkin.to_measurable_space$ fun s₁ s₂ => is_caratheodory_inter

theorem is_caratheodory_iff {s : Set α} : caratheodory.measurable_set' s ↔ ∀ t, m t = m (t ∩ s)+m (t \ s) :=
  Iff.rfl

theorem is_caratheodory_iff_le {s : Set α} : caratheodory.measurable_set' s ↔ ∀ t, (m (t ∩ s)+m (t \ s)) ≤ m t :=
  is_caratheodory_iff_le'

protected theorem Union_eq_of_caratheodory {s : ℕ → Set α} (h : ∀ i, caratheodory.measurable_set' (s i))
  (hd : Pairwise (Disjoint on s)) : m (⋃i, s i) = ∑'i, m (s i) :=
  f_Union h hd

end CaratheodoryMeasurable

variable{α : Type _}

theorem of_function_caratheodory {m : Set α → ℝ≥0∞} {s : Set α} {h₀ : m ∅ = 0} (hs : ∀ t, (m (t ∩ s)+m (t \ s)) ≤ m t) :
  (outer_measure.of_function m h₀).caratheodory.MeasurableSet' s :=
  by 
    apply (is_caratheodory_iff_le _).mpr 
    refine' fun t => le_infi fun f => le_infi$ fun hf => _ 
    refine'
      le_transₓ
        (add_le_add ((infi_le_of_le fun i => f i ∩ s)$ infi_le _ _) ((infi_le_of_le fun i => f i \ s)$ infi_le _ _)) _
    ·
      rw [←Union_inter]
      exact inter_subset_inter_left _ hf
    ·
      rw [←Union_diff]
      exact diff_subset_diff_left hf
    ·
      rw [←Ennreal.tsum_add]
      exact Ennreal.tsum_le_tsum fun i => hs _

theorem bounded_by_caratheodory {m : Set α → ℝ≥0∞} {s : Set α} (hs : ∀ t, (m (t ∩ s)+m (t \ s)) ≤ m t) :
  (bounded_by m).caratheodory.MeasurableSet' s :=
  by 
    apply of_function_caratheodory 
    intro t 
    cases' t.eq_empty_or_nonempty with h h
    ·
      simp [h, empty_not_nonempty]
    ·
      convert le_transₓ _ (hs t)
      ·
        simp [h]
      exact add_le_add supr_const_le supr_const_le

@[simp]
theorem zero_caratheodory : (0 : outer_measure α).caratheodory = ⊤ :=
  top_unique$ fun s _ t => (add_zeroₓ _).symm

theorem top_caratheodory : (⊤ : outer_measure α).caratheodory = ⊤ :=
  top_unique$
    fun s hs =>
      (is_caratheodory_iff_le _).2$
        fun t =>
          t.eq_empty_or_nonempty.elim
            (fun ht =>
              by 
                simp [ht])
            fun ht =>
              by 
                simp only [ht, top_apply, le_top]

theorem le_add_caratheodory (m₁ m₂ : outer_measure α) :
  m₁.caratheodory⊓m₂.caratheodory ≤ (m₁+m₂ : outer_measure α).caratheodory :=
  fun s ⟨hs₁, hs₂⟩ t =>
    by 
      simp [hs₁ t, hs₂ t, add_left_commₓ, add_assocₓ]

theorem le_sum_caratheodory {ι} (m : ι → outer_measure α) : (⨅i, (m i).caratheodory) ≤ (Sum m).caratheodory :=
  fun s h t =>
    by 
      simp [fun i => MeasurableSpace.measurable_set_infi.1 h i t, Ennreal.tsum_add]

theorem le_smul_caratheodory (a : ℝ≥0∞) (m : outer_measure α) : m.caratheodory ≤ (a • m).caratheodory :=
  fun s h t =>
    by 
      simp [h t, mul_addₓ]

@[simp]
theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
  top_unique$
    fun s _ t =>
      by 
        byCases' ht : a ∈ t 
        swap
        ·
          simp [ht]
        byCases' hs : a ∈ s <;> simp 

section InfGen

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def Inf_gen (m : Set (outer_measure α)) (s : Set α) : ℝ≥0∞ :=
  ⨅(μ : outer_measure α)(h : μ ∈ m), μ s

theorem Inf_gen_def (m : Set (outer_measure α)) (t : Set α) : Inf_gen m t = ⨅(μ : outer_measure α)(h : μ ∈ m), μ t :=
  rfl

theorem Inf_eq_bounded_by_Inf_gen (m : Set (outer_measure α)) : Inf m = outer_measure.bounded_by (Inf_gen m) :=
  by 
    refine' le_antisymmₓ _ _
    ·
      refine' le_bounded_by.2$ fun s => _ 
      refine' le_binfi _ 
      intro μ hμ 
      refine' (show Inf m ≤ μ from Inf_le hμ) s
    ·
      refine' le_Inf _ 
      intro μ hμ t 
      refine' le_transₓ (bounded_by_le t) (binfi_le μ hμ)

theorem supr_Inf_gen_nonempty {m : Set (outer_measure α)} (h : m.nonempty) (t : Set α) :
  (⨆h : t.nonempty, Inf_gen m t) = ⨅(μ : outer_measure α)(h : μ ∈ m), μ t :=
  by 
    rcases t.eq_empty_or_nonempty with (rfl | ht)
    ·
      rcases h with ⟨μ, hμ⟩
      rw [eq_false_intro empty_not_nonempty, supr_false, eq_comm]
      simpRw [empty']
      apply bot_unique 
      refine' infi_le_of_le μ (infi_le _ hμ)
    ·
      simp [ht, Inf_gen_def]

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem Inf_apply {m : Set (outer_measure α)} {s : Set α} (h : m.nonempty) :
  Inf m s = ⨅(t : ℕ → Set α)(h2 : s ⊆ Union t), ∑'n, ⨅(μ : outer_measure α)(h3 : μ ∈ m), μ (t n) :=
  by 
    simpRw [Inf_eq_bounded_by_Inf_gen, bounded_by_apply, supr_Inf_gen_nonempty h]

/-- The value of the Infimum of a set of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem Inf_apply' {m : Set (outer_measure α)} {s : Set α} (h : s.nonempty) :
  Inf m s = ⨅(t : ℕ → Set α)(h2 : s ⊆ Union t), ∑'n, ⨅(μ : outer_measure α)(h3 : μ ∈ m), μ (t n) :=
  m.eq_empty_or_nonempty.elim
    (fun hm =>
      by 
        simp [hm, h])
    Inf_apply

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem infi_apply {ι} [Nonempty ι] (m : ι → outer_measure α) (s : Set α) :
  (⨅i, m i) s = ⨅(t : ℕ → Set α)(h2 : s ⊆ Union t), ∑'n, ⨅i, m i (t n) :=
  by 
    rw [infi, Inf_apply (range_nonempty m)]
    simp only [infi_range]

/-- The value of the Infimum of a family of outer measures on a nonempty set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem infi_apply' {ι} (m : ι → outer_measure α) {s : Set α} (hs : s.nonempty) :
  (⨅i, m i) s = ⨅(t : ℕ → Set α)(h2 : s ⊆ Union t), ∑'n, ⨅i, m i (t n) :=
  by 
    rw [infi, Inf_apply' hs]
    simp only [infi_range]

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem binfi_apply
{ι}
{I : set ι}
(hI : I.nonempty)
(m : ι → outer_measure α)
(s : set α) : «expr = »(«expr⨅ , »((i «expr ∈ » I), m i) s, «expr⨅ , »((t : exprℕ() → set α)
  (h2 : «expr ⊆ »(s, Union t)), «expr∑' , »((n), «expr⨅ , »((i «expr ∈ » I), m i (t n))))) :=
by { haveI [] [] [":=", expr hI.to_subtype],
  simp [] [] ["only"] ["[", "<-", expr infi_subtype'', ",", expr infi_apply, "]"] [] [] }

/-- The value of the Infimum of a nonempty family of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
theorem binfi_apply' {ι} (I : Set ι) (m : ι → outer_measure α) {s : Set α} (hs : s.nonempty) :
  (⨅(i : _)(_ : i ∈ I), m i) s = ⨅(t : ℕ → Set α)(h2 : s ⊆ Union t), ∑'n, ⨅(i : _)(_ : i ∈ I), m i (t n) :=
  by 
    simp only [←infi_subtype'', infi_apply' _ hs]

theorem map_infi_le {ι β} (f : α → β) (m : ι → outer_measure α) : map f (⨅i, m i) ≤ ⨅i, map f (m i) :=
  (map_mono f).map_infi_le

theorem comap_infi {ι β} (f : α → β) (m : ι → outer_measure β) : comap f (⨅i, m i) = ⨅i, comap f (m i) :=
  by 
    refine' ext_nonempty fun s hs => _ 
    refine' ((comap_mono f).map_infi_le s).antisymm _ 
    simp only [comap_apply, infi_apply' _ hs, infi_apply' _ (hs.image _), le_infi_iff, Set.image_subset_iff,
      preimage_Union]
    refine' fun t ht => infi_le_of_le _ (infi_le_of_le ht$ Ennreal.tsum_le_tsum$ fun k => _)
    exact infi_le_infi fun i => (m i).mono (image_preimage_subset _ _)

theorem map_infi {ι β} {f : α → β} (hf : injective f) (m : ι → outer_measure α) :
  map f (⨅i, m i) = restrict (range f) (⨅i, map f (m i)) :=
  by 
    refine' Eq.trans _ (map_comap _ _)
    simp only [comap_infi, comap_map hf]

theorem map_infi_comap {ι β} [Nonempty ι] {f : α → β} (m : ι → outer_measure β) :
  map f (⨅i, comap f (m i)) = ⨅i, map f (comap f (m i)) :=
  by 
    refine' (map_infi_le _ _).antisymm fun s => _ 
    simp only [map_apply, comap_apply, infi_apply, le_infi_iff]
    refine' fun t ht => infi_le_of_le (fun n => f '' t n ∪ «expr ᶜ» (range f)) (infi_le_of_le _ _)
    ·
      rw [←Union_union, Set.union_comm, ←inter_subset, ←image_Union, ←image_preimage_eq_inter_range]
      exact image_subset _ ht
    ·
      refine' Ennreal.tsum_le_tsum fun n => infi_le_infi fun i => (m i).mono _ 
      simp 

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem map_binfi_comap
{ι β}
{I : set ι}
(hI : I.nonempty)
{f : α → β}
(m : ι → outer_measure β) : «expr = »(map f «expr⨅ , »((i «expr ∈ » I), comap f (m i)), «expr⨅ , »((i «expr ∈ » I), map f (comap f (m i)))) :=
by { haveI [] [] [":=", expr hI.to_subtype],
  rw ["[", "<-", expr infi_subtype'', ",", "<-", expr infi_subtype'', "]"] [],
  exact [expr map_infi_comap _] }

theorem restrict_infi_restrict {ι} (s : Set α) (m : ι → outer_measure α) :
  restrict s (⨅i, restrict s (m i)) = restrict s (⨅i, m i) :=
  calc restrict s (⨅i, restrict s (m i)) = restrict (range (coeₓ : s → α)) (⨅i, restrict s (m i)) :=
    by 
      rw [Subtype.range_coe]
    _ = map (coeₓ : s → α) (⨅i, comap coeₓ (m i)) := (map_infi Subtype.coe_injective _).symm 
    _ = restrict s (⨅i, m i) := congr_argₓ (map coeₓ) (comap_infi _ _).symm
    

theorem restrict_infi {ι} [Nonempty ι] (s : Set α) (m : ι → outer_measure α) :
  restrict s (⨅i, m i) = ⨅i, restrict s (m i) :=
  (congr_argₓ (map coeₓ) (comap_infi _ _)).trans (map_infi_comap _)

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem restrict_binfi
{ι}
{I : set ι}
(hI : I.nonempty)
(s : set α)
(m : ι → outer_measure α) : «expr = »(restrict s «expr⨅ , »((i «expr ∈ » I), m i), «expr⨅ , »((i «expr ∈ » I), restrict s (m i))) :=
by { haveI [] [] [":=", expr hI.to_subtype],
  rw ["[", "<-", expr infi_subtype'', ",", "<-", expr infi_subtype'', "]"] [],
  exact [expr restrict_infi _ _] }

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
theorem restrict_Inf_eq_Inf_restrict (m : Set (outer_measure α)) {s : Set α} (hm : m.nonempty) :
  restrict s (Inf m) = Inf (restrict s '' m) :=
  by 
    simp only [Inf_eq_infi, restrict_binfi, hm, infi_image]

end InfGen

end OuterMeasure

open OuterMeasure

/-! ### Induced Outer Measure

  We can extend a function defined on a subset of `set α` to an outer measure.
  The underlying function is called `extend`, and the measure it induces is called
  `induced_outer_measure`.

  Some lemmas below are proven twice, once in the general case, and one where the function `m`
  is only defined on measurable sets (i.e. when `P = measurable_set`). In the latter cases, we can
  remove some hypotheses in the statement. The general version has the same name, but with a prime
  at the end. -/


section Extend

variable{α : Type _}{P : α → Prop}

variable(m : ∀ s : α, P s → ℝ≥0∞)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ℝ≥0∞`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ℝ≥0∞ :=
  ⨅h : P s, m s h

theorem extend_eq {s : α} (h : P s) : extend m s = m s h :=
  by 
    simp [extend, h]

theorem extend_eq_top {s : α} (h : ¬P s) : extend m s = ∞ :=
  by 
    simp [extend, h]

theorem le_extend {s : α} (h : P s) : m s h ≤ extend m s :=
  by 
    simp only [extend, le_infi_iff]
    intro 
    rfl'

theorem extend_congr {β : Type _} {Pb : β → Prop} {mb : ∀ s : β, Pb s → ℝ≥0∞} {sa : α} {sb : β} (hP : P sa ↔ Pb sb)
  (hm : ∀ ha : P sa hb : Pb sb, m sa ha = mb sb hb) : extend m sa = extend mb sb :=
  infi_congr_Prop hP fun h => hm _ _

end Extend

section ExtendSet

variable{α : Type _}{P : Set α → Prop}

variable{m : ∀ s : Set α, P s → ℝ≥0∞}

variable(P0 : P ∅)(m0 : m ∅ P0 = 0)

variable(PU : ∀ ⦃f : ℕ → Set α⦄ hm : ∀ i, P (f i), P (⋃i, f i))

variable(mU : ∀ ⦃f : ℕ → Set α⦄ hm : ∀ i, P (f i), Pairwise (Disjoint on f) → m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i))

variable(msU : ∀ ⦃f : ℕ → Set α⦄ hm : ∀ i, P (f i), m (⋃i, f i) (PU hm) ≤ ∑'i, m (f i) (hm i))

variable(m_mono : ∀ ⦃s₁ s₂ : Set α⦄ hs₁ : P s₁ hs₂ : P s₂, s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

theorem extend_empty : extend m ∅ = 0 :=
  (extend_eq _ P0).trans m0

theorem extend_Union_nat {f : ℕ → Set α} (hm : ∀ i, P (f i)) (mU : m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
  (extend_eq _ _).trans$
    mU.trans$
      by 
        congr with i 
        rw [extend_eq]

section Subadditive

include PU msU

theorem extend_Union_le_tsum_nat' (s : ℕ → Set α) : extend m (⋃i, s i) ≤ ∑'i, extend m (s i) :=
  by 
    byCases' h : ∀ i, P (s i)
    ·
      rw [extend_eq _ (PU h), congr_argₓ tsum _]
      ·
        apply msU h 
      funext i 
      apply extend_eq _ (h i)
    ·
      cases' not_forall.1 h with i hi 
      exact le_transₓ (le_infi$ fun h => hi.elim h) (Ennreal.le_tsum i)

end Subadditive

section Mono

include m_mono

theorem extend_mono' ⦃s₁ s₂ : Set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ :=
  by 
    refine' le_infi _ 
    intro h₂ 
    rw [extend_eq m h₁]
    exact m_mono h₁ h₂ hs

end Mono

section Unions

include P0 m0 PU mU

theorem extend_Union {β} [Encodable β] {f : β → Set α} (hd : Pairwise (Disjoint on f)) (hm : ∀ i, P (f i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
  by 
    rw [←Encodable.Union_decode₂, ←tsum_Union_decode₂]
    ·
      exact
        extend_Union_nat PU (fun n => Encodable.Union_decode₂_cases P0 hm)
          (mU _ (Encodable.Union_decode₂_disjoint_on hd))
    ·
      exact extend_empty P0 m0

theorem extend_union {s₁ s₂ : Set α} (hd : Disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
  extend m (s₁ ∪ s₂) = extend m s₁+extend m s₂ :=
  by 
    rw [union_eq_Union, extend_Union P0 m0 PU mU (pairwise_disjoint_on_bool.2 hd) (Bool.forall_bool.2 ⟨h₂, h₁⟩),
      tsum_fintype]
    simp 

end Unions

variable(m)

/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def induced_outer_measure : outer_measure α :=
  outer_measure.of_function (extend m) (extend_empty P0 m0)

variable{m P0 m0}

theorem le_induced_outer_measure {μ : outer_measure α} :
  μ ≤ induced_outer_measure m P0 m0 ↔ ∀ s hs : P s, μ s ≤ m s hs :=
  le_of_function.trans$ forall_congrₓ$ fun s => le_infi_iff

/-- If `P u` is `false` for any set `u` that has nonempty intersection both with `s` and `t`, then
`μ (s ∪ t) = μ s + μ t`, where `μ = induced_outer_measure m P0 m0`.

E.g., if `α` is an (e)metric space and `P u = diam u < r`, then this lemma implies that
`μ (s ∪ t) = μ s + μ t` on any two sets such that `r ≤ edist x y` for all `x ∈ s` and `y ∈ t`. -/
theorem induced_outer_measure_union_of_false_of_nonempty_inter {s t : Set α}
  (h : ∀ u, (s ∩ u).Nonempty → (t ∩ u).Nonempty → ¬P u) :
  induced_outer_measure m P0 m0 (s ∪ t) = induced_outer_measure m P0 m0 s+induced_outer_measure m P0 m0 t :=
  of_function_union_of_top_of_nonempty_inter$ fun u hsu htu => @infi_of_empty _ _ _ ⟨h u hsu htu⟩ _

include msU m_mono

theorem induced_outer_measure_eq_extend' {s : Set α} (hs : P s) : induced_outer_measure m P0 m0 s = extend m s :=
  of_function_eq s (fun t => extend_mono' m_mono hs) (extend_Union_le_tsum_nat' PU msU)

theorem induced_outer_measure_eq' {s : Set α} (hs : P s) : induced_outer_measure m P0 m0 s = m s hs :=
  (induced_outer_measure_eq_extend' PU msU m_mono hs).trans$ extend_eq _ _

theorem induced_outer_measure_eq_infi (s : Set α) :
  induced_outer_measure m P0 m0 s = ⨅(t : Set α)(ht : P t)(h : s ⊆ t), m t ht :=
  by 
    apply le_antisymmₓ
    ·
      simp only [le_infi_iff]
      intro t ht 
      simp only [le_infi_iff]
      intro hs 
      refine' le_transₓ (mono' _ hs) _ 
      exact le_of_eqₓ (induced_outer_measure_eq' _ msU m_mono _)
    ·
      refine' le_infi _ 
      intro f 
      refine' le_infi _ 
      intro hf 
      refine' le_transₓ _ (extend_Union_le_tsum_nat' _ msU _)
      refine' le_infi _ 
      intro h2f 
      refine' infi_le_of_le _ (infi_le_of_le h2f$ infi_le _ hf)

theorem induced_outer_measure_preimage (f : α ≃ α) (Pm : ∀ s : Set α, P (f ⁻¹' s) ↔ P s)
  (mm : ∀ s : Set α hs : P s, m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs) {A : Set α} :
  induced_outer_measure m P0 m0 (f ⁻¹' A) = induced_outer_measure m P0 m0 A :=
  by 
    simp only [induced_outer_measure_eq_infi _ msU m_mono]
    symm 
    refine' infi_congr (preimage f) f.injective.preimage_surjective _ 
    intro s 
    refine' infi_congr_Prop (Pm s) _ 
    intro hs 
    refine' infi_congr_Prop f.surjective.preimage_subset_preimage_iff _ 
    intro h2s 
    exact mm s hs

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem induced_outer_measure_exists_set
{s : set α}
(hs : «expr ≠ »(induced_outer_measure m P0 m0 s, «expr∞»()))
{ε : «exprℝ≥0∞»()}
(hε : «expr ≠ »(ε, 0)) : «expr∃ , »((t : set α)
 (ht : P t), «expr ∧ »(«expr ⊆ »(s, t), «expr ≤ »(induced_outer_measure m P0 m0 t, «expr + »(induced_outer_measure m P0 m0 s, ε)))) :=
begin
  have [] [] [":=", expr ennreal.lt_add_right hs hε],
  conv ["at", ident this] [] { to_lhs,
    rw [expr induced_outer_measure_eq_infi _ msU m_mono] },
  simp [] [] ["only"] ["[", expr infi_lt_iff, "]"] [] ["at", ident this],
  rcases [expr this, "with", "⟨", ident t, ",", ident h1t, ",", ident h2t, ",", ident h3t, "⟩"],
  exact [expr ⟨t, h1t, h2t, le_trans «expr $ »(le_of_eq, induced_outer_measure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩]
end

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `of_function_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
theorem induced_outer_measure_caratheodory (s : Set α) :
  (induced_outer_measure m P0 m0).caratheodory.MeasurableSet' s ↔
    ∀ t : Set α,
      P t →
        (induced_outer_measure m P0 m0 (t ∩ s)+induced_outer_measure m P0 m0 (t \ s)) ≤
          induced_outer_measure m P0 m0 t :=
  by 
    rw [is_caratheodory_iff_le]
    split 
    ·
      intro h t ht 
      exact h t
    ·
      intro h u 
      convRHS => rw [induced_outer_measure_eq_infi _ msU m_mono]
      refine' le_infi _ 
      intro t 
      refine' le_infi _ 
      intro ht 
      refine' le_infi _ 
      intro h2t 
      refine' le_transₓ _ (le_transₓ (h t ht)$ le_of_eqₓ$ induced_outer_measure_eq' _ msU m_mono ht)
      refine' add_le_add (mono' _$ Set.inter_subset_inter_left _ h2t) (mono' _$ diff_subset_diff_left h2t)

end ExtendSet

/-! If `P` is `measurable_set` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/


section MeasurableSpace

variable{α : Type _}[MeasurableSpace α]

variable{m : ∀ s : Set α, MeasurableSet s → ℝ≥0∞}

variable(m0 : m ∅ MeasurableSet.empty = 0)

variable(mU :
    ∀ ⦃f : ℕ → Set α⦄ hm : ∀ i, MeasurableSet (f i),
      Pairwise (Disjoint on f) → m (⋃i, f i) (MeasurableSet.Union hm) = ∑'i, m (f i) (hm i))

include m0 mU

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem extend_mono
{s₁ s₂ : set α}
(h₁ : measurable_set s₁)
(hs : «expr ⊆ »(s₁, s₂)) : «expr ≤ »(extend m s₁, extend m s₂) :=
begin
  refine [expr le_infi _],
  intro [ident h₂],
  have [] [] [":=", expr extend_union measurable_set.empty m0 measurable_set.Union mU disjoint_diff h₁ (h₂.diff h₁)],
  rw [expr union_diff_cancel hs] ["at", ident this],
  rw ["<-", expr extend_eq m] [],
  exact [expr le_iff_exists_add.2 ⟨_, this⟩]
end

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem extend_Union_le_tsum_nat : ∀
s : exprℕ() → set α, «expr ≤ »(extend m «expr⋃ , »((i), s i), «expr∑' , »((i), extend m (s i))) :=
begin
  refine [expr extend_Union_le_tsum_nat' measurable_set.Union _],
  intros [ident f, ident h],
  simp [] [] [] ["[", expr Union_disjointed.symm, "]"] [] [] { single_pass := tt },
  rw ["[", expr mU (measurable_set.disjointed h) (disjoint_disjointed _), "]"] [],
  refine [expr ennreal.tsum_le_tsum (λ i, _)],
  rw ["[", "<-", expr extend_eq m, ",", "<-", expr extend_eq m, "]"] [],
  exact [expr extend_mono m0 mU (measurable_set.disjointed h _) (disjointed_le f _)]
end

theorem induced_outer_measure_eq_extend {s : Set α} (hs : MeasurableSet s) :
  induced_outer_measure m MeasurableSet.empty m0 s = extend m s :=
  of_function_eq s (fun t => extend_mono m0 mU hs) (extend_Union_le_tsum_nat m0 mU)

theorem induced_outer_measure_eq {s : Set α} (hs : MeasurableSet s) :
  induced_outer_measure m MeasurableSet.empty m0 s = m s hs :=
  (induced_outer_measure_eq_extend m0 mU hs).trans$ extend_eq _ _

end MeasurableSpace

namespace OuterMeasure

variable{α : Type _}[MeasurableSpace α](m : outer_measure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : outer_measure α :=
  induced_outer_measure (fun s _ => m s) MeasurableSet.empty m.empty

theorem le_trim : m ≤ m.trim :=
  le_of_function.mpr$ fun s => le_infi$ fun _ => le_reflₓ _

theorem trim_eq {s : Set α} (hs : MeasurableSet s) : m.trim s = m s :=
  induced_outer_measure_eq' MeasurableSet.Union (fun f hf => m.Union_nat f) (fun _ _ _ _ h => m.mono h) hs

theorem trim_congr {m₁ m₂ : outer_measure α} (H : ∀ {s : Set α}, MeasurableSet s → m₁ s = m₂ s) : m₁.trim = m₂.trim :=
  by 
    unfold trim 
    congr 
    funext s hs 
    exact H hs

@[mono]
theorem trim_mono : Monotone (trim : outer_measure α → outer_measure α) :=
  fun m₁ m₂ H s => binfi_le_binfi$ fun f hs => Ennreal.tsum_le_tsum$ fun b => infi_le_infi$ fun hf => H _

theorem le_trim_iff {m₁ m₂ : outer_measure α} : m₁ ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_of_function.trans$ forall_congrₓ$ fun s => le_infi_iff

theorem trim_le_trim_iff {m₁ m₂ : outer_measure α} : m₁.trim ≤ m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s ≤ m₂ s :=
  le_trim_iff.trans$
    forall_congrₓ$
      fun s =>
        forall_congrₓ$
          fun hs =>
            by 
              rw [trim_eq _ hs]

theorem trim_eq_trim_iff {m₁ m₂ : outer_measure α} : m₁.trim = m₂.trim ↔ ∀ s, MeasurableSet s → m₁ s = m₂ s :=
  by 
    simp only [le_antisymm_iffₓ, trim_le_trim_iff, forall_and_distrib]

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem trim_eq_infi
(s : set α) : «expr = »(m.trim s, «expr⨅ , »((t) (st : «expr ⊆ »(s, t)) (ht : measurable_set t), m t)) :=
by { simp [] [] ["only"] ["[", expr infi_comm, "]"] [] [] { single_pass := tt },
  exact [expr induced_outer_measure_eq_infi measurable_set.Union (λ f _, m.Union_nat f) (λ _ _ _ _ h, m.mono h) s] }

theorem trim_eq_infi' (s : Set α) : m.trim s = ⨅t : { t // s ⊆ t ∧ MeasurableSet t }, m t :=
  by 
    simp [infi_subtype, infi_and, trim_eq_infi]

theorem trim_trim (m : outer_measure α) : m.trim.trim = m.trim :=
  trim_eq_trim_iff.2$ fun s => m.trim_eq

@[simp]
theorem trim_zero : (0 : outer_measure α).trim = 0 :=
  ext$
    fun s =>
      le_antisymmₓ (le_transₓ ((trim 0).mono (subset_univ s))$ le_of_eqₓ$ trim_eq _ MeasurableSet.univ) (zero_le _)

theorem trim_sum_ge {ι} (m : ι → outer_measure α) : (Sum fun i => (m i).trim) ≤ (Sum m).trim :=
  fun s =>
    by 
      simp [trim_eq_infi] <;>
        exact fun t st ht => Ennreal.tsum_le_tsum fun i => infi_le_of_le t$ infi_le_of_le st$ infi_le _ ht

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_measurable_superset_eq_trim
(m : outer_measure α)
(s : set α) : «expr∃ , »((t), «expr ∧ »(«expr ⊆ »(s, t), «expr ∧ »(measurable_set t, «expr = »(m t, m.trim s)))) :=
begin
  simp [] [] ["only"] ["[", expr trim_eq_infi, "]"] [] [],
  set [] [ident ms] [] [":="] [expr «expr⨅ , »((t : set α) (st : «expr ⊆ »(s, t)) (ht : measurable_set t), m t)] [],
  by_cases [expr hs, ":", expr «expr = »(ms, «expr∞»())],
  { simp [] [] ["only"] ["[", expr hs, "]"] [] [],
    simp [] [] ["only"] ["[", expr infi_eq_top, "]"] [] ["at", ident hs],
    exact [expr ⟨univ, subset_univ s, measurable_set.univ, hs _ (subset_univ s) measurable_set.univ⟩] },
  { have [] [":", expr ∀
     r «expr > » ms, «expr∃ , »((t), «expr ∧ »(«expr ⊆ »(s, t), «expr ∧ »(measurable_set t, «expr < »(m t, r))))] [],
    { intros [ident r, ident hs],
      simpa [] [] [] ["[", expr infi_lt_iff, "]"] [] ["using", expr hs] },
    have [] [":", expr ∀
     n : exprℕ(), «expr∃ , »((t), «expr ∧ »(«expr ⊆ »(s, t), «expr ∧ »(measurable_set t, «expr < »(m t, «expr + »(ms, «expr ⁻¹»(n))))))] [],
    { assume [binders (n)],
      refine [expr this _ (ennreal.lt_add_right hs _)],
      simp [] [] [] [] [] [] },
    choose [] [ident t] [ident hsub, ident hm, ident hm'] [],
    refine [expr ⟨«expr⋂ , »((n), t n), subset_Inter hsub, measurable_set.Inter hm, _⟩],
    have [] [":", expr tendsto (λ n : exprℕ(), «expr + »(ms, «expr ⁻¹»(n))) at_top (expr𝓝() «expr + »(ms, 0))] [],
    from [expr tendsto_const_nhds.add ennreal.tendsto_inv_nat_nhds_zero],
    rw [expr add_zero] ["at", ident this],
    refine [expr le_antisymm «expr $ »(ge_of_tendsto' this, λ n, _) _],
    { exact [expr le_trans «expr $ »(m.mono', Inter_subset t n) (hm' n).le] },
    { refine [expr infi_le_of_le «expr⋂ , »((n), t n) _],
      refine [expr infi_le_of_le (subset_Inter hsub) _],
      refine [expr infi_le _ (measurable_set.Inter hm)] } }
end

theorem exists_measurable_superset_of_trim_eq_zero {m : outer_measure α} {s : Set α} (h : m.trim s = 0) :
  ∃ t, s ⊆ t ∧ MeasurableSet t ∧ m t = 0 :=
  by 
    rcases exists_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩
    exact ⟨t, hst, ht, h ▸ hm⟩

/-- If `μ i` is a countable family of outer measures, then for every set `s` there exists
a measurable set `t ⊇ s` such that `μ i t = (μ i).trim s` for all `i`. -/
theorem exists_measurable_superset_forall_eq_trim {ι} [Encodable ι] (μ : ι → outer_measure α) (s : Set α) :
  ∃ t, s ⊆ t ∧ MeasurableSet t ∧ ∀ i, μ i t = (μ i).trim s :=
  by 
    choose t hst ht hμt using fun i => (μ i).exists_measurable_superset_eq_trim s 
    replace hst := subset_Inter hst 
    replace ht := MeasurableSet.Inter ht 
    refine' ⟨⋂i, t i, hst, ht, fun i => le_antisymmₓ _ _⟩
    exacts[hμt i ▸ (μ i).mono (Inter_subset _ _), (mono' _ hst).trans_eq ((μ i).trim_eq ht)]

-- error in MeasureTheory.Measure.OuterMeasure: ././Mathport/Syntax/Translate/Basic.lean:341:40: in rcases: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- If `m₁ s = op (m₂ s) (m₃ s)` for all `s`, then the same is true for `m₁.trim`, `m₂.trim`,
and `m₃ s`. -/
theorem trim_binop
{m₁ m₂ m₃ : outer_measure α}
{op : «exprℝ≥0∞»() → «exprℝ≥0∞»() → «exprℝ≥0∞»()}
(h : ∀ s, «expr = »(m₁ s, op (m₂ s) (m₃ s)))
(s : set α) : «expr = »(m₁.trim s, op (m₂.trim s) (m₃.trim s)) :=
begin
  rcases [expr exists_measurable_superset_forall_eq_trim «expr![ , ]»([m₁, m₂, m₃]) s, "with", "⟨", ident t, ",", ident hst, ",", ident ht, ",", ident htm, "⟩"],
  simp [] [] ["only"] ["[", expr fin.forall_fin_succ, ",", expr matrix.cons_val_zero, ",", expr matrix.cons_val_succ, "]"] [] ["at", ident htm],
  rw ["[", "<-", expr htm.1, ",", "<-", expr htm.2.1, ",", "<-", expr htm.2.2.1, ",", expr h, "]"] []
end

/-- If `m₁ s = op (m₂ s)` for all `s`, then the same is true for `m₁.trim` and `m₂.trim`. -/
theorem trim_op {m₁ m₂ : outer_measure α} {op : ℝ≥0∞ → ℝ≥0∞} (h : ∀ s, m₁ s = op (m₂ s)) (s : Set α) :
  m₁.trim s = op (m₂.trim s) :=
  @trim_binop α _ m₁ m₂ 0 (fun a b => op a) h s

/-- `trim` is additive. -/
theorem trim_add (m₁ m₂ : outer_measure α) : (m₁+m₂).trim = m₁.trim+m₂.trim :=
  ext$ trim_binop (add_apply m₁ m₂)

/-- `trim` respects scalar multiplication. -/
theorem trim_smul (c : ℝ≥0∞) (m : outer_measure α) : (c • m).trim = c • m.trim :=
  ext$ trim_op (smul_apply c m)

/-- `trim` sends the supremum of two outer measures to the supremum of the trimmed measures. -/
theorem trim_sup (m₁ m₂ : outer_measure α) : (m₁⊔m₂).trim = m₁.trim⊔m₂.trim :=
  ext$ fun s => (trim_binop (sup_apply m₁ m₂) s).trans (sup_apply _ _ _).symm

/-- `trim` sends the supremum of a countable family of outer measures to the supremum
of the trimmed measures. -/
theorem trim_supr {ι} [Encodable ι] (μ : ι → outer_measure α) : trim (⨆i, μ i) = ⨆i, trim (μ i) :=
  by 
    ext1 s 
    rcases exists_measurable_superset_forall_eq_trim (fun o => Option.elim o (supr μ) μ) s with ⟨t, hst, ht, hμt⟩
    simp only [Option.forall, Option.elim] at hμt 
    simp only [supr_apply, ←hμt.1, ←hμt.2]

/-- The trimmed property of a measure μ states that `μ.to_outer_measure.trim = μ.to_outer_measure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
theorem restrict_trim {μ : outer_measure α} {s : Set α} (hs : MeasurableSet s) :
  (restrict s μ).trim = restrict s μ.trim :=
  by 
    refine' le_antisymmₓ (fun t => _) (le_trim_iff.2$ fun t ht => _)
    ·
      rw [restrict_apply]
      rcases μ.exists_measurable_superset_eq_trim (t ∩ s) with ⟨t', htt', ht', hμt'⟩
      rw [←hμt']
      rw [inter_subset] at htt' 
      refine' (mono' _ htt').trans _ 
      rw [trim_eq _ (hs.compl.union ht'), restrict_apply, union_inter_distrib_right, compl_inter_self, Set.empty_union]
      exact μ.mono' (inter_subset_left _ _)
    ·
      rw [restrict_apply, trim_eq _ (ht.inter hs), restrict_apply]
      exact le_rfl

end OuterMeasure

end MeasureTheory

