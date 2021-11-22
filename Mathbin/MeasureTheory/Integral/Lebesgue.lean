import Mathbin.MeasureTheory.Measure.MutuallySingular 
import Mathbin.MeasureTheory.Constructions.BorelSpace 
import Mathbin.Algebra.IndicatorFunction 
import Mathbin.Algebra.Support

/-!
# Lebesgue integral for `ℝ≥0∞`-valued functions

We define simple functions and show that each Borel measurable function on `ℝ≥0∞` can be
approximated by a sequence of simple functions.

To prove something for an arbitrary measurable function into `ℝ≥0∞`, the theorem
`measurable.ennreal_induction` shows that is it sufficient to show that the property holds for
(multiples of) characteristic functions and is closed under addition and supremum of increasing
sequences of functions.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/


noncomputable theory

open Set hiding restrict restrict_apply

open Filter Ennreal

open function(support)

open_locale Classical TopologicalSpace BigOperators Nnreal Ennreal MeasureTheory

namespace MeasureTheory

variable{α β γ δ : Type _}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure simple_func.{u, v}(α : Type u)[MeasurableSpace α](β : Type v) where 
  toFun : α → β 
  measurable_set_fiber' : ∀ x, MeasurableSet (to_fun ⁻¹' {x})
  finite_range' : (Set.Range to_fun).Finite

local infixr:25 " →ₛ " => simple_func

namespace SimpleFunc

section Measurable

variable[MeasurableSpace α]

instance CoeFun : CoeFun (α →ₛ β) fun _ => α → β :=
  ⟨to_fun⟩

theorem coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g :=
  by 
    cases f <;> cases g <;> congr <;> exact H

@[ext]
theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
  coe_injective$ funext H

theorem finite_range (f : α →ₛ β) : (Set.Range f).Finite :=
  f.finite_range'

theorem measurable_set_fiber (f : α →ₛ β) (x : β) : MeasurableSet (f ⁻¹' {x}) :=
  f.measurable_set_fiber' x

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : Finset β :=
  f.finite_range.to_finset

@[simp]
theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
  finite.mem_to_finset _

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range :=
  mem_range.2 ⟨x, rfl⟩

@[simp]
theorem coe_range (f : α →ₛ β) : («expr↑ » f.range : Set β) = Set.Range f :=
  f.finite_range.coe_to_finset

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : Measureₓ α} (H : μ (f ⁻¹' {x}) ≠ 0) : x ∈ f.range :=
  let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H 
  mem_range.2 ⟨a, ha⟩

theorem forall_range_iff {f : α →ₛ β} {p : β → Prop} : (∀ y _ : y ∈ f.range, p y) ↔ ∀ x, p (f x) :=
  by 
    simp only [mem_range, Set.forall_range_iff]

theorem exists_range_iff {f : α →ₛ β} {p : β → Prop} : (∃ (y : _)(_ : y ∈ f.range), p y) ↔ ∃ x, p (f x) :=
  by 
    simpa only [mem_range, exists_prop] using Set.exists_range_iff

theorem preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
  preimage_singleton_eq_empty.trans$ not_congr mem_range.symm

theorem exists_forall_le [Nonempty β] [DirectedOrder β] (f : α →ₛ β) : ∃ C, ∀ x, f x ≤ C :=
  f.range.exists_le.imp$ fun C => forall_range_iff.1

/-- Constant function as a `simple_func`. -/
def const α {β} [MeasurableSpace α] (b : β) : α →ₛ β :=
  ⟨fun a => b, fun x => MeasurableSet.const _, finite_range_const⟩

instance  [Inhabited β] : Inhabited (α →ₛ β) :=
  ⟨const _ (default _)⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b :=
  rfl

@[simp]
theorem coe_const (b : β) : «expr⇑ » (const α b) = Function.const α b :=
  rfl

@[simp]
theorem range_const α [MeasurableSpace α] [Nonempty α] (b : β) : (const α b).range = {b} :=
  Finset.coe_injective$
    by 
      simp 

theorem range_const_subset α [MeasurableSpace α] (b : β) : (const α b).range ⊆ {b} :=
  Finset.coe_subset.1$
    by 
      simp 

theorem measurable_set_cut (r : α → β → Prop) (f : α →ₛ β) (h : ∀ b, MeasurableSet { a | r a b }) :
  MeasurableSet { a | r a (f a) } :=
  by 
    have  : { a | r a (f a) } = ⋃(b : _)(_ : b ∈ range f), { a | r a b } ∩ f ⁻¹' {b}
    ·
      ext a 
      suffices  : r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i
      ·
        simpa 
      exact ⟨fun h => ⟨a, ⟨h, rfl⟩⟩, fun ⟨a', ⟨h', e⟩⟩ => e.symm ▸ h'⟩
    rw [this]
    exact MeasurableSet.bUnion f.finite_range.countable fun b _ => MeasurableSet.inter (h b) (f.measurable_set_fiber _)

@[measurability]
theorem measurable_set_preimage (f : α →ₛ β) s : MeasurableSet (f ⁻¹' s) :=
  measurable_set_cut (fun _ b => b ∈ s) f fun b => MeasurableSet.const (b ∈ s)

/-- A simple function is measurable -/
@[measurability]
protected theorem Measurable [MeasurableSpace β] (f : α →ₛ β) : Measurable f :=
  fun s _ => measurable_set_preimage f s

@[measurability]
protected theorem AeMeasurable [MeasurableSpace β] {μ : Measureₓ α} (f : α →ₛ β) : AeMeasurable f μ :=
  f.measurable.ae_measurable

protected theorem sum_measure_preimage_singleton (f : α →ₛ β) {μ : Measureₓ α} (s : Finset β) :
  (∑y in s, μ (f ⁻¹' {y})) = μ (f ⁻¹' «expr↑ » s) :=
  sum_measure_preimage_singleton _ fun _ _ => f.measurable_set_fiber _

theorem sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : Measureₓ α) : (∑y in f.range, μ (f ⁻¹' {y})) = μ univ :=
  by 
    rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

/-- If-then-else as a `simple_func`. -/
def piecewise (s : Set α) (hs : MeasurableSet s) (f g : α →ₛ β) : α →ₛ β :=
  ⟨s.piecewise f g,
    fun x =>
      by 
        letI this : MeasurableSpace β := ⊤ <;> exact f.measurable.piecewise hs g.measurable trivialₓ,
    (f.finite_range.union g.finite_range).Subset range_ite_subset⟩

@[simp]
theorem coe_piecewise {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) :
  «expr⇑ » (piecewise s hs f g) = s.piecewise f g :=
  rfl

theorem piecewise_apply {s : Set α} (hs : MeasurableSet s) (f g : α →ₛ β) a :
  piecewise s hs f g a = if a ∈ s then f a else g a :=
  rfl

@[simp]
theorem piecewise_compl {s : Set α} (hs : MeasurableSet («expr ᶜ» s)) (f g : α →ₛ β) :
  piecewise («expr ᶜ» s) hs f g = piecewise s hs.of_compl g f :=
  coe_injective$
    by 
      simp [hs]

@[simp]
theorem piecewise_univ (f g : α →ₛ β) : piecewise univ MeasurableSet.univ f g = f :=
  coe_injective$
    by 
      simp 

@[simp]
theorem piecewise_empty (f g : α →ₛ β) : piecewise ∅ MeasurableSet.empty f g = g :=
  coe_injective$
    by 
      simp 

theorem support_indicator [HasZero β] {s : Set α} (hs : MeasurableSet s) (f : α →ₛ β) :
  Function.Support (f.piecewise s hs (simple_func.const α 0)) = s ∩ Function.Support f :=
  Set.support_indicator

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem range_indicator
{s : set α}
(hs : measurable_set s)
(hs_nonempty : s.nonempty)
(hs_ne_univ : «expr ≠ »(s, univ))
(x y : β) : «expr = »((piecewise s hs (const α x) (const α y)).range, {x, y}) :=
begin
  ext1 [] [ident z],
  rw ["[", expr mem_range, ",", expr set.mem_range, ",", expr finset.mem_insert, ",", expr finset.mem_singleton, "]"] [],
  simp_rw [expr piecewise_apply] [],
  split; intro [ident h],
  { obtain ["⟨", ident a, ",", ident haz, "⟩", ":=", expr h],
    by_cases [expr has, ":", expr «expr ∈ »(a, s)],
    { left,
      simp [] [] ["only"] ["[", expr has, ",", expr function.const_apply, ",", expr if_true, ",", expr coe_const, "]"] [] ["at", ident haz],
      exact [expr haz.symm] },
    { right,
      simp [] [] ["only"] ["[", expr has, ",", expr function.const_apply, ",", expr if_false, ",", expr coe_const, "]"] [] ["at", ident haz],
      exact [expr haz.symm] } },
  { cases [expr h] [],
    { obtain ["⟨", ident a, ",", ident has, "⟩", ":", expr «expr∃ , »((a), «expr ∈ »(a, s))],
      from [expr hs_nonempty],
      exact [expr ⟨a, by simpa [] [] [] ["[", expr has, "]"] [] ["using", expr h.symm]⟩] },
    { obtain ["⟨", ident a, ",", ident has, "⟩", ":", expr «expr∃ , »((a), «expr ∉ »(a, s))],
      { by_contra [],
        push_neg ["at", ident h],
        refine [expr hs_ne_univ _],
        ext1 [] [ident a],
        simp [] [] [] ["[", expr h a, "]"] [] [] },
      exact [expr ⟨a, by simpa [] [] [] ["[", expr has, "]"] [] ["using", expr h.symm]⟩] } }
end

theorem measurable_bind [MeasurableSpace γ] (f : α →ₛ β) (g : β → α → γ) (hg : ∀ b, Measurable (g b)) :
  Measurable fun a => g (f a) a :=
  fun s hs => (f.measurable_set_cut fun a b => g b a ∈ s)$ fun b => hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
  ⟨fun a => g (f a) a, fun c => (f.measurable_set_cut fun a b => g b a = c)$ fun b => (g b).measurable_set_preimage {c},
    (f.finite_range.bUnion fun b _ => (g b).finite_range).Subset$
      by 
        rintro _ ⟨a, rfl⟩ <;> simp  <;> exact ⟨a, a, rfl⟩⟩

@[simp]
theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) a : f.bind g a = g (f a) a :=
  rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ :=
  bind f (const α ∘ g)

theorem map_apply (g : β → γ) (f : α →ₛ β) a : f.map g a = g (f a) :=
  rfl

theorem map_map (g : β → γ) (h : γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) :=
  rfl

@[simp]
theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = (g ∘ f) :=
  rfl

@[simp]
theorem range_map [DecidableEq γ] (g : β → γ) (f : α →ₛ β) : (f.map g).range = f.range.image g :=
  Finset.coe_injective$
    by 
      simp [range_comp]

@[simp]
theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) :=
  rfl

theorem map_preimage (f : α →ₛ β) (g : β → γ) (s : Set γ) :
  f.map g ⁻¹' s = f ⁻¹' «expr↑ » (f.range.filter fun b => g b ∈ s) :=
  by 
    simp only [coe_range, sep_mem_eq, Set.mem_range, Function.comp_app, coe_map, Finset.coe_filter, ←mem_preimage,
      inter_comm, preimage_inter_range]
    apply preimage_comp

theorem map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
  f.map g ⁻¹' {c} = f ⁻¹' «expr↑ » (f.range.filter fun b => g b = c) :=
  map_preimage _ _ _

/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp [MeasurableSpace β] (f : β →ₛ γ) (g : α → β) (hgm : Measurable g) : α →ₛ γ :=
  { toFun := f ∘ g, finite_range' := f.finite_range.subset$ Set.range_comp_subset_range _ _,
    measurable_set_fiber' := fun z => hgm (f.measurable_set_fiber z) }

@[simp]
theorem coe_comp [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
  «expr⇑ » (f.comp g hgm) = (f ∘ g) :=
  rfl

theorem range_comp_subset_range [MeasurableSpace β] (f : β →ₛ γ) {g : α → β} (hgm : Measurable g) :
  (f.comp g hgm).range ⊆ f.range :=
  Finset.coe_subset.1$
    by 
      simp only [coe_range, coe_comp, Set.range_comp_subset_range]

/-- Extend a `simple_func` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
def extend [MeasurableSpace β] (f₁ : α →ₛ γ) (g : α → β) (hg : MeasurableEmbedding g) (f₂ : β →ₛ γ) : β →ₛ γ :=
  { toFun := Function.extendₓ g f₁ f₂,
    finite_range' :=
      (f₁.finite_range.union$ f₂.finite_range.subset (image_subset_range _ _)).Subset (range_extend_subset _ _ _),
    measurable_set_fiber' :=
      by 
        letI this : MeasurableSpace γ := ⊤
        haveI  : MeasurableSingletonClass γ := ⟨fun _ => trivialₓ⟩
        exact fun x => hg.measurable_extend f₁.measurable f₂.measurable (measurable_set_singleton _) }

@[simp]
theorem extend_apply [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g) (f₂ : β →ₛ γ) (x : α) :
  (f₁.extend g hg f₂) (g x) = f₁ x :=
  Function.extend_applyₓ hg.injective _ _ _

@[simp]
theorem extend_comp_eq' [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g) (f₂ : β →ₛ γ) :
  (f₁.extend g hg f₂ ∘ g) = f₁ :=
  funext$ fun x => extend_apply _ _ _ _

@[simp]
theorem extend_comp_eq [MeasurableSpace β] (f₁ : α →ₛ γ) {g : α → β} (hg : MeasurableEmbedding g) (f₂ : β →ₛ γ) :
  (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
  coe_injective$ extend_comp_eq' _ _ _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ β → γ) (g : α →ₛ β) : α →ₛ γ :=
  f.bind fun f => g.map f

@[simp]
theorem seq_apply (f : α →ₛ β → γ) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) :=
  rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ β × γ :=
  (f.map Prod.mk).seq g

@[simp]
theorem pair_apply (f : α →ₛ β) (g : α →ₛ γ) a : pair f g a = (f a, g a) :=
  rfl

theorem pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : Set β) (t : Set γ) :
  pair f g ⁻¹' Set.Prod s t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl

theorem pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  pair f g ⁻¹' {(b, c)} = f ⁻¹' {b} ∩ g ⁻¹' {c} :=
  by 
    rw [←singleton_prod_singleton]
    exact pair_preimage _ _ _ _

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f :=
  by 
    ext <;> simp 

instance  [HasZero β] : HasZero (α →ₛ β) :=
  ⟨const α 0⟩

instance  [Add β] : Add (α →ₛ β) :=
  ⟨fun f g => (f.map (·+·)).seq g⟩

instance  [Mul β] : Mul (α →ₛ β) :=
  ⟨fun f g => (f.map (·*·)).seq g⟩

instance  [HasSup β] : HasSup (α →ₛ β) :=
  ⟨fun f g => (f.map (·⊔·)).seq g⟩

instance  [HasInf β] : HasInf (α →ₛ β) :=
  ⟨fun f g => (f.map (·⊓·)).seq g⟩

instance  [LE β] : LE (α →ₛ β) :=
  ⟨fun f g => ∀ a, f a ≤ g a⟩

@[simp, normCast]
theorem coe_zero [HasZero β] : «expr⇑ » (0 : α →ₛ β) = 0 :=
  rfl

@[simp]
theorem const_zero [HasZero β] : const α (0 : β) = 0 :=
  rfl

@[simp, normCast]
theorem coe_add [Add β] (f g : α →ₛ β) : «expr⇑ » (f+g) = f+g :=
  rfl

@[simp, normCast]
theorem coe_mul [Mul β] (f g : α →ₛ β) : «expr⇑ » (f*g) = f*g :=
  rfl

@[simp, normCast]
theorem coe_le [Preorderₓ β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp]
theorem range_zero [Nonempty α] [HasZero β] : (0 : α →ₛ β).range = {0} :=
  Finset.ext$
    fun x =>
      by 
        simp [eq_comm]

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
@[simp]
theorem range_eq_empty_of_is_empty {β} [hα : is_empty α] (f : «expr →ₛ »(α, β)) : «expr = »(f.range, «expr∅»()) :=
begin
  rw ["<-", expr finset.not_nonempty_iff_eq_empty] [],
  by_contra [],
  obtain ["⟨", ident y, ",", ident hy_mem, "⟩", ":=", expr h],
  rw ["[", expr simple_func.mem_range, ",", expr set.mem_range, "]"] ["at", ident hy_mem],
  obtain ["⟨", ident x, ",", ident hxy, "⟩", ":=", expr hy_mem],
  rw [expr is_empty_iff] ["at", ident hα],
  exact [expr hα x]
end

theorem eq_zero_of_mem_range_zero [HasZero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
  forall_range_iff.2$ fun x => rfl

theorem sup_apply [HasSup β] (f g : α →ₛ β) (a : α) : (f⊔g) a = f a⊔g a :=
  rfl

theorem mul_apply [Mul β] (f g : α →ₛ β) (a : α) : (f*g) a = f a*g a :=
  rfl

theorem add_apply [Add β] (f g : α →ₛ β) (a : α) : (f+g) a = f a+g a :=
  rfl

theorem add_eq_map₂ [Add β] (f g : α →ₛ β) : (f+g) = (pair f g).map fun p : β × β => p.1+p.2 :=
  rfl

theorem mul_eq_map₂ [Mul β] (f g : α →ₛ β) : (f*g) = (pair f g).map fun p : β × β => p.1*p.2 :=
  rfl

theorem sup_eq_map₂ [HasSup β] (f g : α →ₛ β) : f⊔g = (pair f g).map fun p : β × β => p.1⊔p.2 :=
  rfl

theorem const_mul_eq_map [Mul β] (f : α →ₛ β) (b : β) : (const α b*f) = f.map fun a => b*a :=
  rfl

theorem map_add [Add β] [Add γ] {g : β → γ} (hg : ∀ x y, g (x+y) = g x+g y) (f₁ f₂ : α →ₛ β) :
  (f₁+f₂).map g = f₁.map g+f₂.map g :=
  ext$ fun x => hg _ _

instance  [AddMonoidₓ β] : AddMonoidₓ (α →ₛ β) :=
  Function.Injective.addMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add

instance AddCommMonoidₓ [AddCommMonoidₓ β] : AddCommMonoidₓ (α →ₛ β) :=
  Function.Injective.addCommMonoid (fun f => show α → β from f) coe_injective coe_zero coe_add

instance  [Neg β] : Neg (α →ₛ β) :=
  ⟨fun f => f.map Neg.neg⟩

@[simp, normCast]
theorem coe_neg [Neg β] (f : α →ₛ β) : «expr⇑ » (-f) = -f :=
  rfl

instance  [Sub β] : Sub (α →ₛ β) :=
  ⟨fun f g => (f.map Sub.sub).seq g⟩

@[simp, normCast]
theorem coe_sub [Sub β] (f g : α →ₛ β) : «expr⇑ » (f - g) = f - g :=
  rfl

theorem sub_apply [Sub β] (f g : α →ₛ β) (x : α) : (f - g) x = f x - g x :=
  rfl

instance  [AddGroupₓ β] : AddGroupₓ (α →ₛ β) :=
  Function.Injective.addGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg coe_sub

instance  [AddCommGroupₓ β] : AddCommGroupₓ (α →ₛ β) :=
  Function.Injective.addCommGroup (fun f => show α → β from f) coe_injective coe_zero coe_add coe_neg coe_sub

variable{K : Type _}

instance  [HasScalar K β] : HasScalar K (α →ₛ β) :=
  ⟨fun k f => f.map ((· • ·) k)⟩

@[simp]
theorem coe_smul [HasScalar K β] (c : K) (f : α →ₛ β) : «expr⇑ » (c • f) = c • f :=
  rfl

theorem smul_apply [HasScalar K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a :=
  rfl

instance  [Semiringₓ K] [AddCommMonoidₓ β] [Module K β] : Module K (α →ₛ β) :=
  Function.Injective.module K ⟨fun f => show α → β from f, coe_zero, coe_add⟩ coe_injective coe_smul

theorem smul_eq_map [HasScalar K β] (k : K) (f : α →ₛ β) : k • f = f.map ((· • ·) k) :=
  rfl

instance  [Preorderₓ β] : Preorderₓ (α →ₛ β) :=
  { simple_func.has_le with le_refl := fun f a => le_reflₓ _,
    le_trans := fun f g h hfg hgh a => le_transₓ (hfg _) (hgh a) }

instance  [PartialOrderₓ β] : PartialOrderₓ (α →ₛ β) :=
  { simple_func.preorder with le_antisymm := fun f g hfg hgf => ext$ fun a => le_antisymmₓ (hfg a) (hgf a) }

instance  [LE β] [OrderBot β] : OrderBot (α →ₛ β) :=
  { bot := const α ⊥, bot_le := fun f a => bot_le }

instance  [LE β] [OrderTop β] : OrderTop (α →ₛ β) :=
  { top := const α ⊤, le_top := fun f a => le_top }

instance  [SemilatticeInf β] : SemilatticeInf (α →ₛ β) :=
  { simple_func.partial_order with inf := ·⊓·, inf_le_left := fun f g a => inf_le_left,
    inf_le_right := fun f g a => inf_le_right, le_inf := fun f g h hfh hgh a => le_inf (hfh a) (hgh a) }

instance  [SemilatticeSup β] : SemilatticeSup (α →ₛ β) :=
  { simple_func.partial_order with sup := ·⊔·, le_sup_left := fun f g a => le_sup_left,
    le_sup_right := fun f g a => le_sup_right, sup_le := fun f g h hfh hgh a => sup_le (hfh a) (hgh a) }

instance  [SemilatticeSupBot β] : SemilatticeSupBot (α →ₛ β) :=
  { simple_func.semilattice_sup, simple_func.order_bot with  }

instance  [Lattice β] : Lattice (α →ₛ β) :=
  { simple_func.semilattice_sup, simple_func.semilattice_inf with  }

instance  [BoundedLattice β] : BoundedLattice (α →ₛ β) :=
  { simple_func.lattice, simple_func.order_bot, simple_func.order_top with  }

theorem finset_sup_apply [SemilatticeSupBot β] {f : γ → α →ₛ β} (s : Finset γ) (a : α) :
  s.sup f a = s.sup fun c => f c a :=
  by 
    refine' Finset.induction_on s rfl _ 
    intro a s hs ih 
    rw [Finset.sup_insert, Finset.sup_insert, sup_apply, ih]

section Restrict

variable[HasZero β]

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : Set α) : α →ₛ β :=
  if hs : MeasurableSet s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : α →ₛ β} {s : Set α} (hs : ¬MeasurableSet s) : restrict f s = 0 :=
  dif_neg hs

@[simp]
theorem coe_restrict (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) : «expr⇑ » (restrict f s) = indicator s f :=
  by 
    rw [restrict, dif_pos hs]
    rfl

@[simp]
theorem restrict_univ (f : α →ₛ β) : restrict f univ = f :=
  by 
    simp [restrict]

@[simp]
theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 :=
  by 
    simp [restrict]

theorem map_restrict_of_zero [HasZero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : Set α) :
  (f.restrict s).map g = (f.map g).restrict s :=
  ext$
    fun x =>
      if hs : MeasurableSet s then
        by 
          simp [hs, Set.indicator_comp_of_zero hg]
      else
        by 
          simp [restrict_of_not_measurable hs, hg]

theorem map_coe_ennreal_restrict (f : α →ₛ  ℝ≥0 ) (s : Set α) :
  (f.restrict s).map (coeₓ :  ℝ≥0  → ℝ≥0∞) = (f.map coeₓ).restrict s :=
  map_restrict_of_zero Ennreal.coe_zero _ _

theorem map_coe_nnreal_restrict (f : α →ₛ  ℝ≥0 ) (s : Set α) :
  (f.restrict s).map (coeₓ :  ℝ≥0  → ℝ) = (f.map coeₓ).restrict s :=
  map_restrict_of_zero Nnreal.coe_zero _ _

theorem restrict_apply (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) a : restrict f s a = indicator s f a :=
  by 
    simp only [f.coe_restrict hs]

theorem restrict_preimage (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : (0 : β) ∉ t) :
  restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
  by 
    simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]

theorem restrict_preimage_singleton (f : α →ₛ β) {s : Set α} (hs : MeasurableSet s) {r : β} (hr : r ≠ 0) :
  restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
  f.restrict_preimage hs hr.symm

theorem mem_restrict_range {r : β} {s : Set α} {f : α →ₛ β} (hs : MeasurableSet s) :
  r ∈ (restrict f s).range ↔ r = 0 ∧ s ≠ univ ∨ r ∈ f '' s :=
  by 
    rw [←Finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

theorem mem_image_of_mem_range_restrict {r : β} {s : Set α} {f : α →ₛ β} (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) :
  r ∈ f '' s :=
  if hs : MeasurableSet s then
    by 
      simpa [mem_restrict_range hs, h0] using hr
  else
    by 
      rw [restrict_of_not_measurable hs] at hr 
      exact (h0$ eq_zero_of_mem_range_zero hr).elim

@[mono]
theorem restrict_mono [Preorderₓ β] (s : Set α) {f g : α →ₛ β} (H : f ≤ g) : f.restrict s ≤ g.restrict s :=
  if hs : MeasurableSet s then
    fun x =>
      by 
        simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
  else
    by 
      simp only [restrict_of_not_measurable hs, le_reflₓ]

end Restrict

section Approx

section 

variable[SemilatticeSupBot β][HasZero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
  (Finset.range n).sup fun k => restrict (const α (i k)) { a : α | i k ≤ f a }

theorem approx_apply [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : Measurable f) :
  (approx i f n : α →ₛ β) a = (Finset.range n).sup fun k => if i k ≤ f a then i k else 0 :=
  by 
    dsimp only [approx]
    rw [finset_sup_apply]
    congr 
    funext k 
    rw [restrict_apply]
    rfl 
    exact hf measurable_set_Ici

theorem monotone_approx (i : ℕ → β) (f : α → β) : Monotone (approx i f) :=
  fun n m h => Finset.sup_mono$ Finset.range_subset.2 h

theorem approx_comp [TopologicalSpace β] [OrderClosedTopology β] [MeasurableSpace β] [OpensMeasurableSpace β]
  [MeasurableSpace γ] {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α) (hf : Measurable f) (hg : Measurable g) :
  (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) :=
  by 
    rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]

end 

theorem supr_approx_apply [TopologicalSpace β] [CompleteLattice β] [OrderClosedTopology β] [HasZero β]
  [MeasurableSpace β] [OpensMeasurableSpace β] (i : ℕ → β) (f : α → β) (a : α) (hf : Measurable f)
  (h_zero : (0 : β) = ⊥) : (⨆n, (approx i f n : α →ₛ β) a) = ⨆(k : _)(h : i k ≤ f a), i k :=
  by 
    refine' le_antisymmₓ (supr_le$ fun n => _) (supr_le$ fun k => supr_le$ fun hk => _)
    ·
      rw [approx_apply a hf, h_zero]
      refine' Finset.sup_le fun k hk => _ 
      splitIfs 
      exact le_supr_of_le k (le_supr _ h)
      exact bot_le
    ·
      refine' le_supr_of_le (k+1) _ 
      rw [approx_apply a hf]
      have  : k ∈ Finset.range (k+1) := Finset.mem_range.2 (Nat.lt_succ_selfₓ _)
      refine' le_transₓ (le_of_eqₓ _) (Finset.le_sup this)
      rw [if_pos hk]

end Approx

section Eapprox

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ℝ≥0∞ :=
  Ennreal.ofReal ((Encodable.decode ℚ n).getOrElse (0 : ℚ))

theorem ennreal_rat_embed_encode (q : ℚ) : ennreal_rat_embed (Encodable.encode q) = Real.toNnreal q :=
  by 
    rw [ennreal_rat_embed, Encodable.encodek] <;> rfl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
  approx ennreal_rat_embed

theorem eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ :=
  by 
    simp only [eapprox, approx, finset_sup_apply, Finset.sup_lt_iff, WithTop.zero_lt_top, Finset.mem_range,
      Ennreal.bot_eq_zero, restrict]
    intro b hb 
    splitIfs
    ·
      simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const]
      calc { a : α | ennreal_rat_embed b ≤ f a }.indicator (fun x => ennreal_rat_embed b) a ≤ ennreal_rat_embed b :=
        indicator_le_self _ _ a _ < ⊤ := Ennreal.coe_lt_top
    ·
      exact WithTop.zero_lt_top

@[mono]
theorem monotone_eapprox (f : α → ℝ≥0∞) : Monotone (eapprox f) :=
  monotone_approx _ f

theorem supr_eapprox_apply (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) : (⨆n, (eapprox f n : α →ₛ ℝ≥0∞) a) = f a :=
  by 
    rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl]
    refine' le_antisymmₓ (supr_le$ fun i => supr_le$ fun hi => hi) (le_of_not_gtₓ _)
    intro h 
    rcases Ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩
    have  : (Real.toNnreal q : ℝ≥0∞) ≤ ⨆(k : ℕ)(h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k
    ·
      refine' le_supr_of_le (Encodable.encode q) _ 
      rw [ennreal_rat_embed_encode q]
      refine' le_supr_of_le (le_of_ltₓ q_lt) _ 
      exact le_reflₓ _ 
    exact lt_irreflₓ _ (lt_of_le_of_ltₓ this lt_q)

theorem eapprox_comp [MeasurableSpace γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ} (hf : Measurable f) (hg : Measurable g) :
  (eapprox (f ∘ g) n : α → ℝ≥0∞) = ((eapprox f n : γ →ₛ ℝ≥0∞) ∘ g) :=
  funext$ fun a => approx_comp a hf hg

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapprox_diff (f : α → ℝ≥0∞) : ∀ n : ℕ, α →ₛ  ℝ≥0 
| 0 => (eapprox f 0).map Ennreal.toNnreal
| n+1 => (eapprox f (n+1) - eapprox f n).map Ennreal.toNnreal

theorem sum_eapprox_diff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
  (∑k in Finset.range (n+1), (eapprox_diff f k a : ℝ≥0∞)) = eapprox f n a :=
  by 
    induction' n with n IH
    ·
      simp only [Nat.nat_zero_eq_zero, Finset.sum_singleton, Finset.range_one]
      rfl
    ·
      rw [Finset.sum_range_succ, Nat.succ_eq_add_one, IH, eapprox_diff, coe_map, Function.comp_app, coe_sub,
        Pi.sub_apply, Ennreal.coe_to_nnreal, add_tsub_cancel_of_le (monotone_eapprox f (Nat.le_succₓ _) _)]
      apply (lt_of_le_of_ltₓ _ (eapprox_lt_top f (n+1) a)).Ne 
      rw [tsub_le_iff_right]
      exact le_self_add

theorem tsum_eapprox_diff (f : α → ℝ≥0∞) (hf : Measurable f) (a : α) : (∑'n, (eapprox_diff f n a : ℝ≥0∞)) = f a :=
  by 
    simpRw [Ennreal.tsum_eq_supr_nat' (tendsto_add_at_top_nat 1), sum_eapprox_diff, supr_eapprox_apply f hf a]

end Eapprox

end Measurable

section Measureₓ

variable{m : MeasurableSpace α}{μ ν : Measureₓ α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measureₓ α) : ℝ≥0∞ :=
  ∑x in f.range, x*μ (f ⁻¹' {x})

theorem lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
  f.lintegral μ = ∑x in s, x*μ (f ⁻¹' {x}) :=
  by 
    refine' Finset.sum_bij_ne_zero (fun r _ _ => r) _ _ _ _
    ·
      simpa only [forall_range_iff, mul_ne_zero_iff, and_imp]
    ·
      intros 
      assumption
    ·
      intro b _ hb 
      refine' ⟨b, _, hb, rfl⟩
      rw [mem_range, ←preimage_singleton_nonempty]
      exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2
    ·
      intros 
      rfl

theorem lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : Finset ℝ≥0∞} (hs : f.range \ {0} ⊆ s) :
  f.lintegral μ = ∑x in s, x*μ (f ⁻¹' {x}) :=
  f.lintegral_eq_of_subset$ fun x hfx _ => hs$ Finset.mem_sdiff.2 ⟨f.mem_range_self x, mt Finset.mem_singleton.1 hfx⟩

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
theorem map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) : (f.map g).lintegral μ = ∑x in f.range, g x*μ (f ⁻¹' {x}) :=
  by 
    simp only [lintegral, range_map]
    refine' Finset.sum_image' _ fun b hb => _ 
    rcases mem_range.1 hb with ⟨a, rfl⟩
    rw [map_preimage_singleton, ←f.sum_measure_preimage_singleton, Finset.mul_sum]
    refine' Finset.sum_congr _ _
    ·
      congr
    ·
      intro x 
      simp only [Finset.mem_filter]
      rintro ⟨_, h⟩
      rw [h]

theorem add_lintegral (f g : α →ₛ ℝ≥0∞) : (f+g).lintegral μ = f.lintegral μ+g.lintegral μ :=
  calc (f+g).lintegral μ = ∑x in (pair f g).range, (x.1*μ (pair f g ⁻¹' {x}))+x.2*μ (pair f g ⁻¹' {x}) :=
    by 
      rw [add_eq_map₂, map_lintegral] <;> exact Finset.sum_congr rfl fun a ha => add_mulₓ _ _ _ 
    _ = (∑x in (pair f g).range, x.1*μ (pair f g ⁻¹' {x}))+∑x in (pair f g).range, x.2*μ (pair f g ⁻¹' {x}) :=
    by 
      rw [Finset.sum_add_distrib]
    _ = ((pair f g).map Prod.fst).lintegral μ+((pair f g).map Prod.snd).lintegral μ :=
    by 
      rw [map_lintegral, map_lintegral]
    _ = lintegral f μ+lintegral g μ := rfl
    

theorem const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) : (const α x*f).lintegral μ = x*f.lintegral μ :=
  calc (f.map fun a => x*a).lintegral μ = ∑r in f.range, (x*r)*μ (f ⁻¹' {r}) := map_lintegral _ _ 
    _ = ∑r in f.range, x*r*μ (f ⁻¹' {r}) := Finset.sum_congr rfl fun a ha => mul_assocₓ _ _ _ 
    _ = x*f.lintegral μ := Finset.mul_sum.symm
    

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : MeasurableSpace α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] Measureₓ α →ₗ[ℝ≥0∞] ℝ≥0∞ :=
  { toFun :=
      fun f =>
        { toFun := lintegral f,
          map_add' :=
            by 
              simp [lintegral, mul_addₓ, Finset.sum_add_distrib],
          map_smul' :=
            fun c μ =>
              by 
                simp [lintegral, mul_left_commₓ _ c, Finset.mul_sum] },
    map_add' := fun f g => LinearMap.ext fun μ => add_lintegral f g,
    map_smul' := fun c f => LinearMap.ext fun μ => const_mul_lintegral f c }

@[simp]
theorem zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
  LinearMap.ext_iff.1 lintegralₗ.map_zero μ

theorem lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ+ν) = f.lintegral μ+f.lintegral ν :=
  (lintegralₗ f).map_add μ ν

theorem lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) : f.lintegral (c • μ) = c • f.lintegral μ :=
  (lintegralₗ f).map_smul c μ

@[simp]
theorem lintegral_zero [MeasurableSpace α] (f : α →ₛ ℝ≥0∞) : f.lintegral 0 = 0 :=
  (lintegralₗ f).map_zero

theorem lintegral_sum {m : MeasurableSpace α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → Measureₓ α) :
  f.lintegral (measure.sum μ) = ∑'i, f.lintegral (μ i) :=
  by 
    simp only [lintegral, measure.sum_apply, f.measurable_set_preimage, ←Finset.tsum_subtype, ←Ennreal.tsum_mul_left]
    apply Ennreal.tsum_comm

theorem restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
  (restrict f s).lintegral μ = ∑r in f.range, r*μ (f ⁻¹' {r} ∩ s) :=
  calc (restrict f s).lintegral μ = ∑r in f.range, r*μ (restrict f s ⁻¹' {r}) :=
    lintegral_eq_of_subset _$
      fun x hx =>
        if hxs : x ∈ s then
          fun _ =>
            by 
              simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
        else
          False.elim$
            hx$
              by 
                simp 
    _ = ∑r in f.range, r*μ (f ⁻¹' {r} ∩ s) :=
    Finset.sum_congr rfl$
      forall_range_iff.2$
        fun b =>
          if hb : f b = 0 then
            by 
              simp only [hb, zero_mul]
          else
            by 
              rw [restrict_preimage_singleton _ hs hb, inter_comm]
    

theorem lintegral_restrict {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (s : Set α) (μ : Measureₓ α) :
  f.lintegral (μ.restrict s) = ∑y in f.range, y*μ (f ⁻¹' {y} ∩ s) :=
  by 
    simp only [lintegral, measure.restrict_apply, f.measurable_set_preimage]

theorem restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
  (restrict f s).lintegral μ = f.lintegral (μ.restrict s) :=
  by 
    rw [f.restrict_lintegral hs, lintegral_restrict]

theorem const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c*μ univ :=
  by 
    rw [lintegral]
    casesI is_empty_or_nonempty α
    ·
      simp [μ.eq_zero_of_is_empty]
    ·
      simp [preimage_const_of_mem]

theorem const_lintegral_restrict (c : ℝ≥0∞) (s : Set α) : (const α c).lintegral (μ.restrict s) = c*μ s :=
  by 
    rw [const_lintegral, measure.restrict_apply MeasurableSet.univ, univ_inter]

theorem restrict_const_lintegral (c : ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
  ((const α c).restrict s).lintegral μ = c*μ s :=
  by 
    rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

theorem le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ⊔g.lintegral μ ≤ (f⊔g).lintegral μ :=
  calc f.lintegral μ⊔g.lintegral μ = ((pair f g).map Prod.fst).lintegral μ⊔((pair f g).map Prod.snd).lintegral μ := rfl 
    _ ≤ ∑x in (pair f g).range, (x.1⊔x.2)*μ (pair f g ⁻¹' {x}) :=
    by 
      rw [map_lintegral, map_lintegral]
      refine' sup_le _ _ <;> refine' Finset.sum_le_sum fun a _ => mul_le_mul_right' _ _ 
      exact le_sup_left 
      exact le_sup_right 
    _ = (f⊔g).lintegral μ :=
    by 
      rw [sup_eq_map₂, map_lintegral]
    

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono]
theorem lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) : f.lintegral μ ≤ g.lintegral ν :=
  calc f.lintegral μ ≤ f.lintegral μ⊔g.lintegral μ := le_sup_left 
    _ ≤ (f⊔g).lintegral μ := le_sup_lintegral _ _ 
    _ = g.lintegral μ :=
    by 
      rw [sup_of_le_right hfg]
    _ ≤ g.lintegral ν := Finset.sum_le_sum$ fun y hy => Ennreal.mul_left_mono$ hμν _ (g.measurable_set_preimage _)
    

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
theorem lintegral_eq_of_measure_preimage [MeasurableSpace β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞} {ν : Measureₓ β}
  (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) : f.lintegral μ = g.lintegral ν :=
  by 
    simp only [lintegral, ←H]
    apply lintegral_eq_of_subset 
    simp only [H]
    intros 
    exact mem_range_of_measure_ne_zero ‹_›

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
theorem lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) : f.lintegral μ = g.lintegral μ :=
  lintegral_eq_of_measure_preimage$
    fun y =>
      measure_congr$
        eventually.set_eq$
          h.mono$
            fun x hx =>
              by 
                simp [hx]

theorem lintegral_map' {β} [MeasurableSpace β] {μ' : Measureₓ β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞) (m' : α → β)
  (eq : ∀ a, f a = g (m' a)) (h : ∀ s, MeasurableSet s → μ' s = μ (m' ⁻¹' s)) : f.lintegral μ = g.lintegral μ' :=
  lintegral_eq_of_measure_preimage$
    fun y =>
      by 
        simp only [preimage, Eq]
        exact (h (g ⁻¹' {y}) (g.measurable_set_preimage _)).symm

theorem lintegral_map {β} [MeasurableSpace β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : Measurable f) :
  g.lintegral (measure.map f μ) = (g.comp f hf).lintegral μ :=
  Eq.symm$ lintegral_map' _ _ f (fun a => rfl) fun s hs => measure.map_apply hf hs

end Measureₓ

section FinMeasSupp

open Finset Function

theorem support_eq [MeasurableSpace α] [HasZero β] (f : α →ₛ β) :
  support f = ⋃(y : _)(_ : y ∈ f.range.filter fun y => y ≠ 0), f ⁻¹' {y} :=
  Set.ext$
    fun x =>
      by 
        simp only [Finset.set_bUnion_preimage_singleton, mem_support, Set.mem_preimage, Finset.mem_coe, mem_filter,
          mem_range_self, true_andₓ]

variable{m : MeasurableSpace α}[HasZero β][HasZero γ]{μ : Measureₓ α}{f : α →ₛ β}

theorem measurable_set_support [MeasurableSpace α] (f : α →ₛ β) : MeasurableSet (support f) :=
  by 
    rw [f.support_eq]
    exact Finset.measurable_set_bUnion _ fun y hy => measurable_set_fiber _ _

/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def fin_meas_supp {m : MeasurableSpace α} (f : α →ₛ β) (μ : Measureₓ α) : Prop :=
  f =ᶠ[μ.cofinite] 0

theorem fin_meas_supp_iff_support : f.fin_meas_supp μ ↔ μ (support f) < ∞ :=
  Iff.rfl

theorem fin_meas_supp_iff : f.fin_meas_supp μ ↔ ∀ y _ : y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
  by 
    split 
    ·
      refine' fun h y hy => lt_of_le_of_ltₓ (measure_mono _) h 
      exact fun x hx H : f x = 0 => hy$ H ▸ Eq.symm hx
    ·
      intro H 
      rw [fin_meas_supp_iff_support, support_eq]
      refine' lt_of_le_of_ltₓ (measure_bUnion_finset_le _ _) (sum_lt_top _)
      exact fun y hy => (H y (Finset.mem_filter.1 hy).2).Ne

namespace FinMeasSupp

theorem meas_preimage_singleton_ne_zero (h : f.fin_meas_supp μ) {y : β} (hy : y ≠ 0) : μ (f ⁻¹' {y}) < ∞ :=
  fin_meas_supp_iff.1 h y hy

protected theorem map {g : β → γ} (hf : f.fin_meas_supp μ) (hg : g 0 = 0) : (f.map g).FinMeasSupp μ :=
  flip lt_of_le_of_ltₓ hf (measure_mono$ support_comp_subset hg f)

theorem of_map {g : β → γ} (h : (f.map g).FinMeasSupp μ) (hg : ∀ b, g b = 0 → b = 0) : f.fin_meas_supp μ :=
  flip lt_of_le_of_ltₓ h$ measure_mono$ support_subset_comp hg _

theorem map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) : (f.map g).FinMeasSupp μ ↔ f.fin_meas_supp μ :=
  ⟨fun h => h.of_map$ fun b => hg.1, fun h => h.map$ hg.2 rfl⟩

protected theorem pair {g : α →ₛ γ} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) : (pair f g).FinMeasSupp μ :=
  calc μ (support$ pair f g) = μ (support f ∪ support g) := congr_argₓ μ$ support_prod_mk f g 
    _ ≤ μ (support f)+μ (support g) := measure_union_le _ _ 
    _ < _ := add_lt_top.2 ⟨hf, hg⟩
    

protected theorem map₂ [HasZero δ] (hf : f.fin_meas_supp μ) {g : α →ₛ γ} (hg : g.fin_meas_supp μ) {op : β → γ → δ}
  (H : op 0 0 = 0) : ((pair f g).map (Function.uncurry op)).FinMeasSupp μ :=
  (hf.pair hg).map H

protected theorem add {β} [AddMonoidₓ β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (f+g).FinMeasSupp μ :=
  by 
    rw [add_eq_map₂]
    exact hf.map₂ hg (zero_addₓ 0)

protected theorem mul {β} [MonoidWithZeroₓ β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (f*g).FinMeasSupp μ :=
  by 
    rw [mul_eq_map₂]
    exact hf.map₂ hg (zero_mul 0)

theorem lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.fin_meas_supp μ) (hf : ∀ᵐa ∂μ, f a ≠ ∞) : f.lintegral μ < ∞ :=
  by 
    refine' sum_lt_top fun a ha => _ 
    rcases eq_or_ne a ∞ with (rfl | ha)
    ·
      simp only [ae_iff, Ne.def, not_not] at hf 
      simp [Set.Preimage, hf]
    ·
      byCases' ha0 : a = 0
      ·
        subst a 
        rwa [zero_mul]
      ·
        exact mul_ne_top ha (fin_meas_supp_iff.1 hm _ ha0).Ne

theorem of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.fin_meas_supp μ :=
  by 
    refine' fin_meas_supp_iff.2 fun b hb => _ 
    rw [f.lintegral_eq_of_subset' (Finset.subset_insert b _)] at h 
    refine' Ennreal.lt_top_of_mul_ne_top_right _ hb 
    exact (lt_top_of_sum_ne_top h (Finset.mem_insert_self _ _)).Ne

theorem iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐa ∂μ, f a ≠ ∞) : f.fin_meas_supp μ ↔ f.lintegral μ < ∞ :=
  ⟨fun h => h.lintegral_lt_top hf, fun h => of_lintegral_ne_top h.ne⟩

end FinMeasSupp

end FinMeasSupp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_eliminator]
protected theorem induction {α γ} [MeasurableSpace α] [AddMonoidₓ γ] {P : simple_func α γ → Prop}
  (h_ind : ∀ c {s} hs : MeasurableSet s, P (simple_func.piecewise s hs (simple_func.const _ c) (simple_func.const _ 0)))
  (h_add : ∀ ⦃f g : simple_func α γ⦄, Disjoint (support f) (support g) → P f → P g → P (f+g)) (f : simple_func α γ) :
  P f :=
  by 
    generalize h : f.range \ {0} = s 
    rw [←Finset.coe_inj, Finset.coe_sdiff, Finset.coe_singleton, simple_func.coe_range] at h 
    revert s f h 
    refine' Finset.induction _ _
    ·
      intro f hf 
      rw [Finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf 
      convert h_ind 0 MeasurableSet.univ 
      ext x 
      simp [hf]
    ·
      intro x s hxs ih f hf 
      have mx := f.measurable_set_preimage {x}
      let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f 
      have Pg : P g
      ·
        apply ih 
        simp only [g, simple_func.coe_piecewise, range_piecewise]
        rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hf, Finset.coe_insert,
          insert_diff_self_of_not_mem, diff_eq_empty.mpr, Set.empty_union]
        ·
          rw [Set.image_subset_iff]
          convert Set.subset_univ _ 
          exact preimage_const_of_mem (mem_singleton _)
        ·
          rwa [Finset.mem_coe]
      convert h_add _ Pg (h_ind x mx)
      ·
        ext1 y 
        byCases' hy : y ∈ f ⁻¹' {x} <;> [simpa [hy], simp [hy]]
      rintro y 
      byCases' hy : y ∈ f ⁻¹' {x} <;> simp [hy]

end SimpleFunc

section Lintegral

open SimpleFunc

variable{m : MeasurableSpace α}{μ ν : Measureₓ α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
def lintegral {m : MeasurableSpace α} (μ : Measureₓ α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆(g : α →ₛ ℝ≥0∞)(hf : «expr⇑ » g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/


notation3  "∫⁻" (...) ", " r:(scoped f => f) " ∂" μ => lintegral μ r

notation3  "∫⁻" (...) ", " r:(scoped f => lintegral volume f) => r

notation3  "∫⁻" (...) " in " s ", " r:(scoped f => f) " ∂" μ => lintegral (measure.restrict μ s) r

notation3  "∫⁻" (...) " in " s ", " r:(scoped f => lintegral measure.restrict volume s f) => r

theorem simple_func.lintegral_eq_lintegral {m : MeasurableSpace α} (f : α →ₛ ℝ≥0∞) (μ : Measureₓ α) :
  (∫⁻a, f a ∂μ) = f.lintegral μ :=
  le_antisymmₓ (bsupr_le$ fun g hg => lintegral_mono hg$ le_reflₓ _)
    (le_supr_of_le f$ le_supr_of_le (le_reflₓ _) (le_reflₓ _))

@[mono]
theorem lintegral_mono' {m : MeasurableSpace α} ⦃μ ν : Measureₓ α⦄ (hμν : μ ≤ ν) ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  (∫⁻a, f a ∂μ) ≤ ∫⁻a, g a ∂ν :=
  supr_le_supr$ fun φ => supr_le_supr2$ fun hφ => ⟨le_transₓ hφ hfg, lintegral_mono (le_reflₓ φ) hμν⟩

theorem lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) : (∫⁻a, f a ∂μ) ≤ ∫⁻a, g a ∂μ :=
  lintegral_mono' (le_reflₓ μ) hfg

theorem lintegral_mono_nnreal {f g : α →  ℝ≥0 } (h : f ≤ g) : (∫⁻a, f a ∂μ) ≤ ∫⁻a, g a ∂μ :=
  by 
    refine' lintegral_mono _ 
    intro a 
    rw [Ennreal.coe_le_coe]
    exact h a

theorem lintegral_mono_set {m : MeasurableSpace α} ⦃μ : Measureₓ α⦄ {s t : Set α} {f : α → ℝ≥0∞} (hst : s ⊆ t) :
  (∫⁻x in s, f x ∂μ) ≤ ∫⁻x in t, f x ∂μ :=
  lintegral_mono' (measure.restrict_mono hst (le_reflₓ μ)) (le_reflₓ f)

theorem lintegral_mono_set' {m : MeasurableSpace α} ⦃μ : Measureₓ α⦄ {s t : Set α} {f : α → ℝ≥0∞} (hst : s ≤ᵐ[μ] t) :
  (∫⁻x in s, f x ∂μ) ≤ ∫⁻x in t, f x ∂μ :=
  lintegral_mono' (measure.restrict_mono' hst (le_reflₓ μ)) (le_reflₓ f)

theorem monotone_lintegral {m : MeasurableSpace α} (μ : Measureₓ α) : Monotone (lintegral μ) :=
  lintegral_mono

@[simp]
theorem lintegral_const (c : ℝ≥0∞) : (∫⁻a, c ∂μ) = c*μ univ :=
  by 
    rw [←simple_func.const_lintegral, ←simple_func.lintegral_eq_lintegral, simple_func.coe_const]

@[simp]
theorem lintegral_one : (∫⁻a, (1 : ℝ≥0∞) ∂μ) = μ univ :=
  by 
    rw [lintegral_const, one_mulₓ]

theorem set_lintegral_const (s : Set α) (c : ℝ≥0∞) : (∫⁻a in s, c ∂μ) = c*μ s :=
  by 
    rw [lintegral_const, measure.restrict_apply_univ]

theorem set_lintegral_one s : (∫⁻a in s, 1 ∂μ) = μ s :=
  by 
    rw [set_lintegral_const, one_mulₓ]

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
theorem lintegral_eq_nnreal {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ : Measureₓ α) :
  (∫⁻a, f a ∂μ) = ⨆(φ : α →ₛ  ℝ≥0 )(hf : ∀ x, «expr↑ » (φ x) ≤ f x), (φ.map (coeₓ :  ℝ≥0  → ℝ≥0∞)).lintegral μ :=
  by 
    refine' le_antisymmₓ (bsupr_le$ fun φ hφ => _) (supr_le_supr2$ fun φ => ⟨φ.map (coeₓ :  ℝ≥0  → ℝ≥0∞), le_reflₓ _⟩)
    byCases' h : ∀ᵐa ∂μ, φ a ≠ ∞
    ·
      let ψ := φ.map Ennreal.toNnreal 
      replace h : ψ.map (coeₓ :  ℝ≥0  → ℝ≥0∞) =ᵐ[μ] φ := h.mono fun a => Ennreal.coe_to_nnreal 
      have  : ∀ x, «expr↑ » (ψ x) ≤ f x := fun x => le_transₓ Ennreal.coe_to_nnreal_le_self (hφ x)
      exact le_supr_of_le (φ.map Ennreal.toNnreal) (le_supr_of_le this (ge_of_eq$ lintegral_congr h))
    ·
      have h_meas : μ (φ ⁻¹' {∞}) ≠ 0 
      exact mt measure_zero_iff_ae_nmem.1 h 
      refine' le_transₓ le_top (ge_of_eq$ (supr_eq_top _).2$ fun b hb => _)
      obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n*μ (φ ⁻¹' {∞})
      exact exists_nat_mul_gt h_meas (ne_of_ltₓ hb)
      use (const α (n :  ℝ≥0 )).restrict (φ ⁻¹' {∞})
      simp only [lt_supr_iff, exists_prop, coe_restrict, φ.measurable_set_preimage, coe_const, Ennreal.coe_indicator,
        map_coe_ennreal_restrict, map_const, Ennreal.coe_nat, restrict_const_lintegral]
      refine' ⟨indicator_le fun x hx => le_transₓ _ (hφ _), hn⟩
      simp only [mem_preimage, mem_singleton_iff] at hx 
      simp only [hx, le_top]

theorem exists_simple_func_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : (∫⁻x, f x ∂μ) ≠ ∞) {ε : ℝ≥0∞}
  (hε : ε ≠ 0) :
  ∃ φ : α →ₛ  ℝ≥0 ,
    (∀ x, «expr↑ » (φ x) ≤ f x) ∧ ∀ ψ : α →ₛ  ℝ≥0 , (∀ x, «expr↑ » (ψ x) ≤ f x) → (map coeₓ (ψ - φ)).lintegral μ < ε :=
  by 
    rw [lintegral_eq_nnreal] at h 
    have  := Ennreal.lt_add_right h hε 
    erw [Ennreal.bsupr_add] at this <;> [skip,
      exact
        ⟨0,
          fun x =>
            by 
              simp ⟩]
    simpRw [lt_supr_iff, supr_lt_iff, supr_le_iff]  at this 
    rcases this with ⟨φ, hle : ∀ x, «expr↑ » (φ x) ≤ f x, b, hbφ, hb⟩
    refine' ⟨φ, hle, fun ψ hψ => _⟩
    have  : (map coeₓ φ).lintegral μ ≠ ∞
    exact ne_top_of_le_ne_top h (le_bsupr φ hle)
    rw [←add_lt_add_iff_left this, ←add_lintegral, ←map_add @Ennreal.coe_add]
    refine' (hb _ fun x => le_transₓ _ (max_leₓ (hle x) (hψ x))).trans_lt hbφ 
    normCast 
    simp only [add_apply, sub_apply, add_tsub_eq_max]

theorem supr_lintegral_le {ι : Sort _} (f : ι → α → ℝ≥0∞) : (⨆i, ∫⁻a, f i a ∂μ) ≤ ∫⁻a, ⨆i, f i a ∂μ :=
  by 
    simp only [←supr_apply]
    exact (monotone_lintegral μ).le_map_supr

theorem supr2_lintegral_le {ι : Sort _} {ι' : ι → Sort _} (f : ∀ i, ι' i → α → ℝ≥0∞) :
  (⨆(i : _)(h : ι' i), ∫⁻a, f i h a ∂μ) ≤ ∫⁻a, ⨆(i : _)(h : ι' i), f i h a ∂μ :=
  by 
    convert (monotone_lintegral μ).le_map_supr2 f 
    ext1 a 
    simp only [supr_apply]

theorem le_infi_lintegral {ι : Sort _} (f : ι → α → ℝ≥0∞) : (∫⁻a, ⨅i, f i a ∂μ) ≤ ⨅i, ∫⁻a, f i a ∂μ :=
  by 
    simp only [←infi_apply]
    exact (monotone_lintegral μ).map_infi_le

theorem le_infi2_lintegral {ι : Sort _} {ι' : ι → Sort _} (f : ∀ i, ι' i → α → ℝ≥0∞) :
  (∫⁻a, ⨅(i : _)(h : ι' i), f i h a ∂μ) ≤ ⨅(i : _)(h : ι' i), ∫⁻a, f i h a ∂μ :=
  by 
    convert (monotone_lintegral μ).map_infi2_le f 
    ext1 a 
    simp only [infi_apply]

theorem lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐa ∂μ, f a ≤ g a) : (∫⁻a, f a ∂μ) ≤ ∫⁻a, g a ∂μ :=
  by 
    rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩
    have  : ∀ᵐx ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0 
    refine' supr_le$ fun s => supr_le$ fun hfs => le_supr_of_le (s.restrict («expr ᶜ» t))$ le_supr_of_le _ _
    ·
      intro a 
      byCases' a ∈ t <;> simp [h, restrict_apply, ht.compl]
      exact le_transₓ (hfs a) (by_contradiction$ fun hnfg => h (hts hnfg))
    ·
      refine' le_of_eqₓ (simple_func.lintegral_congr$ this.mono$ fun a hnt => _)
      byCases' hat : a ∈ t <;> simp [hat, ht.compl]
      exact (hnt hat).elim

theorem set_lintegral_mono_ae {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
  (hfg : ∀ᵐx ∂μ, x ∈ s → f x ≤ g x) : (∫⁻x in s, f x ∂μ) ≤ ∫⁻x in s, g x ∂μ :=
  lintegral_mono_ae$ (ae_restrict_iff$ measurable_set_le hf hg).2 hfg

theorem set_lintegral_mono {s : Set α} {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
  (hfg : ∀ x _ : x ∈ s, f x ≤ g x) : (∫⁻x in s, f x ∂μ) ≤ ∫⁻x in s, g x ∂μ :=
  set_lintegral_mono_ae hf hg (ae_of_all _ hfg)

theorem lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : (∫⁻a, f a ∂μ) = ∫⁻a, g a ∂μ :=
  le_antisymmₓ (lintegral_mono_ae$ h.le) (lintegral_mono_ae$ h.symm.le)

theorem lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) : (∫⁻a, f a ∂μ) = ∫⁻a, g a ∂μ :=
  by 
    simp only [h]

theorem set_lintegral_congr {f : α → ℝ≥0∞} {s t : Set α} (h : s =ᵐ[μ] t) : (∫⁻x in s, f x ∂μ) = ∫⁻x in t, f x ∂μ :=
  by 
    rw [restrict_congr_set h]

theorem set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : Set α} (hs : MeasurableSet s) (hfg : ∀ᵐx ∂μ, x ∈ s → f x = g x) :
  (∫⁻x in s, f x ∂μ) = ∫⁻x in s, g x ∂μ :=
  by 
    rw [lintegral_congr_ae]
    rw [eventually_eq]
    rwa [ae_restrict_iff' hs]

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
{f : exprℕ() → α → «exprℝ≥0∞»()}
(hf : ∀ n, measurable (f n))
(h_mono : monotone f) : «expr = »(«expr∫⁻ , ∂ »((a), «expr⨆ , »((n), f n a), μ), «expr⨆ , »((n), «expr∫⁻ , ∂ »((a), f n a, μ))) :=
begin
  set [] [ident c] [":", expr «exprℝ≥0»() → «exprℝ≥0∞»()] [":="] [expr coe] [],
  set [] [ident F] [] [":="] [expr λ a : α, «expr⨆ , »((n), f n a)] [],
  have [ident hF] [":", expr measurable F] [":=", expr measurable_supr hf],
  refine [expr le_antisymm _ (supr_lintegral_le _)],
  rw ["[", expr lintegral_eq_nnreal, "]"] [],
  refine [expr supr_le (assume s, supr_le (assume hsf, _))],
  refine [expr ennreal.le_of_forall_lt_one_mul_le (assume a ha, _)],
  rcases [expr ennreal.lt_iff_exists_coe.1 ha, "with", "⟨", ident r, ",", ident rfl, ",", ident ha, "⟩"],
  have [ident ha] [":", expr «expr < »(r, 1)] [":=", expr ennreal.coe_lt_coe.1 ha],
  let [ident rs] [] [":=", expr s.map (λ a, «expr * »(r, a))],
  have [ident eq_rs] [":", expr «expr = »(«expr * »((const α r : «expr →ₛ »(α, «exprℝ≥0∞»())), map c s), rs.map c)] [],
  { ext1 [] [ident a],
    exact [expr ennreal.coe_mul.symm] },
  have [ident eq] [":", expr ∀
   p, «expr = »(«expr ⁻¹' »(rs.map c, {p}), «expr⋃ , »((n), «expr ∩ »(«expr ⁻¹' »(rs.map c, {p}), {a | «expr ≤ »(p, f n a)})))] [],
  { assume [binders (p)],
    rw ["[", "<-", expr inter_Union, ",", "<-", expr inter_univ «expr ⁻¹' »(map c rs, {p}), "]"] [] { occs := occurrences.pos «expr[ , ]»([1]) },
    refine [expr set.ext (assume x, «expr $ »(and_congr_right, assume hx, (true_iff _).2 _))],
    by_cases [expr p_eq, ":", expr «expr = »(p, 0)],
    { simp [] [] [] ["[", expr p_eq, "]"] [] [] },
    simp [] [] [] [] [] ["at", ident hx],
    subst [expr hx],
    have [] [":", expr «expr ≠ »(«expr * »(r, s x), 0)] [],
    { rwa ["[", expr («expr ≠ »), ",", "<-", expr ennreal.coe_eq_zero, "]"] [] },
    have [] [":", expr «expr ≠ »(s x, 0)] [],
    { refine [expr mt _ this],
      assume [binders (h)],
      rw ["[", expr h, ",", expr mul_zero, "]"] [] },
    have [] [":", expr «expr < »(rs.map c x, «expr⨆ , »((n : exprℕ()), f n x))] [],
    { refine [expr lt_of_lt_of_le (ennreal.coe_lt_coe.2 _) (hsf x)],
      suffices [] [":", expr «expr < »(«expr * »(r, s x), «expr * »(1, s x))],
      simpa [] [] [] ["[", expr rs, "]"] [] [],
      exact [expr mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this)] },
    rcases [expr lt_supr_iff.1 this, "with", "⟨", ident i, ",", ident hi, "⟩"],
    exact [expr mem_Union.2 ⟨i, le_of_lt hi⟩] },
  have [ident mono] [":", expr ∀
   r : «exprℝ≥0∞»(), monotone (λ n, «expr ∩ »(«expr ⁻¹' »(rs.map c, {r}), {a | «expr ≤ »(r, f n a)}))] [],
  { assume [binders (r i j h)],
    refine [expr inter_subset_inter (subset.refl _) _],
    assume [binders (x hx)],
    exact [expr le_trans hx (h_mono h x)] },
  have [ident h_meas] [":", expr ∀
   n, measurable_set {a : α | «expr ≤ »(«expr⇑ »(map c rs) a, f n a)}] [":=", expr assume
   n, measurable_set_le (simple_func.measurable _) (hf n)],
  calc
    «expr = »(«expr * »((r : «exprℝ≥0∞»()), (s.map c).lintegral μ), «expr∑ in , »((r), (rs.map c).range, «expr * »(r, μ «expr ⁻¹' »(rs.map c, {r})))) : by rw ["[", "<-", expr const_mul_lintegral, ",", expr eq_rs, ",", expr simple_func.lintegral, "]"] []
    «expr ≤ »(..., «expr∑ in , »((r), (rs.map c).range, «expr * »(r, μ «expr⋃ , »((n), «expr ∩ »(«expr ⁻¹' »(rs.map c, {r}), {a | «expr ≤ »(r, f n a)}))))) : le_of_eq «expr $ »(finset.sum_congr rfl, assume
     x hx, by rw ["<-", expr eq] [])
    «expr ≤ »(..., «expr∑ in , »((r), (rs.map c).range, «expr⨆ , »((n), «expr * »(r, μ «expr ∩ »(«expr ⁻¹' »(rs.map c, {r}), {a | «expr ≤ »(r, f n a)}))))) : le_of_eq «expr $ »(finset.sum_congr rfl, assume
     x hx, begin
       rw ["[", expr measure_Union_eq_supr _ «expr $ »(directed_of_sup, mono x), ",", expr ennreal.mul_supr, "]"] [],
       { assume [binders (i)],
         refine [expr ((rs.map c).measurable_set_preimage _).inter _],
         exact [expr hf i measurable_set_Ici] }
     end)
    «expr ≤ »(..., «expr⨆ , »((n), «expr∑ in , »((r), (rs.map c).range, «expr * »(r, μ «expr ∩ »(«expr ⁻¹' »(rs.map c, {r}), {a | «expr ≤ »(r, f n a)}))))) : begin
      refine [expr le_of_eq _],
      rw ["[", expr ennreal.finset_sum_supr_nat, "]"] [],
      assume [binders (p i j h)],
      exact [expr mul_le_mul_left' «expr $ »(measure_mono, mono p h) _]
    end
    «expr ≤ »(..., «expr⨆ , »((n : exprℕ()), ((rs.map c).restrict {a | «expr ≤ »(rs.map c a, f n a)}).lintegral μ)) : begin
      refine [expr supr_le_supr (assume n, _)],
      rw ["[", expr restrict_lintegral _ (h_meas n), "]"] [],
      { refine [expr le_of_eq «expr $ »(finset.sum_congr rfl, assume r hr, _)],
        congr' [2] ["with", ident a],
        refine [expr and_congr_right _],
        simp [] [] [] [] [] [] { contextual := tt } }
    end
    «expr ≤ »(..., «expr⨆ , »((n), «expr∫⁻ , ∂ »((a), f n a, μ))) : begin
      refine [expr supr_le_supr (assume n, _)],
      rw ["[", "<-", expr simple_func.lintegral_eq_lintegral, "]"] [],
      refine [expr lintegral_mono (assume a, _)],
      simp [] [] ["only"] ["[", expr map_apply, "]"] [] ["at", ident h_meas],
      simp [] [] ["only"] ["[", expr coe_map, ",", expr restrict_apply _ (h_meas _), ",", expr («expr ∘ »), "]"] [] [],
      exact [expr indicator_apply_le id]
    end
end

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_supr' {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AeMeasurable (f n) μ) (h_mono : ∀ᵐx ∂μ, Monotone fun n => f n x) :
  (∫⁻a, ⨆n, f n a ∂μ) = ⨆n, ∫⁻a, f n a ∂μ :=
  by 
    simpRw [←supr_apply]
    let p : α → (ℕ → ℝ≥0∞) → Prop := fun x f' => Monotone f' 
    have hp : ∀ᵐx ∂μ, p x fun i => f i x 
    exact h_mono 
    have h_ae_seq_mono : Monotone (aeSeq hf p)
    ·
      intro n m hnm x 
      byCases' hx : x ∈ AeSeqSet hf p
      ·
        exact aeSeq.prop_of_mem_ae_seq_set hf hx hnm
      ·
        simp only [aeSeq, hx, if_false]
        exact le_reflₓ _ 
    rw [lintegral_congr_ae (aeSeq.supr hf hp).symm]
    simpRw [supr_apply]
    rw [@lintegral_supr _ _ μ _ (aeSeq.measurable hf p) h_ae_seq_mono]
    congr 
    exact funext fun n => lintegral_congr_ae (aeSeq.ae_seq_n_eq_fun_n_ae hf hp n)

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞} (hf : ∀ n, AeMeasurable (f n) μ)
  (h_mono : ∀ᵐx ∂μ, Monotone fun n => f n x) (h_tendsto : ∀ᵐx ∂μ, tendsto (fun n => f n x) at_top (𝓝$ F x)) :
  tendsto (fun n => ∫⁻x, f n x ∂μ) at_top (𝓝$ ∫⁻x, F x ∂μ) :=
  by 
    have  : Monotone fun n => ∫⁻x, f n x ∂μ := fun i j hij => lintegral_mono_ae (h_mono.mono$ fun x hx => hx hij)
    suffices key : (∫⁻x, F x ∂μ) = ⨆n, ∫⁻x, f n x ∂μ
    ·
      rw [key]
      exact tendsto_at_top_supr this 
    rw [←lintegral_supr' hf h_mono]
    refine' lintegral_congr_ae _ 
    filterUpwards [h_mono, h_tendsto]
    exact fun x hx_mono hx_tendsto => tendsto_nhds_unique hx_tendsto (tendsto_at_top_supr hx_mono)

theorem lintegral_eq_supr_eapprox_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) :
  (∫⁻a, f a ∂μ) = ⨆n, (eapprox f n).lintegral μ :=
  calc (∫⁻a, f a ∂μ) = ∫⁻a, ⨆n, (eapprox f n : α → ℝ≥0∞) a ∂μ :=
    by 
      congr <;> ext a <;> rw [supr_eapprox_apply f hf]
    _ = ⨆n, ∫⁻a, (eapprox f n : α → ℝ≥0∞) a ∂μ :=
    by 
      rw [lintegral_supr]
      ·
        measurability
      ·
        intro i j h 
        exact monotone_eapprox f h 
    _ = ⨆n, (eapprox f n).lintegral μ :=
    by 
      congr <;> ext n <;> rw [(eapprox f n).lintegral_eq_lintegral]
    

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
theorem exists_pos_set_lintegral_lt_of_measure_lt
{f : α → «exprℝ≥0∞»()}
(h : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»()))
{ε : «exprℝ≥0∞»()}
(hε : «expr ≠ »(ε, 0)) : «expr∃ , »((δ «expr > » 0), ∀
 s, «expr < »(μ s, δ) → «expr < »(«expr∫⁻ in , ∂ »((x), s, f x, μ), ε)) :=
begin
  rcases [expr exists_between hε.bot_lt, "with", "⟨", ident ε₂, ",", ident hε₂0, ":", expr «expr < »(0, ε₂), ",", ident hε₂ε, "⟩"],
  rcases [expr exists_between hε₂0, "with", "⟨", ident ε₁, ",", ident hε₁0, ",", ident hε₁₂, "⟩"],
  rcases [expr exists_simple_func_forall_lintegral_sub_lt_of_pos h hε₁0.ne', "with", "⟨", ident φ, ",", ident hle, ",", ident hφ, "⟩"],
  rcases [expr φ.exists_forall_le, "with", "⟨", ident C, ",", ident hC, "⟩"],
  use ["[", expr «expr / »(«expr - »(ε₂, ε₁), C), ",", expr ennreal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ennreal.coe_ne_top⟩, "]"],
  refine [expr λ s hs, lt_of_le_of_lt _ hε₂ε],
  simp [] [] ["only"] ["[", expr lintegral_eq_nnreal, ",", expr supr_le_iff, "]"] [] [],
  intros [ident ψ, ident hψ],
  calc
    «expr ≤ »((map coe ψ).lintegral (μ.restrict s), «expr + »((map coe φ).lintegral (μ.restrict s), (map coe «expr - »(ψ, φ)).lintegral (μ.restrict s))) : begin
      rw ["[", "<-", expr simple_func.add_lintegral, ",", "<-", expr simple_func.map_add @ennreal.coe_add, "]"] [],
      refine [expr simple_func.lintegral_mono (λ x, _) le_rfl],
      simp [] [] [] ["[", "-", ident ennreal.coe_add, ",", expr add_tsub_eq_max, ",", expr le_max_right, "]"] [] []
    end
    «expr ≤ »(..., «expr + »((map coe φ).lintegral (μ.restrict s), ε₁)) : begin
      refine [expr add_le_add le_rfl (le_trans _ (hφ _ hψ).le)],
      exact [expr simple_func.lintegral_mono le_rfl measure.restrict_le_self]
    end
    «expr ≤ »(..., «expr + »((simple_func.const α (C : «exprℝ≥0∞»())).lintegral (μ.restrict s), ε₁)) : by { mono ["*"] [] [] [],
      exacts ["[", expr λ x, coe_le_coe.2 (hC x), ",", expr le_rfl, ",", expr le_rfl, "]"] }
    «expr = »(..., «expr + »(«expr * »(C, μ s), ε₁)) : by simp [] [] [] ["[", "<-", expr simple_func.lintegral_eq_lintegral, "]"] [] []
    «expr ≤ »(..., «expr + »(«expr * »(C, «expr / »(«expr - »(ε₂, ε₁), C)), ε₁)) : by { mono ["*"] [] [] [],
      exacts ["[", expr le_rfl, ",", expr hs.le, ",", expr le_rfl, "]"] }
    «expr ≤ »(..., «expr + »(«expr - »(ε₂, ε₁), ε₁)) : add_le_add mul_div_le le_rfl
    «expr = »(..., ε₂) : tsub_add_cancel_of_le hε₁₂.le
end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
theorem tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : (∫⁻x, f x ∂μ) ≠ ∞) {l : Filter ι} {s : ι → Set α}
  (hl : tendsto (μ ∘ s) l (𝓝 0)) : tendsto (fun i => ∫⁻x in s i, f x ∂μ) l (𝓝 0) :=
  by 
    simp only [Ennreal.nhds_zero, tendsto_infi, tendsto_principal, mem_Iio, ←pos_iff_ne_zero] at hl⊢
    intro ε ε0 
    rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩
    exact (hl δ δ0).mono fun i => hδ _

@[simp]
theorem lintegral_add {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
  (∫⁻a, f a+g a ∂μ) = (∫⁻a, f a ∂μ)+∫⁻a, g a ∂μ :=
  calc (∫⁻a, f a+g a ∂μ) = ∫⁻a, (⨆n, (eapprox f n : α → ℝ≥0∞) a)+⨆n, (eapprox g n : α → ℝ≥0∞) a ∂μ :=
    by 
      simp only [supr_eapprox_apply, hf, hg]
    _ = ∫⁻a, ⨆n, (eapprox f n+eapprox g n : α → ℝ≥0∞) a ∂μ :=
    by 
      congr 
      funext a 
      rw [Ennreal.supr_add_supr_of_monotone]
      ·
        rfl
      ·
        intro i j h 
        exact monotone_eapprox _ h a
      ·
        intro i j h 
        exact monotone_eapprox _ h a 
    _ = ⨆n, (eapprox f n).lintegral μ+(eapprox g n).lintegral μ :=
    by 
      rw [lintegral_supr]
      ·
        congr 
        funext n 
        rw [←simple_func.add_lintegral, ←simple_func.lintegral_eq_lintegral]
        rfl
      ·
        measurability
      ·
        intro i j h a 
        exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _)
    _ = (⨆n, (eapprox f n).lintegral μ)+⨆n, (eapprox g n).lintegral μ :=
    by 
      refine' (Ennreal.supr_add_supr_of_monotone _ _).symm <;>
        ·
          intro i j h 
          exact simple_func.lintegral_mono (monotone_eapprox _ h) (le_reflₓ μ)
    _ = (∫⁻a, f a ∂μ)+∫⁻a, g a ∂μ :=
    by 
      rw [lintegral_eq_supr_eapprox_lintegral hf, lintegral_eq_supr_eapprox_lintegral hg]
    

theorem lintegral_add' {f g : α → ℝ≥0∞} (hf : AeMeasurable f μ) (hg : AeMeasurable g μ) :
  (∫⁻a, f a+g a ∂μ) = (∫⁻a, f a ∂μ)+∫⁻a, g a ∂μ :=
  calc (∫⁻a, f a+g a ∂μ) = ∫⁻a, hf.mk f a+hg.mk g a ∂μ := lintegral_congr_ae (eventually_eq.add hf.ae_eq_mk hg.ae_eq_mk)
    _ = (∫⁻a, hf.mk f a ∂μ)+∫⁻a, hg.mk g a ∂μ := lintegral_add hf.measurable_mk hg.measurable_mk 
    _ = (∫⁻a, f a ∂μ)+∫⁻a, g a ∂μ :=
    by 
      congr 1
      ·
        exact lintegral_congr_ae hf.ae_eq_mk.symm
      ·
        exact lintegral_congr_ae hg.ae_eq_mk.symm
    

theorem lintegral_zero : (∫⁻a : α, 0 ∂μ) = 0 :=
  by 
    simp 

theorem lintegral_zero_fun : (∫⁻a : α, (0 : α → ℝ≥0∞) a ∂μ) = 0 :=
  by 
    simp 

@[simp]
theorem lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) : (∫⁻a, f a ∂c • μ) = c*∫⁻a, f a ∂μ :=
  by 
    simp only [lintegral, supr_subtype', simple_func.lintegral_smul, Ennreal.mul_supr, smul_eq_mul]

@[simp]
theorem lintegral_sum_measure {m : MeasurableSpace α} {ι} (f : α → ℝ≥0∞) (μ : ι → Measureₓ α) :
  (∫⁻a, f a ∂measure.sum μ) = ∑'i, ∫⁻a, f a ∂μ i :=
  by 
    simp only [lintegral, supr_subtype', simple_func.lintegral_sum, Ennreal.tsum_eq_supr_sum]
    rw [supr_comm]
    congr 
    funext s 
    induction' s using Finset.induction_on with i s hi hs
    ·
      apply bot_unique 
      simp 
    simp only [Finset.sum_insert hi, ←hs]
    refine' (Ennreal.supr_add_supr _).symm 
    intro φ ψ 
    exact
      ⟨⟨φ⊔ψ, fun x => sup_le (φ.2 x) (ψ.2 x)⟩,
        add_le_add (simple_func.lintegral_mono le_sup_left (le_reflₓ _))
          (Finset.sum_le_sum$ fun j hj => simple_func.lintegral_mono le_sup_right (le_reflₓ _))⟩

@[simp]
theorem lintegral_add_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) (μ ν : Measureₓ α) :
  (∫⁻a, f a ∂μ+ν) = (∫⁻a, f a ∂μ)+∫⁻a, f a ∂ν :=
  by 
    simpa [tsum_fintype] using lintegral_sum_measure f fun b => cond b μ ν

@[simp]
theorem lintegral_zero_measure {m : MeasurableSpace α} (f : α → ℝ≥0∞) : (∫⁻a, f a ∂(0 : Measureₓ α)) = 0 :=
  bot_unique$
    by 
      simp [lintegral]

theorem set_lintegral_empty (f : α → ℝ≥0∞) : (∫⁻x in ∅, f x ∂μ) = 0 :=
  by 
    rw [measure.restrict_empty, lintegral_zero_measure]

theorem set_lintegral_univ (f : α → ℝ≥0∞) : (∫⁻x in univ, f x ∂μ) = ∫⁻x, f x ∂μ :=
  by 
    rw [measure.restrict_univ]

theorem set_lintegral_measure_zero (s : Set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) : (∫⁻x in s, f x ∂μ) = 0 :=
  by 
    convert lintegral_zero_measure _ 
    exact measure.restrict_eq_zero.2 hs'

theorem lintegral_finset_sum (s : Finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b _ : b ∈ s, Measurable (f b)) :
  (∫⁻a, ∑b in s, f b a ∂μ) = ∑b in s, ∫⁻a, f b a ∂μ :=
  by 
    induction' s using Finset.induction_on with a s has ih
    ·
      simp 
    ·
      simp only [Finset.sum_insert has]
      rw [Finset.forall_mem_insert] at hf 
      rw [lintegral_add hf.1 (s.measurable_sum hf.2), ih hf.2]

@[simp]
theorem lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻a, r*f a ∂μ) = r*∫⁻a, f a ∂μ :=
  calc (∫⁻a, r*f a ∂μ) = ∫⁻a, ⨆n, (const α r*eapprox f n) a ∂μ :=
    by 
      congr 
      funext a 
      rw [←supr_eapprox_apply f hf, Ennreal.mul_supr]
      rfl 
    _ = ⨆n, r*(eapprox f n).lintegral μ :=
    by 
      rw [lintegral_supr]
      ·
        congr 
        funext n 
        rw [←simple_func.const_mul_lintegral, ←simple_func.lintegral_eq_lintegral]
      ·
        intro n 
        exact simple_func.measurable _
      ·
        intro i j h a 
        exact mul_le_mul_left' (monotone_eapprox _ h _) _ 
    _ = r*∫⁻a, f a ∂μ :=
    by 
      rw [←Ennreal.mul_supr, lintegral_eq_supr_eapprox_lintegral hf]
    

theorem lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AeMeasurable f μ) : (∫⁻a, r*f a ∂μ) = r*∫⁻a, f a ∂μ :=
  by 
    have A : (∫⁻a, f a ∂μ) = ∫⁻a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk 
    have B : (∫⁻a, r*f a ∂μ) = ∫⁻a, r*hf.mk f a ∂μ := lintegral_congr_ae (eventually_eq.fun_comp hf.ae_eq_mk _)
    rw [A, B, lintegral_const_mul _ hf.measurable_mk]

theorem lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : (r*∫⁻a, f a ∂μ) ≤ ∫⁻a, r*f a ∂μ :=
  by 
    rw [lintegral, Ennreal.mul_supr]
    refine' supr_le fun s => _ 
    rw [Ennreal.mul_supr]
    simp only [supr_le_iff, ge_iff_le]
    intro hs 
    rw [←simple_func.const_mul_lintegral]
    refine' le_supr_of_le (const α r*s) (le_supr_of_le (fun x => _) (le_reflₓ _))
    exact mul_le_mul_left' (hs x) _

theorem lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) : (∫⁻a, r*f a ∂μ) = r*∫⁻a, f a ∂μ :=
  by 
    byCases' h : r = 0
    ·
      simp [h]
    apply le_antisymmₓ _ (lintegral_const_mul_le r f)
    have rinv : (r*r⁻¹) = 1 := Ennreal.mul_inv_cancel h hr 
    have rinv' : (r⁻¹*r) = 1
    ·
      ·
        rw [mul_commₓ]
        exact rinv 
    have  := lintegral_const_mul_le (r⁻¹) fun x => r*f x 
    simp [(mul_assocₓ _ _ _).symm, rinv'] at this 
    simpa [(mul_assocₓ _ _ _).symm, rinv] using mul_le_mul_left' this r

theorem lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻a, f a*r ∂μ) = (∫⁻a, f a ∂μ)*r :=
  by 
    simpRw [mul_commₓ, lintegral_const_mul r hf]

theorem lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : AeMeasurable f μ) : (∫⁻a, f a*r ∂μ) = (∫⁻a, f a ∂μ)*r :=
  by 
    simpRw [mul_commₓ, lintegral_const_mul'' r hf]

theorem lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) : ((∫⁻a, f a ∂μ)*r) ≤ ∫⁻a, f a*r ∂μ :=
  by 
    simpRw [mul_commₓ, lintegral_const_mul_le r f]

theorem lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) : (∫⁻a, f a*r ∂μ) = (∫⁻a, f a ∂μ)*r :=
  by 
    simpRw [mul_commₓ, lintegral_const_mul' r f hr]

theorem lintegral_lintegral_mul {β} [MeasurableSpace β] {ν : Measureₓ β} {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
  (hf : AeMeasurable f μ) (hg : AeMeasurable g ν) : (∫⁻x, ∫⁻y, f x*g y ∂ν ∂μ) = (∫⁻x, f x ∂μ)*∫⁻y, g y ∂ν :=
  by 
    simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

theorem lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) : (∫⁻a, g (f a) ∂μ) = ∫⁻a, g (f' a) ∂μ :=
  lintegral_congr_ae$
    h.mono$
      fun a h =>
        by 
          rw [h]

theorem lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁') (h₂ : f₂ =ᵐ[μ] f₂') (g : β → γ → ℝ≥0∞) :
  (∫⁻a, g (f₁ a) (f₂ a) ∂μ) = ∫⁻a, g (f₁' a) (f₂' a) ∂μ :=
  lintegral_congr_ae$
    h₁.mp$
      h₂.mono$
        fun _ h₂ h₁ =>
          by 
            rw [h₁, h₂]

@[simp]
theorem lintegral_indicator (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) :
  (∫⁻a, s.indicator f a ∂μ) = ∫⁻a in s, f a ∂μ :=
  by 
    simp only [lintegral, ←restrict_lintegral_eq_lintegral_restrict _ hs, supr_subtype']
    apply le_antisymmₓ <;> refine' supr_le_supr2 (Subtype.forall.2$ fun φ hφ => _)
    ·
      refine' ⟨⟨φ, le_transₓ hφ (indicator_le_self _ _)⟩, _⟩
      refine' simple_func.lintegral_mono (fun x => _) (le_reflₓ _)
      byCases' hx : x ∈ s
      ·
        simp [hx, hs, le_reflₓ]
      ·
        apply le_transₓ (hφ x)
        simp [hx, hs, le_reflₓ]
    ·
      refine' ⟨⟨φ.restrict s, fun x => _⟩, le_reflₓ _⟩
      simp [hφ x, hs, indicator_le_indicator]

theorem set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : Measurable f) (r : ℝ≥0∞) :
  (∫⁻x in { x | f x = r }, f x ∂μ) = r*μ { x | f x = r } :=
  by 
    have  : ∀ᵐx ∂μ, x ∈ { x | f x = r } → f x = r := ae_of_all μ fun _ hx => hx 
    erw [set_lintegral_congr_fun _ this, lintegral_const, measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact hf (measurable_set_singleton r)

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) : (ε*μ { x | ε ≤ f x }) ≤ ∫⁻a, f a ∂μ :=
  by 
    have  : MeasurableSet { a : α | ε ≤ f a }
    exact hf measurable_set_Ici 
    rw [←simple_func.restrict_const_lintegral _ this, ←simple_func.lintegral_eq_lintegral]
    refine' lintegral_mono fun a => _ 
    simp only [restrict_apply _ this]
    exact indicator_apply_le id

theorem lintegral_eq_top_of_measure_eq_top_pos {f : α → ℝ≥0∞} (hf : Measurable f) (hμf : 0 < μ { x | f x = ∞ }) :
  (∫⁻x, f x ∂μ) = ∞ :=
  eq_top_iff.mpr$
    calc ∞ = ∞*μ { x | ∞ ≤ f x } :=
      by 
        simp [mul_eq_top, hμf.ne.symm]
      _ ≤ ∫⁻x, f x ∂μ := mul_meas_ge_le_lintegral hf ∞
      

theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
  μ { x | ε ≤ f x } ≤ (∫⁻a, f a ∂μ) / ε :=
  (Ennreal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2$
    by 
      rw [mul_commₓ]
      exact mul_meas_ge_le_lintegral hf ε

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
@[simp]
theorem lintegral_eq_zero_iff
{f : α → «exprℝ≥0∞»()}
(hf : measurable f) : «expr ↔ »(«expr = »(«expr∫⁻ , ∂ »((a), f a, μ), 0), «expr =ᵐ[ ] »(f, μ, 0)) :=
begin
  refine [expr iff.intro (assume h, _) (assume h, _)],
  { have [] [":", expr ∀ n : exprℕ(), «expr∀ᵐ ∂ , »((a), μ, «expr < »(f a, «expr ⁻¹»(n)))] [],
    { assume [binders (n)],
      rw ["[", expr ae_iff, ",", "<-", expr nonpos_iff_eq_zero, ",", "<-", expr @ennreal.zero_div «expr ⁻¹»(n), ",", expr ennreal.le_div_iff_mul_le, ",", expr mul_comm, "]"] [],
      simp [] [] ["only"] ["[", expr not_lt, "]"] [] [],
      exacts ["[", expr «expr ▸ »(h, mul_meas_ge_le_lintegral hf «expr ⁻¹»(n)), ",", expr or.inl (ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top), ",", expr or.inr ennreal.zero_ne_top, "]"] },
    refine [expr (ae_all_iff.2 this).mono (λ a ha, _)],
    by_contradiction [ident h],
    rcases [expr ennreal.exists_inv_nat_lt h, "with", "⟨", ident n, ",", ident hn, "⟩"],
    exact [expr «expr $ »(lt_irrefl _, «expr $ »(lt_trans hn, ha n)).elim] },
  { calc
      «expr = »(«expr∫⁻ , ∂ »((a), f a, μ), «expr∫⁻ , ∂ »((a), 0, μ)) : lintegral_congr_ae h
      «expr = »(..., 0) : lintegral_zero }
end

@[simp]
theorem lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : AeMeasurable f μ) : (∫⁻a, f a ∂μ) = 0 ↔ f =ᵐ[μ] 0 :=
  by 
    have  : (∫⁻a, f a ∂μ) = ∫⁻a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk 
    rw [this, lintegral_eq_zero_iff hf.measurable_mk]
    exact ⟨fun H => hf.ae_eq_mk.trans H, fun H => hf.ae_eq_mk.symm.trans H⟩

theorem lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : Measurable f) : (0 < ∫⁻a, f a ∂μ) ↔ 0 < μ (Function.Support f) :=
  by 
    simp [pos_iff_ne_zero, hf, Filter.EventuallyEq, ae_iff, Function.Support]

/-- Weaker version of the monotone convergence theorem-/
theorem lintegral_supr_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (h_mono : ∀ n, ∀ᵐa ∂μ, f n a ≤ f n.succ a) :
  (∫⁻a, ⨆n, f n a ∂μ) = ⨆n, ∫⁻a, f n a ∂μ :=
  let ⟨s, hs⟩ := exists_measurable_superset_of_null (ae_iff.1 (ae_all_iff.2 h_mono))
  let g := fun n a => if a ∈ s then 0 else f n a 
  have g_eq_f : ∀ᵐa ∂μ, ∀ n, g n a = f n a := (measure_zero_iff_ae_nmem.1 hs.2.2).mono fun a ha n => if_neg ha 
  calc (∫⁻a, ⨆n, f n a ∂μ) = ∫⁻a, ⨆n, g n a ∂μ :=
    lintegral_congr_ae$
      g_eq_f.mono$
        fun a ha =>
          by 
            simp only [ha]
    _ = ⨆n, ∫⁻a, g n a ∂μ :=
    lintegral_supr (fun n => measurable_const.piecewise hs.2.1 (hf n))
      (monotone_nat_of_le_succ$
        fun n a =>
          Classical.by_cases
            (fun h : a ∈ s =>
              by 
                simp [g, if_pos h])
            fun h : a ∉ s =>
              by 
                simp only [g, if_neg h]
                have  := hs.1
                rw [subset_def] at this 
                have  := mt (this a) h 
                simp only [not_not, mem_set_of_eq] at this 
                exact this n)
    _ = ⨆n, ∫⁻a, f n a ∂μ :=
    by 
      simp only [lintegral_congr_ae (g_eq_f.mono$ fun a ha => ha _)]
    

theorem lintegral_sub {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hg_fin : (∫⁻a, g a ∂μ) ≠ ∞)
  (h_le : g ≤ᵐ[μ] f) : (∫⁻a, f a - g a ∂μ) = (∫⁻a, f a ∂μ) - ∫⁻a, g a ∂μ :=
  by 
    rw [←Ennreal.add_left_inj hg_fin, tsub_add_cancel_of_le (lintegral_mono_ae h_le), ←lintegral_add (hf.sub hg) hg]
    refine' lintegral_congr_ae (h_le.mono$ fun x hx => _)
    exact tsub_add_cancel_of_le hx

theorem lintegral_sub_le (f g : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (h : f ≤ᵐ[μ] g) :
  ((∫⁻x, g x ∂μ) - ∫⁻x, f x ∂μ) ≤ ∫⁻x, g x - f x ∂μ :=
  by 
    byCases' hfi : (∫⁻x, f x ∂μ) = ∞
    ·
      rw [hfi, Ennreal.sub_top]
      exact bot_le
    ·
      rw [lintegral_sub hg hf hfi h]
      rfl'

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on
{f g : α → «exprℝ≥0∞»()}
(hf : measurable f)
(hg : measurable g)
(hfi : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»()))
(h_le : «expr ≤ᵐ[ ] »(f, μ, g))
{s : set α}
(hμs : «expr ≠ »(μ s, 0))
(h : «expr∀ᵐ ∂ , »((x), μ, «expr ∈ »(x, s) → «expr < »(f x, g x))) : «expr < »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∫⁻ , ∂ »((x), g x, μ)) :=
begin
  rw ["[", "<-", expr tsub_pos_iff_lt, ",", "<-", expr lintegral_sub hg hf hfi h_le, "]"] [],
  by_contra [ident hnlt],
  rw ["[", expr not_lt, ",", expr nonpos_iff_eq_zero, ",", expr lintegral_eq_zero_iff (hg.sub hf), ",", expr filter.eventually_eq, "]"] ["at", ident hnlt],
  simp [] [] ["only"] ["[", expr ae_iff, ",", expr tsub_eq_zero_iff_le, ",", expr pi.zero_apply, ",", expr not_lt, ",", expr not_le, "]"] [] ["at", ident hnlt, ident h],
  refine [expr hμs _],
  push_neg ["at", ident h],
  have [ident hs_eq] [":", expr «expr = »(s, «expr ∪ »({a : α | «expr ∧ »(«expr ∈ »(a, s), «expr ≤ »(g a, f a))}, {a : α | «expr ∧ »(«expr ∈ »(a, s), «expr < »(f a, g a))}))] [],
  { ext1 [] [ident x],
    simp_rw ["[", expr set.mem_union, ",", expr set.mem_set_of_eq, ",", "<-", expr not_le, "]"] [],
    tauto [] },
  rw [expr hs_eq] [],
  refine [expr measure_union_null h (measure_mono_null _ hnlt)],
  simp [] [] [] [] [] []
end

theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hf : Measurable f) (hg : Measurable g)
  (hfi : (∫⁻x, f x ∂μ) ≠ ∞) (h : ∀ᵐx ∂μ, f x < g x) : (∫⁻x, f x ∂μ) < ∫⁻x, g x ∂μ :=
  by 
    rw [Ne.def, ←measure.measure_univ_eq_zero] at hμ 
    refine' lintegral_strict_mono_of_ae_le_of_ae_lt_on hf hg hfi (ae_le_of_ae_lt h) hμ _ 
    simpa using h

theorem set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s) (hs : μ s ≠ 0)
  (hf : Measurable f) (hg : Measurable g) (hfi : (∫⁻x in s, f x ∂μ) ≠ ∞) (h : ∀ᵐx ∂μ, x ∈ s → f x < g x) :
  (∫⁻x in s, f x ∂μ) < ∫⁻x in s, g x ∂μ :=
  lintegral_strict_mono
    (by 
      simp [hs])
    hf hg hfi ((ae_restrict_iff' hsm).mpr h)

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_infi_ae {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) (h_mono : ∀ n : ℕ, f n.succ ≤ᵐ[μ] f n)
  (h_fin : (∫⁻a, f 0 a ∂μ) ≠ ∞) : (∫⁻a, ⨅n, f n a ∂μ) = ⨅n, ∫⁻a, f n a ∂μ :=
  have fn_le_f0 : (∫⁻a, ⨅n, f n a ∂μ) ≤ ∫⁻a, f 0 a ∂μ := lintegral_mono fun a => infi_le_of_le 0 (le_reflₓ _)
  have fn_le_f0' : (⨅n, ∫⁻a, f n a ∂μ) ≤ ∫⁻a, f 0 a ∂μ := infi_le_of_le 0 (le_reflₓ _)
  (Ennreal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1$
    show ((∫⁻a, f 0 a ∂μ) - ∫⁻a, ⨅n, f n a ∂μ) = (∫⁻a, f 0 a ∂μ) - ⨅n, ∫⁻a, f n a ∂μ from
      calc ((∫⁻a, f 0 a ∂μ) - ∫⁻a, ⨅n, f n a ∂μ) = ∫⁻a, f 0 a - ⨅n, f n a ∂μ :=
        (lintegral_sub (h_meas 0) (measurable_infi h_meas)
            (ne_top_of_le_ne_top h_fin$ lintegral_mono fun a => infi_le _ _) (ae_of_all _$ fun a => infi_le _ _)).symm
          
        _ = ∫⁻a, ⨆n, f 0 a - f n a ∂μ := congr rfl (funext fun a => Ennreal.sub_infi)
        _ = ⨆n, ∫⁻a, f 0 a - f n a ∂μ :=
        lintegral_supr_ae (fun n => (h_meas 0).sub (h_meas n))
          fun n => (h_mono n).mono$ fun a ha => tsub_le_tsub (le_reflₓ _) ha 
        _ = ⨆n, (∫⁻a, f 0 a ∂μ) - ∫⁻a, f n a ∂μ :=
        have h_mono : ∀ᵐa ∂μ, ∀ n : ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono 
        have h_mono : ∀ n, ∀ᵐa ∂μ, f n a ≤ f 0 a :=
          fun n =>
            h_mono.mono$
              fun a h =>
                by 
                  induction' n with n ih
                  ·
                    exact le_reflₓ _
                  ·
                    exact le_transₓ (h n) ih 
        congr_argₓ supr$
          funext$
            fun n =>
              lintegral_sub (h_meas _) (h_meas _) (ne_top_of_le_ne_top h_fin$ lintegral_mono_ae$ h_mono n) (h_mono n)
        _ = (∫⁻a, f 0 a ∂μ) - ⨅n, ∫⁻a, f n a ∂μ := Ennreal.sub_infi.symm
        

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
theorem lintegral_infi {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) (h_anti : Antitone f)
  (h_fin : (∫⁻a, f 0 a ∂μ) ≠ ∞) : (∫⁻a, ⨅n, f n a ∂μ) = ⨅n, ∫⁻a, f n a ∂μ :=
  lintegral_infi_ae h_meas (fun n => ae_of_all _$ h_anti n.le_succ) h_fin

/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
theorem lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, AeMeasurable (f n) μ) :
  (∫⁻a, liminf at_top fun n => f n a ∂μ) ≤ liminf at_top fun n => ∫⁻a, f n a ∂μ :=
  calc (∫⁻a, liminf at_top fun n => f n a ∂μ) = ∫⁻a, ⨆n : ℕ, ⨅(i : _)(_ : i ≥ n), f i a ∂μ :=
    by 
      simp only [liminf_eq_supr_infi_of_nat]
    _ = ⨆n : ℕ, ∫⁻a, ⨅(i : _)(_ : i ≥ n), f i a ∂μ :=
    lintegral_supr' (fun n => ae_measurable_binfi _ (countable_encodable _) h_meas)
      (ae_of_all μ fun a n m hnm => infi_le_infi_of_subset$ fun i hi => le_transₓ hnm hi)
    _ ≤ ⨆n : ℕ, ⨅(i : _)(_ : i ≥ n), ∫⁻a, f i a ∂μ := supr_le_supr$ fun n => le_infi2_lintegral _ 
    _ = at_top.liminf fun n => ∫⁻a, f n a ∂μ := Filter.liminf_eq_supr_infi_of_nat.symm
    

/-- Known as Fatou's lemma -/
theorem lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀ n, Measurable (f n)) :
  (∫⁻a, liminf at_top fun n => f n a ∂μ) ≤ liminf at_top fun n => ∫⁻a, f n a ∂μ :=
  lintegral_liminf_le' fun n => (h_meas n).AeMeasurable

theorem limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞} (hf_meas : ∀ n, Measurable (f n))
  (h_bound : ∀ n, f n ≤ᵐ[μ] g) (h_fin : (∫⁻a, g a ∂μ) ≠ ∞) :
  (limsup at_top fun n => ∫⁻a, f n a ∂μ) ≤ ∫⁻a, limsup at_top fun n => f n a ∂μ :=
  calc (limsup at_top fun n => ∫⁻a, f n a ∂μ) = ⨅n : ℕ, ⨆(i : _)(_ : i ≥ n), ∫⁻a, f i a ∂μ :=
    limsup_eq_infi_supr_of_nat 
    _ ≤ ⨅n : ℕ, ∫⁻a, ⨆(i : _)(_ : i ≥ n), f i a ∂μ := infi_le_infi$ fun n => supr2_lintegral_le _ 
    _ = ∫⁻a, ⨅n : ℕ, ⨆(i : _)(_ : i ≥ n), f i a ∂μ :=
    by 
      refine' (lintegral_infi _ _ _).symm
      ·
        intro n 
        exact measurable_bsupr _ (countable_encodable _) hf_meas
      ·
        intro n m hnm a 
        exact supr_le_supr_of_subset$ fun i hi => le_transₓ hnm hi
      ·
        refine' ne_top_of_le_ne_top h_fin (lintegral_mono_ae _)
        refine' (ae_all_iff.2 h_bound).mono fun n hn => _ 
        exact supr_le fun i => supr_le$ fun hi => hn i 
    _ = ∫⁻a, limsup at_top fun n => f n a ∂μ :=
    by 
      simp only [limsup_eq_infi_supr_of_nat]
    

/-- Dominated convergence theorem for nonnegative functions -/
theorem tendsto_lintegral_of_dominated_convergence {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀ n, Measurable (F n)) (h_bound : ∀ n, F n ≤ᵐ[μ] bound) (h_fin : (∫⁻a, bound a ∂μ) ≠ ∞)
  (h_lim : ∀ᵐa ∂μ, tendsto (fun n => F n a) at_top (𝓝 (f a))) :
  tendsto (fun n => ∫⁻a, F n a ∂μ) at_top (𝓝 (∫⁻a, f a ∂μ)) :=
  tendsto_of_le_liminf_of_limsup_le
    (calc (∫⁻a, f a ∂μ) = ∫⁻a, liminf at_top fun n : ℕ => F n a ∂μ :=
      lintegral_congr_ae$ h_lim.mono$ fun a h => h.liminf_eq.symm 
      _ ≤ liminf at_top fun n => ∫⁻a, F n a ∂μ := lintegral_liminf_le hF_meas
      )
    (calc (limsup at_top fun n : ℕ => ∫⁻a, F n a ∂μ) ≤ ∫⁻a, limsup at_top fun n => F n a ∂μ :=
      limsup_lintegral_le hF_meas h_bound h_fin 
      _ = ∫⁻a, f a ∂μ := lintegral_congr_ae$ h_lim.mono$ fun a h => h.limsup_eq
      )

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
theorem tendsto_lintegral_of_dominated_convergence' {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀ n, AeMeasurable (F n) μ) (h_bound : ∀ n, F n ≤ᵐ[μ] bound) (h_fin : (∫⁻a, bound a ∂μ) ≠ ∞)
  (h_lim : ∀ᵐa ∂μ, tendsto (fun n => F n a) at_top (𝓝 (f a))) :
  tendsto (fun n => ∫⁻a, F n a ∂μ) at_top (𝓝 (∫⁻a, f a ∂μ)) :=
  by 
    have  : ∀ n, (∫⁻a, F n a ∂μ) = ∫⁻a, (hF_meas n).mk (F n) a ∂μ := fun n => lintegral_congr_ae (hF_meas n).ae_eq_mk 
    simpRw [this]
    apply tendsto_lintegral_of_dominated_convergence bound (fun n => (hF_meas n).measurable_mk) _ h_fin
    ·
      have  : ∀ n, ∀ᵐa ∂μ, (hF_meas n).mk (F n) a = F n a := fun n => (hF_meas n).ae_eq_mk.symm 
      have  : ∀ᵐa ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this 
      filterUpwards [this, h_lim]
      intro a H H' 
      simpRw [H]
      exact H'
    ·
      intro n 
      filterUpwards [h_bound n, (hF_meas n).ae_eq_mk]
      intro a H H' 
      rwa [H'] at H

/-- Dominated convergence theorem for filters with a countable basis -/
theorem tendsto_lintegral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.is_countably_generated]
  {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞) (hF_meas : ∀ᶠn in l, Measurable (F n))
  (h_bound : ∀ᶠn in l, ∀ᵐa ∂μ, F n a ≤ bound a) (h_fin : (∫⁻a, bound a ∂μ) ≠ ∞)
  (h_lim : ∀ᵐa ∂μ, tendsto (fun n => F n a) l (𝓝 (f a))) : tendsto (fun n => ∫⁻a, F n a ∂μ) l (𝓝$ ∫⁻a, f a ∂μ) :=
  by 
    rw [tendsto_iff_seq_tendsto]
    intro x xl 
    have hxl
    ·
      rw [tendsto_at_top'] at xl 
      exact xl 
    have h := inter_mem hF_meas h_bound 
    replace h := hxl _ h 
    rcases h with ⟨k, h⟩
    rw [←tendsto_add_at_top_iff_nat k]
    refine' tendsto_lintegral_of_dominated_convergence _ _ _ _ _
    ·
      exact bound
    ·
      intro 
      refine' (h _ _).1 
      exact Nat.le_add_leftₓ _ _
    ·
      intro 
      refine' (h _ _).2 
      exact Nat.le_add_leftₓ _ _
    ·
      assumption
    ·
      refine' h_lim.mono fun a h_lim => _ 
      apply @tendsto.comp _ _ _ (fun n => x (n+k)) fun n => F n a
      ·
        assumption 
      rw [tendsto_add_at_top_iff_nat]
      assumption

section 

open Encodable

/-- Monotone convergence for a suprema over a directed family and indexed by an encodable type -/
theorem lintegral_supr_directed [Encodable β] {f : β → α → ℝ≥0∞} (hf : ∀ b, Measurable (f b))
  (h_directed : Directed (· ≤ ·) f) : (∫⁻a, ⨆b, f b a ∂μ) = ⨆b, ∫⁻a, f b a ∂μ :=
  by 
    casesI is_empty_or_nonempty β
    ·
      simp [supr_of_empty]
    inhabit β 
    have  : ∀ a, (⨆b, f b a) = ⨆n, f (h_directed.sequence f n) a
    ·
      intro a 
      refine' le_antisymmₓ (supr_le$ fun b => _) (supr_le$ fun n => le_supr (fun n => f n a) _)
      exact le_supr_of_le (encode b+1) (h_directed.le_sequence b a)
    calc (∫⁻a, ⨆b, f b a ∂μ) = ∫⁻a, ⨆n, f (h_directed.sequence f n) a ∂μ :=
      by 
        simp only [this]_ = ⨆n, ∫⁻a, f (h_directed.sequence f n) a ∂μ :=
      lintegral_supr (fun n => hf _) h_directed.sequence_mono _ = ⨆b, ∫⁻a, f b a ∂μ :=
      by 
        refine' le_antisymmₓ (supr_le$ fun n => _) (supr_le$ fun b => _)
        ·
          exact le_supr (fun b => ∫⁻a, f b a ∂μ) _
        ·
          exact le_supr_of_le (encode b+1) (lintegral_mono$ h_directed.le_sequence b)

end 

theorem lintegral_tsum [Encodable β] {f : β → α → ℝ≥0∞} (hf : ∀ i, Measurable (f i)) :
  (∫⁻a, ∑'i, f i a ∂μ) = ∑'i, ∫⁻a, f i a ∂μ :=
  by 
    simp only [Ennreal.tsum_eq_supr_sum]
    rw [lintegral_supr_directed]
    ·
      simp [lintegral_finset_sum _ fun i _ => hf i]
    ·
      intro b 
      exact Finset.measurable_sum _ fun i _ => hf i
    ·
      intro s t 
      use s ∪ t 
      split 
      exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_left _ _)
      exact fun a => Finset.sum_le_sum_of_subset (Finset.subset_union_right _ _)

open Measureₓ

theorem lintegral_Union [Encodable β] {s : β → Set α} (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
  (f : α → ℝ≥0∞) : (∫⁻a in ⋃i, s i, f a ∂μ) = ∑'i, ∫⁻a in s i, f a ∂μ :=
  by 
    simp only [measure.restrict_Union hd hm, lintegral_sum_measure]

theorem lintegral_Union_le [Encodable β] (s : β → Set α) (f : α → ℝ≥0∞) :
  (∫⁻a in ⋃i, s i, f a ∂μ) ≤ ∑'i, ∫⁻a in s i, f a ∂μ :=
  by 
    rw [←lintegral_sum_measure]
    exact lintegral_mono' restrict_Union_le (le_reflₓ _)

theorem lintegral_union {f : α → ℝ≥0∞} {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
  (hAB : Disjoint A B) : (∫⁻a in A ∪ B, f a ∂μ) = (∫⁻a in A, f a ∂μ)+∫⁻a in B, f a ∂μ :=
  by 
    rw [Set.union_eq_Union, lintegral_Union, tsum_bool, add_commₓ]
    ·
      simp only [to_bool_false_eq_ff, to_bool_true_eq_tt, cond]
    ·
      intro i 
      exact MeasurableSet.cond hA hB
    ·
      rwa [pairwise_disjoint_on_bool]

theorem lintegral_add_compl (f : α → ℝ≥0∞) {A : Set α} (hA : MeasurableSet A) :
  ((∫⁻x in A, f x ∂μ)+∫⁻x in «expr ᶜ» A, f x ∂μ) = ∫⁻x, f x ∂μ :=
  by 
    rw [←lintegral_add_measure, measure.restrict_add_restrict_compl hA]

theorem lintegral_map [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
  (∫⁻a, f a ∂map g μ) = ∫⁻a, f (g a) ∂μ :=
  by 
    simp only [lintegral_eq_supr_eapprox_lintegral, hf, hf.comp hg]
    congr with n : 1
    convert simple_func.lintegral_map _ hg 
    ext1 x 
    simp only [eapprox_comp hf hg, coe_comp]

theorem lintegral_map' [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : AeMeasurable f (measure.map g μ))
  (hg : Measurable g) : (∫⁻a, f a ∂measure.map g μ) = ∫⁻a, f (g a) ∂μ :=
  calc (∫⁻a, f a ∂measure.map g μ) = ∫⁻a, hf.mk f a ∂measure.map g μ := lintegral_congr_ae hf.ae_eq_mk 
    _ = ∫⁻a, hf.mk f (g a) ∂μ := lintegral_map hf.measurable_mk hg 
    _ = ∫⁻a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)
    

theorem lintegral_comp [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f) (hg : Measurable g) :
  lintegral μ (f ∘ g) = ∫⁻a, f a ∂map g μ :=
  (lintegral_map hf hg).symm

theorem set_lintegral_map [MeasurableSpace β] {f : β → ℝ≥0∞} {g : α → β} {s : Set β} (hs : MeasurableSet s)
  (hf : Measurable f) (hg : Measurable g) : (∫⁻y in s, f y ∂map g μ) = ∫⁻x in g ⁻¹' s, f (g x) ∂μ :=
  by 
    rw [restrict_map hg hs, lintegral_map hf hg]

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` wich
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
theorem _root_.measurable_embedding.lintegral_map [MeasurableSpace β] {g : α → β} (hg : MeasurableEmbedding g)
  (f : β → ℝ≥0∞) : (∫⁻a, f a ∂map g μ) = ∫⁻a, f (g a) ∂μ :=
  by 
    refine' le_antisymmₓ (bsupr_le$ fun f₀ hf₀ => _) (bsupr_le$ fun f₀ hf₀ => _)
    ·
      rw [simple_func.lintegral_map _ hg.measurable, lintegral]
      have  : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ (f ∘ g)
      exact fun x => hf₀ (g x)
      exact le_supr_of_le (comp f₀ g hg.measurable) (le_supr _ this)
    ·
      rw [←f₀.extend_comp_eq hg (const _ 0), ←simple_func.lintegral_map, ←simple_func.lintegral_eq_lintegral]
      refine' lintegral_mono_ae (hg.ae_map_iff.2$ eventually_of_forall$ fun x => _)
      exact (extend_apply _ _ _ _).trans_le (hf₀ _)

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
theorem lintegral_map_equiv [MeasurableSpace β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) : (∫⁻a, f a ∂map g μ) = ∫⁻a, f (g a) ∂μ :=
  g.measurable_embedding.lintegral_map f

section DiracAndCount

variable[MeasurableSpace α]

theorem lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻a, f a ∂dirac a) = f a :=
  by 
    simp [lintegral_congr_ae (ae_eq_dirac' hf)]

theorem lintegral_dirac [MeasurableSingletonClass α] (a : α) (f : α → ℝ≥0∞) : (∫⁻a, f a ∂dirac a) = f a :=
  by 
    simp [lintegral_congr_ae (ae_eq_dirac f)]

theorem lintegral_encodable {α : Type _} {m : MeasurableSpace α} [Encodable α] [MeasurableSingletonClass α]
  (f : α → ℝ≥0∞) (μ : Measureₓ α) : (∫⁻a, f a ∂μ) = ∑'a, f a*μ {a} :=
  by 
    convLHS => rw [←sum_smul_dirac μ, lintegral_sum_measure]
    congr 1 with a : 1
    rw [lintegral_smul_measure, lintegral_dirac, mul_commₓ]

theorem lintegral_count' {f : α → ℝ≥0∞} (hf : Measurable f) : (∫⁻a, f a ∂count) = ∑'a, f a :=
  by 
    rw [count, lintegral_sum_measure]
    congr 
    exact funext fun a => lintegral_dirac' a hf

theorem lintegral_count [MeasurableSingletonClass α] (f : α → ℝ≥0∞) : (∫⁻a, f a ∂count) = ∑'a, f a :=
  by 
    rw [count, lintegral_sum_measure]
    congr 
    exact funext fun a => lintegral_dirac a f

end DiracAndCount

-- error in MeasureTheory.Integral.Lebesgue: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem ae_lt_top
{f : α → «exprℝ≥0∞»()}
(hf : measurable f)
(h2f : «expr ≠ »(«expr∫⁻ , ∂ »((x), f x, μ), «expr∞»())) : «expr∀ᵐ ∂ , »((x), μ, «expr < »(f x, «expr∞»())) :=
begin
  simp_rw ["[", expr ae_iff, ",", expr ennreal.not_lt_top, "]"] [],
  by_contra [ident h],
  apply [expr h2f.lt_top.not_le],
  have [] [":", expr «expr ≤ »(«expr ⁻¹' »(f, {«expr∞»()}).indicator «expr⊤»(), f)] [],
  { intro [ident x],
    by_cases [expr hx, ":", expr «expr ∈ »(x, «expr ⁻¹' »(f, {«expr∞»()}))]; [simpa [] [] [] ["[", expr hx, "]"] [] [], simp [] [] [] ["[", expr hx, "]"] [] []] },
  convert [] [expr lintegral_mono this] [],
  rw ["[", expr lintegral_indicator _ (hf (measurable_set_singleton «expr∞»())), "]"] [],
  simp [] [] [] ["[", expr ennreal.top_mul, ",", expr preimage, ",", expr h, "]"] [] []
end

theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AeMeasurable f μ) (h2f : (∫⁻x, f x ∂μ) ≠ ∞) : ∀ᵐx ∂μ, f x < ∞ :=
  by 
    have h2f_meas : (∫⁻x, hf.mk f x ∂μ) ≠ ∞
    ·
      rwa [←lintegral_congr_ae hf.ae_eq_mk]
    exact
      (ae_lt_top hf.measurable_mk h2f_meas).mp
        (hf.ae_eq_mk.mono
          fun x hx h =>
            by 
              rwa [hx])

theorem set_lintegral_lt_top_of_bdd_above {s : Set α} (hs : μ s ≠ ∞) {f : α →  ℝ≥0 } (hf : Measurable f)
  (hbdd : BddAbove (f '' s)) : (∫⁻x in s, f x ∂μ) < ∞ :=
  by 
    obtain ⟨M, hM⟩ := hbdd 
    rw [mem_upper_bounds] at hM 
    refine' lt_of_le_of_ltₓ (set_lintegral_mono hf.coe_nnreal_ennreal (@measurable_const _ _ _ _ («expr↑ » M)) _) _
    ·
      simpa using hM
    ·
      rw [lintegral_const]
      refine' Ennreal.mul_lt_top ennreal.coe_lt_top.ne _ 
      simp [hs]

theorem set_lintegral_lt_top_of_is_compact [TopologicalSpace α] [OpensMeasurableSpace α] {s : Set α} (hs : μ s ≠ ∞)
  (hsc : IsCompact s) {f : α →  ℝ≥0 } (hf : Continuous f) : (∫⁻x in s, f x ∂μ) < ∞ :=
  set_lintegral_lt_top_of_bdd_above hs hf.measurable (hsc.image hf).BddAbove

/-- Given a measure `μ : measure α` and a function `f : α → ℝ≥0∞`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def measure.with_density {m : MeasurableSpace α} (μ : Measureₓ α) (f : α → ℝ≥0∞) : Measureₓ α :=
  measure.of_measurable (fun s hs => ∫⁻a in s, f a ∂μ)
    (by 
      simp )
    fun s hs hd => lintegral_Union hs hd _

@[simp]
theorem with_density_apply (f : α → ℝ≥0∞) {s : Set α} (hs : MeasurableSet s) : μ.with_density f s = ∫⁻a in s, f a ∂μ :=
  measure.of_measurable_apply s hs

theorem with_density_add {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
  μ.with_density (f+g) = μ.with_density f+μ.with_density g :=
  by 
    refine' measure.ext fun s hs => _ 
    rw [with_density_apply _ hs, measure.coe_add, Pi.add_apply, with_density_apply _ hs, with_density_apply _ hs,
      ←lintegral_add hf hg]
    rfl

theorem with_density_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : Measurable f) :
  μ.with_density (r • f) = r • μ.with_density f :=
  by 
    refine' measure.ext fun s hs => _ 
    rw [with_density_apply _ hs, measure.coe_smul, Pi.smul_apply, with_density_apply _ hs, smul_eq_mul,
      ←lintegral_const_mul r hf]
    rfl

theorem with_density_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) : μ.with_density (r • f) = r • μ.with_density f :=
  by 
    refine' measure.ext fun s hs => _ 
    rw [with_density_apply _ hs, measure.coe_smul, Pi.smul_apply, with_density_apply _ hs, smul_eq_mul,
      ←lintegral_const_mul' r f hr]
    rfl

theorem is_finite_measure_with_density {f : α → ℝ≥0∞} (hf : (∫⁻a, f a ∂μ) ≠ ∞) : is_finite_measure (μ.with_density f) :=
  { measure_univ_lt_top :=
      by 
        rwa [with_density_apply _ MeasurableSet.univ, measure.restrict_univ, lt_top_iff_ne_top] }

theorem with_density_absolutely_continuous {m : MeasurableSpace α} (μ : Measureₓ α) (f : α → ℝ≥0∞) :
  μ.with_density f ≪ μ :=
  by 
    refine' absolutely_continuous.mk fun s hs₁ hs₂ => _ 
    rw [with_density_apply _ hs₁]
    exact set_lintegral_measure_zero _ _ hs₂

@[simp]
theorem with_density_zero : μ.with_density 0 = 0 :=
  by 
    ext1 s hs 
    simp [with_density_apply _ hs]

@[simp]
theorem with_density_one : μ.with_density 1 = μ :=
  by 
    ext1 s hs 
    simp [with_density_apply _ hs]

theorem with_density_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, Measurable (f i)) :
  μ.with_density (∑'n, f n) = Sum fun n => μ.with_density (f n) :=
  by 
    ext1 s hs 
    simpRw [sum_apply _ hs, with_density_apply _ hs]
    change (∫⁻x in s, (∑'n, f n) x ∂μ) = ∑'i : ℕ, ∫⁻x, f i x ∂μ.restrict s 
    rw [←lintegral_tsum h]
    refine' lintegral_congr fun x => tsum_apply (Pi.summable.2 fun _ => Ennreal.summable)

theorem with_density_indicator {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
  μ.with_density (s.indicator f) = (μ.restrict s).withDensity f :=
  by 
    ext1 t ht 
    rw [with_density_apply _ ht, lintegral_indicator _ hs, restrict_comm hs ht, ←with_density_apply _ ht]

theorem with_density_of_real_mutually_singular {f : α → ℝ} (hf : Measurable f) :
  (μ.with_density fun x => Ennreal.ofReal$ f x) ⊥ₘ μ.with_density fun x => Ennreal.ofReal$ -f x :=
  by 
    set S : Set α := { x | f x < 0 } with hSdef 
    have hS : MeasurableSet S := measurable_set_lt hf measurable_const 
    refine' ⟨S, hS, _, _⟩
    ·
      rw [with_density_apply _ hS, lintegral_eq_zero_iff hf.ennreal_of_real, eventually_eq]
      exact (ae_restrict_mem hS).mono fun x hx => Ennreal.of_real_eq_zero.2 (le_of_ltₓ hx)
    ·
      rw [with_density_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_of_real, eventually_eq]
      exact (ae_restrict_mem hS.compl).mono fun x hx => Ennreal.of_real_eq_zero.2 (not_ltₓ.1$ mt neg_pos.1 hx)

theorem restrict_with_density {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
  (μ.with_density f).restrict s = (μ.restrict s).withDensity f :=
  by 
    ext1 t ht 
    rw [restrict_apply ht, with_density_apply _ ht, with_density_apply _ (ht.inter hs), restrict_restrict ht]

theorem with_density_eq_zero {f : α → ℝ≥0∞} (hf : AeMeasurable f μ) (h : μ.with_density f = 0) : f =ᵐ[μ] 0 :=
  by 
    rw [←lintegral_eq_zero_iff' hf, ←set_lintegral_univ, ←with_density_apply _ MeasurableSet.univ, h, measure.coe_zero,
      Pi.zero_apply]

end Lintegral

end MeasureTheory

open MeasureTheory MeasureTheory.SimpleFunc

/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_eliminator]
theorem Measurable.ennreal_induction {α} [MeasurableSpace α] {P : (α → ℝ≥0∞) → Prop}
  (h_ind : ∀ c : ℝ≥0∞ ⦃s⦄, MeasurableSet s → P (indicator s fun _ => c))
  (h_add : ∀ ⦃f g : α → ℝ≥0∞⦄, Disjoint (support f) (support g) → Measurable f → Measurable g → P f → P g → P (f+g))
  (h_supr : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄ hf : ∀ n, Measurable (f n) h_mono : Monotone f hP : ∀ n, P (f n), P fun x => ⨆n, f n x)
  ⦃f : α → ℝ≥0∞⦄ (hf : Measurable f) : P f :=
  by 
    convert h_supr (fun n => (eapprox f n).Measurable) (monotone_eapprox f) _
    ·
      ext1 x 
      rw [supr_eapprox_apply f hf]
    ·
      exact
        fun n =>
          simple_func.induction (fun c s hs => h_ind c hs)
            (fun f g hfg hf hg => h_add hfg f.measurable g.measurable hf hg) (eapprox f n)

namespace MeasureTheory

variable{α : Type _}{m m0 : MeasurableSpace α}

include m

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
theorem lintegral_with_density_eq_lintegral_mul (μ : Measureₓ α) {f : α → ℝ≥0∞} (h_mf : Measurable f) :
  ∀ {g : α → ℝ≥0∞}, Measurable g → (∫⁻a, g a ∂μ.with_density f) = ∫⁻a, (f*g) a ∂μ :=
  by 
    apply Measurable.ennreal_induction
    ·
      intro c s h_ms 
      simp [mul_commₓ _ c, ←indicator_mul_right]
    ·
      intro g h h_univ h_mea_g h_mea_h h_ind_g h_ind_h 
      simp [mul_addₓ, Measurable.mul]
    ·
      intro g h_mea_g h_mono_g h_ind 
      have  : Monotone fun n a => f a*g n a := fun m n hmn x => Ennreal.mul_le_mul le_rfl (h_mono_g hmn x)
      simp [lintegral_supr, Ennreal.mul_supr, h_mf.mul (h_mea_g _)]

theorem with_density_mul (μ : Measureₓ α) {f g : α → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
  μ.with_density (f*g) = (μ.with_density f).withDensity g :=
  by 
    ext1 s hs 
    simp [with_density_apply _ hs, restrict_with_density hs, lintegral_with_density_eq_lintegral_mul _ hf hg]

theorem set_lintegral_with_density_eq_set_lintegral_mul (μ : Measureₓ α) {f g : α → ℝ≥0∞} (hf : Measurable f)
  (hg : Measurable g) {s : Set α} (hs : MeasurableSet s) : (∫⁻x in s, g x ∂μ.with_density f) = ∫⁻x in s, (f*g) x ∂μ :=
  by 
    rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul _ hf hg]

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigma_finite (μ : Measureₓ α) [sigma_finite μ] {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
  ∃ g : α →  ℝ≥0 , (∀ x, 0 < g x) ∧ Measurable g ∧ (∫⁻x, g x ∂μ) < ε :=
  by 
    set s : ℕ → Set α := disjointed (spanning_sets μ)
    have  : ∀ n, μ (s n) < ∞
    exact fun n => (measure_mono$ disjointed_subset _ _).trans_lt (measure_spanning_sets_lt_top μ n)
    obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ →  ℝ≥0 , (∀ i, 0 < δ i) ∧ (∑'i, μ (s i)*δ i) < ε 
    exact Ennreal.exists_pos_tsum_mul_lt_of_encodable ε0 _ fun n => (this n).Ne 
    set N : α → ℕ := spanning_sets_index μ 
    have hN_meas : Measurable N := measurable_spanning_sets_index μ 
    have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanning_sets_index_singleton μ 
    refine' ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, _⟩
    simpa [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas, hNs, lintegral_encodable,
      measurable_spanning_sets_index, mul_commₓ] using δsum

theorem lintegral_trim {μ : Measureₓ α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : @Measurable _ _ m _ f) :
  (∫⁻a, f a ∂μ.trim hm) = ∫⁻a, f a ∂μ :=
  by 
    refine' @Measurable.ennreal_induction α m (fun f => (∫⁻a, f a ∂μ.trim hm) = ∫⁻a, f a ∂μ) _ _ _ f hf
    ·
      intro c s hs 
      rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs), set_lintegral_const, set_lintegral_const]
      suffices h_trim_s : μ.trim hm s = μ s
      ·
        rw [h_trim_s]
      exact trim_measurable_set_eq hm hs
    ·
      intro f g hfg hf hg hf_prop hg_prop 
      have h_m := lintegral_add hf hg 
      have h_m0 := lintegral_add (Measurable.mono hf hm le_rfl) (Measurable.mono hg hm le_rfl)
      rwa [hf_prop, hg_prop, ←h_m0] at h_m
    ·
      intro f hf hf_mono hf_prop 
      rw [lintegral_supr hf hf_mono]
      rw [lintegral_supr (fun n => Measurable.mono (hf n) hm le_rfl) hf_mono]
      congr 
      exact funext fun n => hf_prop n

theorem lintegral_trim_ae {μ : Measureₓ α} (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : AeMeasurable f (μ.trim hm)) :
  (∫⁻a, f a ∂μ.trim hm) = ∫⁻a, f a ∂μ :=
  by 
    rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk), lintegral_congr_ae hf.ae_eq_mk,
      lintegral_trim hm hf.measurable_mk]

section SigmaFinite

variable{E : Type _}[NormedGroup E][MeasurableSpace E][OpensMeasurableSpace E]

theorem univ_le_of_forall_fin_meas_le {μ : Measureₓ α} (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)] (C : ℝ≥0∞)
  {f : Set α → ℝ≥0∞} (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → f s ≤ C)
  (h_F_lim : ∀ S : ℕ → Set α, (∀ n, measurable_set[m] (S n)) → Monotone S → f (⋃n, S n) ≤ ⨆n, f (S n)) : f univ ≤ C :=
  by 
    let S := @spanning_sets _ m (μ.trim hm) _ 
    have hS_mono : Monotone S 
    exact @monotone_spanning_sets _ m (μ.trim hm) _ 
    have hS_meas : ∀ n, measurable_set[m] (S n)
    exact @measurable_spanning_sets _ m (μ.trim hm) _ 
    rw [←@Union_spanning_sets _ m (μ.trim hm)]
    refine' (h_F_lim S hS_meas hS_mono).trans _ 
    refine' supr_le fun n => hf (S n) (hS_meas n) _ 
    exact ((le_trim hm).trans_lt (@measure_spanning_sets_lt_top _ m (μ.trim hm) _ n)).Ne

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `ae_measurable` version. -/
theorem lintegral_le_of_forall_fin_meas_le_of_measurable {μ : Measureₓ α} (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)]
  (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : Measurable f)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻x in s, f x ∂μ) ≤ C) : (∫⁻x, f x ∂μ) ≤ C :=
  by 
    have  : (∫⁻x in univ, f x ∂μ) = ∫⁻x, f x ∂μ
    ·
      simp only [measure.restrict_univ]
    rw [←this]
    refine' univ_le_of_forall_fin_meas_le hm C hf fun S hS_meas hS_mono => _ 
    rw [←lintegral_indicator]
    swap
    ·
      exact hm (⋃n, S n) (@MeasurableSet.Union _ _ m _ _ hS_meas)
    have h_integral_indicator : (⨆n, ∫⁻x in S n, f x ∂μ) = ⨆n, ∫⁻x, (S n).indicator f x ∂μ
    ·
      congr 
      ext1 n 
      rw [lintegral_indicator _ (hm _ (hS_meas n))]
    rw [h_integral_indicator, ←lintegral_supr]
    ·
      refine' le_of_eqₓ (lintegral_congr fun x => _)
      simpRw [indicator_apply]
      byCases' hx_mem : x ∈ Union S
      ·
        simp only [hx_mem, if_true]
        obtain ⟨n, hxn⟩ := mem_Union.mp hx_mem 
        refine' le_antisymmₓ (trans _ (le_supr _ n)) (supr_le fun i => _)
        ·
          simp only [hxn, le_reflₓ, if_true]
        ·
          byCases' hxi : x ∈ S i <;> simp [hxi]
      ·
        simp only [hx_mem, if_false]
        rw [mem_Union] at hx_mem 
        pushNeg  at hx_mem 
        refine' le_antisymmₓ (zero_le _) (supr_le fun n => _)
        simp only [hx_mem n, if_false, nonpos_iff_eq_zero]
    ·
      exact fun n => hf_meas.indicator (hm _ (hS_meas n))
    ·
      intro n₁ n₂ hn₁₂ a 
      simpRw [indicator_apply]
      splitIfs
      ·
        exact le_rfl
      ·
        exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1
      ·
        exact zero_le _
      ·
        exact le_rfl

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_le' {μ : Measureₓ α} (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)] (C : ℝ≥0∞)
  {f : _ → ℝ≥0∞} (hf_meas : AeMeasurable f μ) (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻x in s, f x ∂μ) ≤ C) :
  (∫⁻x, f x ∂μ) ≤ C :=
  by 
    let f' := hf_meas.mk f 
    have hf' : ∀ s, measurable_set[m] s → μ s ≠ ∞ → (∫⁻x in s, f' x ∂μ) ≤ C
    ·
      refine' fun s hs hμs => (le_of_eqₓ _).trans (hf s hs hμs)
      refine' lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono fun x hx => _))
      rw [hx]
    rw [lintegral_congr_ae hf_meas.ae_eq_mk]
    exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf'

omit m

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le [MeasurableSpace α] {μ : Measureₓ α} [sigma_finite μ] (C : ℝ≥0∞)
  {f : α → ℝ≥0∞} (hf_meas : AeMeasurable f μ) (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → (∫⁻x in s, f x ∂μ) ≤ C) :
  (∫⁻x, f x ∂μ) ≤ C :=
  @lintegral_le_of_forall_fin_meas_le' _ _ _ _ le_rfl
    (by 
      rwa [trim_eq_self])
    C _ hf_meas hf

/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
theorem exists_absolutely_continuous_is_finite_measure {m : MeasurableSpace α} (μ : Measureₓ α) [sigma_finite μ] :
  ∃ ν : Measureₓ α, is_finite_measure ν ∧ μ ≪ ν :=
  by 
    obtain ⟨g, gpos, gmeas, hg⟩ :
      ∃ g : α →  ℝ≥0 , (∀ x : α, 0 < g x) ∧ Measurable g ∧ (∫⁻x : α, «expr↑ » (g x) ∂μ) < 1 :=
      exists_pos_lintegral_lt_of_sigma_finite μ Ennreal.zero_lt_one.ne' 
    refine' ⟨μ.with_density fun x => g x, is_finite_measure_with_density hg.ne_top, _⟩
    have  : μ = (μ.with_density fun x => g x).withDensity fun x => g x⁻¹
    ·
      have A : ((fun x : α => (g x : ℝ≥0∞))*fun x : α => «expr↑ » (g x)⁻¹) = 1
      ·
        ext1 x 
        exact Ennreal.mul_inv_cancel (Ennreal.coe_ne_zero.2 (gpos x).ne') Ennreal.coe_ne_top 
      rw [←with_density_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A, with_density_one]
    convLHS => rw [this]
    exact with_density_absolutely_continuous _ _

end SigmaFinite

end MeasureTheory

