import Mathbin.MeasureTheory.Measure.MeasureSpace 
import Mathbin.Analysis.Complex.Basic

/-!

# Vector valued measures

This file defines vector valued measures, which are σ-additive functions from a set to a add monoid
`M` such that it maps the empty set and non-measurable sets to zero. In the case
that `M = ℝ`, we called the vector measure a signed measure and write `signed_measure α`.
Similarly, when `M = ℂ`, we call the measure a complex measure and write `complex_measure α`.

## Main definitions

* `measure_theory.vector_measure` is a vector valued, σ-additive function that maps the empty
  and non-measurable set to zero.
* `measure_theory.vector_measure.map` is the pushforward of a vector measure along a function.
* `measure_theory.vector_measure.restrict` is the restriction of a vector measure on some set.

## Notation

* `v ≤[i] w` means that the vector measure `v` restricted on the set `i` is less than or equal
  to the vector measure `w` restricted on `i`, i.e. `v.restrict i ≤ w.restrict i`.

## Implementation notes

We require all non-measurable sets to be mapped to zero in order for the extensionality lemma
to only compare the underlying functions for measurable sets.

We use `has_sum` instead of `tsum` in the definition of vector measures in comparison to `measure`
since this provides summablity.

## Tags

vector measure, signed measure, complex measure
-/


noncomputable theory

open_locale Classical BigOperators Nnreal Ennreal MeasureTheory

namespace MeasureTheory

variable{α β : Type _}{m : MeasurableSpace α}

/-- A vector measure on a measurable space `α` is a σ-additive `M`-valued function (for some `M`
an add monoid) such that the empty set and non-measurable sets are mapped to zero. -/
structure vector_measure(α : Type _)[MeasurableSpace α](M : Type _)[AddCommMonoidₓ M][TopologicalSpace M] where 
  measureOf' : Set α → M 
  empty' : measure_of' ∅ = 0
  not_measurable' ⦃i : Set α⦄ : ¬MeasurableSet i → measure_of' i = 0
  m_Union' ⦃f : ℕ → Set α⦄ :
  (∀ i, MeasurableSet (f i)) → Pairwise (Disjoint on f) → HasSum (fun i => measure_of' (f i)) (measure_of' (⋃i, f i))

/-- A `signed_measure` is a `ℝ`-vector measure. -/
abbrev signed_measure (α : Type _) [MeasurableSpace α] :=
  vector_measure α ℝ

/-- A `complex_measure` is a `ℂ`-vector_measure. -/
abbrev complex_measure (α : Type _) [MeasurableSpace α] :=
  vector_measure α ℂ

open Set MeasureTheory

namespace VectorMeasure

section 

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

include m

instance  : CoeFun (vector_measure α M) fun _ => Set α → M :=
  ⟨vector_measure.measure_of'⟩

initialize_simps_projections VectorMeasure (measureOf' → apply)

@[simp]
theorem measure_of_eq_coe (v : vector_measure α M) : v.measure_of' = v :=
  rfl

@[simp]
theorem Empty (v : vector_measure α M) : v ∅ = 0 :=
  v.empty'

theorem not_measurable (v : vector_measure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0 :=
  v.not_measurable' hi

theorem m_Union (v : vector_measure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
  (hf₂ : Pairwise (Disjoint on f)) : HasSum (fun i => v (f i)) (v (⋃i, f i)) :=
  v.m_Union' hf₁ hf₂

theorem of_disjoint_Union_nat [T2Space M] (v : vector_measure α M) {f : ℕ → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
  (hf₂ : Pairwise (Disjoint on f)) : v (⋃i, f i) = ∑'i, v (f i) :=
  (v.m_Union hf₁ hf₂).tsum_eq.symm

theorem coe_injective : @Function.Injective (vector_measure α M) (Set α → M) coeFn :=
  fun v w h =>
    by 
      cases v 
      cases w 
      congr

theorem ext_iff' (v w : vector_measure α M) : v = w ↔ ∀ (i : Set α), v i = w i :=
  by 
    rw [←coe_injective.eq_iff, Function.funext_iffₓ]

theorem ext_iff (v w : vector_measure α M) : v = w ↔ ∀ (i : Set α), MeasurableSet i → v i = w i :=
  by 
    split 
    ·
      rintro rfl _ _ 
      rfl
    ·
      rw [ext_iff']
      intro h i 
      byCases' hi : MeasurableSet i
      ·
        exact h i hi
      ·
        simpRw [not_measurable _ hi]

@[ext]
theorem ext {s t : vector_measure α M} (h : ∀ (i : Set α), MeasurableSet i → s i = t i) : s = t :=
  (ext_iff s t).2 h

variable[T2Space M]{v : vector_measure α M}{f : ℕ → Set α}

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_of_disjoint_Union
[encodable β]
{f : β → set α}
(hf₁ : ∀ i, measurable_set (f i))
(hf₂ : pairwise «expr on »(disjoint, f)) : has_sum (λ i, v (f i)) (v «expr⋃ , »((i), f i)) :=
begin
  set [] [ident g] [] [":="] [expr λ
   i : exprℕ(), «expr⋃ , »((b : β) (H : «expr ∈ »(b, encodable.decode₂ β i)), f b)] ["with", ident hg],
  have [ident hg₁] [":", expr ∀ i, measurable_set (g i)] [],
  { exact [expr λ _, measurable_set.Union (λ b, «expr $ »(measurable_set.Union_Prop, λ _, hf₁ b))] },
  have [ident hg₂] [":", expr pairwise «expr on »(disjoint, g)] [],
  { exact [expr encodable.Union_decode₂_disjoint_on hf₂] },
  have [] [] [":=", expr v.of_disjoint_Union_nat hg₁ hg₂],
  rw ["[", expr hg, ",", expr encodable.Union_decode₂, "]"] ["at", ident this],
  have [ident hg₃] [":", expr «expr = »(λ i : β, v (f i), λ i, v (g (encodable.encode i)))] [],
  { ext [] [] [],
    rw [expr hg] [],
    simp [] [] ["only"] [] [] [],
    congr,
    ext [] [ident y] [],
    simp [] [] ["only"] ["[", expr exists_prop, ",", expr mem_Union, ",", expr option.mem_def, "]"] [] [],
    split,
    { intro [ident hy],
      refine [expr ⟨x, (encodable.decode₂_is_partial_inv _ _).2 rfl, hy⟩] },
    { rintro ["⟨", ident b, ",", ident hb₁, ",", ident hb₂, "⟩"],
      rw [expr encodable.decode₂_is_partial_inv _ _] ["at", ident hb₁],
      rwa ["<-", expr encodable.encode_injective hb₁] [] } },
  rw ["[", expr summable.has_sum_iff, ",", expr this, ",", "<-", expr tsum_Union_decode₂, "]"] [],
  { exact [expr v.empty] },
  { rw [expr hg₃] [],
    change [expr summable «expr ∘ »(λ i, v (g i), encodable.encode)] [] [],
    rw [expr function.injective.summable_iff encodable.encode_injective] [],
    { exact [expr (v.m_Union hg₁ hg₂).summable] },
    { intros [ident x, ident hx],
      convert [] [expr v.empty] [],
      simp [] [] ["only"] ["[", expr Union_eq_empty, ",", expr option.mem_def, ",", expr not_exists, ",", expr mem_range, "]"] [] ["at", "⊢", ident hx],
      intros [ident i, ident hi],
      exact [expr false.elim (hx i ((encodable.decode₂_is_partial_inv _ _).1 hi))] } }
end

theorem of_disjoint_Union [Encodable β] {f : β → Set α} (hf₁ : ∀ i, MeasurableSet (f i))
  (hf₂ : Pairwise (Disjoint on f)) : v (⋃i, f i) = ∑'i, v (f i) :=
  (has_sum_of_disjoint_Union hf₁ hf₂).tsum_eq.symm

theorem of_union {A B : Set α} (h : Disjoint A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A ∪ B) = v A+v B :=
  by 
    rw [union_eq_Union, of_disjoint_Union, tsum_fintype, Fintype.sum_bool, cond, cond]
    exacts[fun b => Bool.casesOn b hB hA, pairwise_disjoint_on_bool.2 h]

theorem of_add_of_diff {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) :
  (v A+v (B \ A)) = v B :=
  by 
    rw [←of_union disjoint_diff hA (hB.diff hA), union_diff_cancel h]
    infer_instance

theorem of_diff {M : Type _} [AddCommGroupₓ M] [TopologicalSpace M] [T2Space M] {v : vector_measure α M} {A B : Set α}
  (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A ⊆ B) : v (B \ A) = v B - v A :=
  by 
    rw [←of_add_of_diff hA hB h, add_sub_cancel']
    infer_instance

theorem of_diff_of_diff_eq_zero {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h' : v (B \ A) = 0) :
  (v (A \ B)+v B) = v A :=
  by 
    symm 
    calc v A = v (A \ B ∪ A ∩ B) :=
      by 
        simp only [Set.diff_union_inter]_ = v (A \ B)+v (A ∩ B) :=
      by 
        rw [of_union]
        ·
          rw [Disjoint.comm]
          exact Set.disjoint_of_subset_left (A.inter_subset_right B) Set.disjoint_diff
        ·
          exact hA.diff hB
        ·
          exact hA.inter hB _ = v (A \ B)+v (A ∩ B ∪ B \ A) :=
      by 
        rw [of_union, h', add_zeroₓ]
        ·
          exact Set.disjoint_of_subset_left (A.inter_subset_left B) Set.disjoint_diff
        ·
          exact hA.inter hB
        ·
          exact hB.diff hA _ = v (A \ B)+v B :=
      by 
        rw [Set.union_comm, Set.inter_comm, Set.diff_union_inter]

theorem of_Union_nonneg {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M] [OrderClosedTopology M]
  {v : vector_measure α M} (hf₁ : ∀ i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, 0 ≤ v (f i)) :
  0 ≤ v (⋃i, f i) :=
  (v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonneg hf₃

theorem of_Union_nonpos {M : Type _} [TopologicalSpace M] [OrderedAddCommMonoid M] [OrderClosedTopology M]
  {v : vector_measure α M} (hf₁ : ∀ i, MeasurableSet (f i)) (hf₂ : Pairwise (Disjoint on f)) (hf₃ : ∀ i, v (f i) ≤ 0) :
  v (⋃i, f i) ≤ 0 :=
  (v.of_disjoint_Union_nat hf₁ hf₂).symm ▸ tsum_nonpos hf₃

theorem of_nonneg_disjoint_union_eq_zero {s : signed_measure α} {A B : Set α} (h : Disjoint A B) (hA₁ : MeasurableSet A)
  (hB₁ : MeasurableSet B) (hA₂ : 0 ≤ s A) (hB₂ : 0 ≤ s B) (hAB : s (A ∪ B) = 0) : s A = 0 :=
  by 
    rw [of_union h hA₁ hB₁] at hAB 
    linarith 
    infer_instance

theorem of_nonpos_disjoint_union_eq_zero {s : signed_measure α} {A B : Set α} (h : Disjoint A B) (hA₁ : MeasurableSet A)
  (hB₁ : MeasurableSet B) (hA₂ : s A ≤ 0) (hB₂ : s B ≤ 0) (hAB : s (A ∪ B) = 0) : s A = 0 :=
  by 
    rw [of_union h hA₁ hB₁] at hAB 
    linarith 
    infer_instance

end 

section AddCommMonoidₓ

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

include m

instance  : HasZero (vector_measure α M) :=
  ⟨⟨0, rfl, fun _ _ => rfl, fun _ _ _ => has_sum_zero⟩⟩

instance  : Inhabited (vector_measure α M) :=
  ⟨0⟩

@[simp]
theorem coe_zero : «expr⇑ » (0 : vector_measure α M) = 0 :=
  rfl

theorem zero_apply (i : Set α) : (0 : vector_measure α M) i = 0 :=
  rfl

variable[HasContinuousAdd M]

/-- The sum of two vector measure is a vector measure. -/
def add (v w : vector_measure α M) : vector_measure α M :=
  { measureOf' := v+w,
    empty' :=
      by 
        simp ,
    not_measurable' :=
      fun _ hi =>
        by 
          simp [v.not_measurable hi, w.not_measurable hi],
    m_Union' := fun f hf₁ hf₂ => HasSum.add (v.m_Union hf₁ hf₂) (w.m_Union hf₁ hf₂) }

instance  : Add (vector_measure α M) :=
  ⟨add⟩

@[simp]
theorem coe_add (v w : vector_measure α M) : «expr⇑ » (v+w) = v+w :=
  rfl

theorem add_apply (v w : vector_measure α M) (i : Set α) : (v+w) i = v i+w i :=
  rfl

instance  : AddCommMonoidₓ (vector_measure α M) :=
  Function.Injective.addCommMonoid _ coe_injective coe_zero coe_add

/-- `coe_fn` is an `add_monoid_hom`. -/
@[simps]
def coe_fn_add_monoid_hom : vector_measure α M →+ Set α → M :=
  { toFun := coeFn, map_zero' := coe_zero, map_add' := coe_add }

end AddCommMonoidₓ

section AddCommGroupₓ

variable{M : Type _}[AddCommGroupₓ M][TopologicalSpace M][TopologicalAddGroup M]

include m

/-- The negative of a vector measure is a vector measure. -/
def neg (v : vector_measure α M) : vector_measure α M :=
  { measureOf' := -v,
    empty' :=
      by 
        simp ,
    not_measurable' :=
      fun _ hi =>
        by 
          simp [v.not_measurable hi],
    m_Union' := fun f hf₁ hf₂ => HasSum.neg$ v.m_Union hf₁ hf₂ }

instance  : Neg (vector_measure α M) :=
  ⟨neg⟩

@[simp]
theorem coe_neg (v : vector_measure α M) : «expr⇑ » (-v) = -v :=
  rfl

theorem neg_apply (v : vector_measure α M) (i : Set α) : (-v) i = -v i :=
  rfl

/-- The difference of two vector measure is a vector measure. -/
def sub (v w : vector_measure α M) : vector_measure α M :=
  { measureOf' := v - w,
    empty' :=
      by 
        simp ,
    not_measurable' :=
      fun _ hi =>
        by 
          simp [v.not_measurable hi, w.not_measurable hi],
    m_Union' := fun f hf₁ hf₂ => HasSum.sub (v.m_Union hf₁ hf₂) (w.m_Union hf₁ hf₂) }

instance  : Sub (vector_measure α M) :=
  ⟨sub⟩

@[simp]
theorem coe_sub (v w : vector_measure α M) : «expr⇑ » (v - w) = v - w :=
  rfl

theorem sub_apply (v w : vector_measure α M) (i : Set α) : (v - w) i = v i - w i :=
  rfl

instance  : AddCommGroupₓ (vector_measure α M) :=
  Function.Injective.addCommGroup _ coe_injective coe_zero coe_add coe_neg coe_sub

end AddCommGroupₓ

section DistribMulAction

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

variable{R : Type _}[Semiringₓ R][DistribMulAction R M]

variable[TopologicalSpace R][HasContinuousSmul R M]

include m

/-- Given a real number `r` and a signed measure `s`, `smul r s` is the signed
measure corresponding to the function `r • s`. -/
def smul (r : R) (v : vector_measure α M) : vector_measure α M :=
  { measureOf' := r • v,
    empty' :=
      by 
        rw [Pi.smul_apply, Empty, smul_zero],
    not_measurable' :=
      fun _ hi =>
        by 
          rw [Pi.smul_apply, v.not_measurable hi, smul_zero],
    m_Union' := fun _ hf₁ hf₂ => HasSum.const_smul (v.m_Union hf₁ hf₂) }

instance  : HasScalar R (vector_measure α M) :=
  ⟨smul⟩

@[simp]
theorem coe_smul (r : R) (v : vector_measure α M) : «expr⇑ » (r • v) = r • v :=
  rfl

theorem smul_apply (r : R) (v : vector_measure α M) (i : Set α) : (r • v) i = r • v i :=
  rfl

instance  [HasContinuousAdd M] : DistribMulAction R (vector_measure α M) :=
  Function.Injective.distribMulAction coe_fn_add_monoid_hom coe_injective coe_smul

end DistribMulAction

section Module

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

variable{R : Type _}[Semiringₓ R][Module R M]

variable[TopologicalSpace R][HasContinuousSmul R M]

include m

instance  [HasContinuousAdd M] : Module R (vector_measure α M) :=
  Function.Injective.module R coe_fn_add_monoid_hom coe_injective coe_smul

end Module

end VectorMeasure

namespace Measureₓ

include m

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A finite measure coerced into a real function is a signed measure. -/
@[simps #[]]
def to_signed_measure (μ : measure α) [hμ : is_finite_measure μ] : signed_measure α :=
{ measure_of' := λ i : set α, if measurable_set i then (μ.measure_of i).to_real else 0,
  empty' := by simp [] [] [] ["[", expr μ.empty, "]"] [] [],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' := begin
    intros ["_", ident hf₁, ident hf₂],
    rw ["[", expr μ.m_Union hf₁ hf₂, ",", expr ennreal.tsum_to_real_eq, ",", expr if_pos (measurable_set.Union hf₁), ",", expr summable.has_sum_iff, "]"] [],
    { congr,
      ext [] [ident n] [],
      rw [expr if_pos (hf₁ n)] [] },
    { refine [expr @summable_of_nonneg_of_le _ «expr ∘ »(ennreal.to_real, «expr ∘ »(μ, f)) _ _ _ _],
      { intro [],
        split_ifs [] [],
        exacts ["[", expr ennreal.to_real_nonneg, ",", expr le_refl _, "]"] },
      { intro [],
        split_ifs [] [],
        exacts ["[", expr le_refl _, ",", expr ennreal.to_real_nonneg, "]"] },
      exact [expr summable_measure_to_real hf₁ hf₂] },
    { intros [ident a, ident ha],
      apply [expr ne_of_lt hμ.measure_univ_lt_top],
      rw ["[", expr eq_top_iff, ",", "<-", expr ha, ",", expr outer_measure.measure_of_eq_coe, ",", expr coe_to_outer_measure, "]"] [],
      exact [expr measure_mono (set.subset_univ _)] }
  end }

theorem to_signed_measure_apply_measurable {μ : Measureₓ α} [is_finite_measure μ] {i : Set α} (hi : MeasurableSet i) :
  μ.to_signed_measure i = (μ i).toReal :=
  if_pos hi

theorem to_signed_measure_congr {μ ν : Measureₓ α} [is_finite_measure μ] [is_finite_measure ν] (h : μ = ν) :
  μ.to_signed_measure = ν.to_signed_measure :=
  by 
    congr 
    exact h

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem to_signed_measure_eq_to_signed_measure_iff
{μ ν : measure α}
[is_finite_measure μ]
[is_finite_measure ν] : «expr ↔ »(«expr = »(μ.to_signed_measure, ν.to_signed_measure), «expr = »(μ, ν)) :=
begin
  refine [expr ⟨λ h, _, λ h, _⟩],
  { ext1 [] [ident i, ident hi],
    have [] [":", expr «expr = »(μ.to_signed_measure i, ν.to_signed_measure i)] [],
    { rw [expr h] [] },
    rwa ["[", expr to_signed_measure_apply_measurable hi, ",", expr to_signed_measure_apply_measurable hi, ",", expr ennreal.to_real_eq_to_real, "]"] ["at", ident this]; { exact [expr measure_ne_top _ _] } },
  { congr,
    assumption }
end

@[simp]
theorem to_signed_measure_zero : (0 : Measureₓ α).toSignedMeasure = 0 :=
  by 
    ext i hi 
    simp 

@[simp]
theorem to_signed_measure_add (μ ν : Measureₓ α) [is_finite_measure μ] [is_finite_measure ν] :
  (μ+ν).toSignedMeasure = μ.to_signed_measure+ν.to_signed_measure :=
  by 
    ext i hi 
    rw [to_signed_measure_apply_measurable hi, add_apply,
      Ennreal.to_real_add (ne_of_ltₓ (measure_lt_top _ _)) (ne_of_ltₓ (measure_lt_top _ _)), vector_measure.add_apply,
      to_signed_measure_apply_measurable hi, to_signed_measure_apply_measurable hi]
    all_goals 
      infer_instance

@[simp]
theorem to_signed_measure_smul (μ : Measureₓ α) [is_finite_measure μ] (r :  ℝ≥0 ) :
  (r • μ).toSignedMeasure = r • μ.to_signed_measure :=
  by 
    ext i hi 
    rw [to_signed_measure_apply_measurable hi, vector_measure.smul_apply, to_signed_measure_apply_measurable hi,
      coe_nnreal_smul, Pi.smul_apply, Ennreal.to_real_smul]

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- A measure is a vector measure over `ℝ≥0∞`. -/
@[simps #[]]
def to_ennreal_vector_measure (μ : measure α) : vector_measure α «exprℝ≥0∞»() :=
{ measure_of' := λ i : set α, if measurable_set i then μ i else 0,
  empty' := by simp [] [] [] ["[", expr μ.empty, "]"] [] [],
  not_measurable' := λ _ hi, if_neg hi,
  m_Union' := λ _ hf₁ hf₂, begin
    rw [expr summable.has_sum_iff ennreal.summable] [],
    { rw ["[", expr if_pos (measurable_set.Union hf₁), ",", expr measure_theory.measure_Union hf₂ hf₁, "]"] [],
      exact [expr tsum_congr (λ n, if_pos (hf₁ n))] }
  end }

theorem to_ennreal_vector_measure_apply_measurable {μ : Measureₓ α} {i : Set α} (hi : MeasurableSet i) :
  μ.to_ennreal_vector_measure i = μ i :=
  if_pos hi

@[simp]
theorem to_ennreal_vector_measure_zero : (0 : Measureₓ α).toEnnrealVectorMeasure = 0 :=
  by 
    ext i hi 
    simp 

@[simp]
theorem to_ennreal_vector_measure_add (μ ν : Measureₓ α) :
  (μ+ν).toEnnrealVectorMeasure = μ.to_ennreal_vector_measure+ν.to_ennreal_vector_measure :=
  by 
    refine' MeasureTheory.VectorMeasure.ext fun i hi => _ 
    rw [to_ennreal_vector_measure_apply_measurable hi, add_apply, vector_measure.add_apply,
      to_ennreal_vector_measure_apply_measurable hi, to_ennreal_vector_measure_apply_measurable hi]

theorem to_signed_measure_sub_apply {μ ν : Measureₓ α} [is_finite_measure μ] [is_finite_measure ν] {i : Set α}
  (hi : MeasurableSet i) : (μ.to_signed_measure - ν.to_signed_measure) i = (μ i).toReal - (ν i).toReal :=
  by 
    rw [vector_measure.sub_apply, to_signed_measure_apply_measurable hi, measure.to_signed_measure_apply_measurable hi,
      sub_eq_add_neg]

end Measureₓ

namespace VectorMeasure

open Measureₓ

section 

/-- A vector measure over `ℝ≥0∞` is a measure. -/
def ennreal_to_measure {m : MeasurableSpace α} (v : vector_measure α ℝ≥0∞) : Measureₓ α :=
  of_measurable (fun s _ => v s) v.empty fun f hf₁ hf₂ => v.of_disjoint_Union_nat hf₁ hf₂

theorem ennreal_to_measure_apply {m : MeasurableSpace α} {v : vector_measure α ℝ≥0∞} {s : Set α}
  (hs : MeasurableSet s) : ennreal_to_measure v s = v s :=
  by 
    rw [ennreal_to_measure, of_measurable_apply _ hs]

/-- The equiv between `vector_measure α ℝ≥0∞` and `measure α` formed by
`measure_theory.vector_measure.ennreal_to_measure` and
`measure_theory.measure.to_ennreal_vector_measure`. -/
@[simps]
def equiv_measure [MeasurableSpace α] : vector_measure α ℝ≥0∞ ≃ Measureₓ α :=
  { toFun := ennreal_to_measure, invFun := to_ennreal_vector_measure,
    left_inv :=
      fun _ =>
        ext
          fun s hs =>
            by 
              rw [to_ennreal_vector_measure_apply_measurable hs, ennreal_to_measure_apply hs],
    right_inv :=
      fun _ =>
        measure.ext
          fun s hs =>
            by 
              rw [ennreal_to_measure_apply hs, to_ennreal_vector_measure_apply_measurable hs] }

end 

section 

variable[MeasurableSpace α][MeasurableSpace β]

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

variable(v : vector_measure α M)

/-- The pushforward of a vector measure along a function. -/
def map (v : vector_measure α M) (f : α → β) : vector_measure β M :=
  if hf : Measurable f then
    { measureOf' := fun s => if MeasurableSet s then v (f ⁻¹' s) else 0,
      empty' :=
        by 
          simp ,
      not_measurable' := fun i hi => if_neg hi,
      m_Union' :=
        by 
          intro g hg₁ hg₂ 
          convert v.m_Union (fun i => hf (hg₁ i)) fun i j hij x hx => hg₂ i j hij hx
          ·
            ext i 
            rw [if_pos (hg₁ i)]
          ·
            rw [preimage_Union, if_pos (MeasurableSet.Union hg₁)] }
  else 0

theorem map_not_measurable {f : α → β} (hf : ¬Measurable f) : v.map f = 0 :=
  dif_neg hf

theorem map_apply {f : α → β} (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s) :=
  by 
    rw [map, dif_pos hf]
    exact if_pos hs

@[simp]
theorem map_id : v.map id = v :=
  ext
    fun i hi =>
      by 
        rw [map_apply v measurable_id hi, preimage_id]

@[simp]
theorem map_zero (f : α → β) : (0 : vector_measure α M).map f = 0 :=
  by 
    byCases' hf : Measurable f
    ·
      ext i hi 
      rw [map_apply _ hf hi, zero_apply, zero_apply]
    ·
      exact dif_neg hf

section 

variable{N : Type _}[AddCommMonoidₓ N][TopologicalSpace N]

/-- Given a vector measure `v` on `M` and a continuous add_monoid_hom `f : M → N`, `f ∘ v` is a
vector measure on `N`. -/
def map_range (v : vector_measure α M) (f : M →+ N) (hf : Continuous f) : vector_measure α N :=
  { measureOf' := fun s => f (v s),
    empty' :=
      by 
        rw [Empty, AddMonoidHom.map_zero],
    not_measurable' :=
      fun i hi =>
        by 
          rw [not_measurable v hi, AddMonoidHom.map_zero],
    m_Union' := fun g hg₁ hg₂ => HasSum.map (v.m_Union hg₁ hg₂) f hf }

@[simp]
theorem map_range_apply {f : M →+ N} (hf : Continuous f) {s : Set α} : v.map_range f hf s = f (v s) :=
  rfl

@[simp]
theorem map_range_id : v.map_range (AddMonoidHom.id M) continuous_id = v :=
  by 
    ext 
    rfl

@[simp]
theorem map_range_zero {f : M →+ N} (hf : Continuous f) : map_range (0 : vector_measure α M) f hf = 0 :=
  by 
    ext 
    simp 

section HasContinuousAdd

variable[HasContinuousAdd M][HasContinuousAdd N]

@[simp]
theorem map_range_add {v w : vector_measure α M} {f : M →+ N} (hf : Continuous f) :
  (v+w).map_range f hf = v.map_range f hf+w.map_range f hf :=
  by 
    ext 
    simp 

/-- Given a continuous add_monoid_hom `f : M → N`, `map_range_hom` is the add_monoid_hom mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def map_range_hom (f : M →+ N) (hf : Continuous f) : vector_measure α M →+ vector_measure α N :=
  { toFun := fun v => v.map_range f hf, map_zero' := map_range_zero hf, map_add' := fun _ _ => map_range_add hf }

end HasContinuousAdd

section Module

variable{R : Type _}[Semiringₓ R][Module R M][Module R N]

variable[TopologicalSpace R][HasContinuousAdd M][HasContinuousAdd N][HasContinuousSmul R M][HasContinuousSmul R N]

/-- Given a continuous linear map `f : M → N`, `map_rangeₗ` is the linear map mapping the
vector measure `v` on `M` to the vector measure `f ∘ v` on `N`. -/
def map_rangeₗ (f : M →ₗ[R] N) (hf : Continuous f) : vector_measure α M →ₗ[R] vector_measure α N :=
  { toFun := fun v => v.map_range f.to_add_monoid_hom hf, map_add' := fun _ _ => map_range_add hf,
    map_smul' :=
      by 
        intros 
        ext 
        simp  }

end Module

end 

/-- The restriction of a vector measure on some set. -/
def restrict (v : vector_measure α M) (i : Set α) : vector_measure α M :=
  if hi : MeasurableSet i then
    { measureOf' := fun s => if MeasurableSet s then v (s ∩ i) else 0,
      empty' :=
        by 
          simp ,
      not_measurable' := fun i hi => if_neg hi,
      m_Union' :=
        by 
          intro f hf₁ hf₂ 
          convert v.m_Union (fun n => (hf₁ n).inter hi) (hf₂.mono$ fun i j => Disjoint.mono inf_le_left inf_le_left)
          ·
            ext n 
            rw [if_pos (hf₁ n)]
          ·
            rw [Union_inter, if_pos (MeasurableSet.Union hf₁)] }
  else 0

theorem restrict_not_measurable {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0 :=
  dif_neg hi

theorem restrict_apply {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) :
  v.restrict i j = v (j ∩ i) :=
  by 
    rw [restrict, dif_pos hi]
    exact if_pos hj

theorem restrict_eq_self {i : Set α} (hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) (hij : j ⊆ i) :
  v.restrict i j = v j :=
  by 
    rw [restrict_apply v hi hj, inter_eq_left_iff_subset.2 hij]

@[simp]
theorem restrict_empty : v.restrict ∅ = 0 :=
  ext
    fun i hi =>
      by 
        rw [restrict_apply v MeasurableSet.empty hi, inter_empty, v.empty, zero_apply]

@[simp]
theorem restrict_univ : v.restrict univ = v :=
  ext
    fun i hi =>
      by 
        rw [restrict_apply v MeasurableSet.univ hi, inter_univ]

@[simp]
theorem restrict_zero {i : Set α} : (0 : vector_measure α M).restrict i = 0 :=
  by 
    byCases' hi : MeasurableSet i
    ·
      ext j hj 
      rw [restrict_apply 0 hi hj]
      rfl
    ·
      exact dif_neg hi

section HasContinuousAdd

variable[HasContinuousAdd M]

theorem map_add (v w : vector_measure α M) (f : α → β) : (v+w).map f = v.map f+w.map f :=
  by 
    byCases' hf : Measurable f
    ·
      ext i hi 
      simp [map_apply _ hf hi]
    ·
      simp [map, dif_neg hf]

/-- `vector_measure.map` as an additive monoid homomorphism. -/
@[simps]
def map_gm (f : α → β) : vector_measure α M →+ vector_measure β M :=
  { toFun := fun v => v.map f, map_zero' := map_zero f, map_add' := fun _ _ => map_add _ _ f }

theorem restrict_add (v w : vector_measure α M) (i : Set α) : (v+w).restrict i = v.restrict i+w.restrict i :=
  by 
    byCases' hi : MeasurableSet i
    ·
      ext j hj 
      simp [restrict_apply _ hi hj]
    ·
      simp [restrict_not_measurable _ hi]

/--`vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrict_gm (i : Set α) : vector_measure α M →+ vector_measure α M :=
  { toFun := fun v => v.restrict i, map_zero' := restrict_zero, map_add' := fun _ _ => restrict_add _ _ i }

end HasContinuousAdd

end 

section 

variable[MeasurableSpace β]

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

variable{R : Type _}[Semiringₓ R][DistribMulAction R M]

variable[TopologicalSpace R][HasContinuousSmul R M]

include m

@[simp]
theorem map_smul {v : vector_measure α M} {f : α → β} (c : R) : (c • v).map f = c • v.map f :=
  by 
    byCases' hf : Measurable f
    ·
      ext i hi 
      simp [map_apply _ hf hi]
    ·
      simp only [map, dif_neg hf]
      ext i hi 
      simp 

@[simp]
theorem restrict_smul {v : vector_measure α M} {i : Set α} (c : R) : (c • v).restrict i = c • v.restrict i :=
  by 
    byCases' hi : MeasurableSet i
    ·
      ext j hj 
      simp [restrict_apply _ hi hj]
    ·
      simp only [restrict_not_measurable _ hi]
      ext j hj 
      simp 

end 

section 

variable[MeasurableSpace β]

variable{M : Type _}[AddCommMonoidₓ M][TopologicalSpace M]

variable{R : Type _}[Semiringₓ R][Module R M]

variable[TopologicalSpace R][HasContinuousSmul R M][HasContinuousAdd M]

include m

/-- `vector_measure.map` as a linear map. -/
@[simps]
def mapₗ (f : α → β) : vector_measure α M →ₗ[R] vector_measure β M :=
  { toFun := fun v => v.map f, map_add' := fun _ _ => map_add _ _ f, map_smul' := fun _ _ => map_smul _ }

/-- `vector_measure.restrict` as an additive monoid homomorphism. -/
@[simps]
def restrictₗ (i : Set α) : vector_measure α M →ₗ[R] vector_measure α M :=
  { toFun := fun v => v.restrict i, map_add' := fun _ _ => restrict_add _ _ i, map_smul' := fun _ _ => restrict_smul _ }

end 

section 

variable{M : Type _}[TopologicalSpace M][AddCommMonoidₓ M][PartialOrderₓ M]

include m

/-- Vector measures over a partially ordered monoid is partially ordered.

This definition is consistent with `measure.partial_order`. -/
instance  : PartialOrderₓ (vector_measure α M) :=
  { le := fun v w => ∀ i, MeasurableSet i → v i ≤ w i, le_refl := fun v i hi => le_reflₓ _,
    le_trans := fun u v w h₁ h₂ i hi => le_transₓ (h₁ i hi) (h₂ i hi),
    le_antisymm := fun v w h₁ h₂ => ext fun i hi => le_antisymmₓ (h₁ i hi) (h₂ i hi) }

variable{u v w : vector_measure α M}

theorem le_iff : v ≤ w ↔ ∀ i, MeasurableSet i → v i ≤ w i :=
  Iff.rfl

theorem le_iff' : v ≤ w ↔ ∀ i, v i ≤ w i :=
  by 
    refine' ⟨fun h i => _, fun h i hi => h i⟩
    byCases' hi : MeasurableSet i
    ·
      exact h i hi
    ·
      rw [v.not_measurable hi, w.not_measurable hi]

end 

localized [MeasureTheory]
  notation:50 v " ≤[" i:50 "] " w:50 =>
    MeasureTheory.VectorMeasure.restrict v i ≤ MeasureTheory.VectorMeasure.restrict w i

section 

variable{M : Type _}[TopologicalSpace M][AddCommMonoidₓ M][PartialOrderₓ M]

variable(v w : vector_measure α M)

theorem restrict_le_restrict_iff {i : Set α} (hi : MeasurableSet i) :
  v ≤[i] w ↔ ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j :=
  ⟨fun h j hj₁ hj₂ => restrict_eq_self v hi hj₁ hj₂ ▸ restrict_eq_self w hi hj₁ hj₂ ▸ h j hj₁,
    fun h =>
      le_iff.1
        fun j hj =>
          (restrict_apply v hi hj).symm ▸ (restrict_apply w hi hj).symm ▸ h (hj.inter hi) (Set.inter_subset_right j i)⟩

theorem subset_le_of_restrict_le_restrict {i : Set α} (hi : MeasurableSet i) (hi₂ : v ≤[i] w) {j : Set α} (hj : j ⊆ i) :
  v j ≤ w j :=
  by 
    byCases' hj₁ : MeasurableSet j
    ·
      exact (restrict_le_restrict_iff _ _ hi).1 hi₂ hj₁ hj
    ·
      rw [v.not_measurable hj₁, w.not_measurable hj₁]

theorem restrict_le_restrict_of_subset_le {i : Set α} (h : ∀ ⦃j⦄, MeasurableSet j → j ⊆ i → v j ≤ w j) : v ≤[i] w :=
  by 
    byCases' hi : MeasurableSet i
    ·
      exact (restrict_le_restrict_iff _ _ hi).2 h
    ·
      rw [restrict_not_measurable v hi, restrict_not_measurable w hi]
      exact le_reflₓ _

theorem restrict_le_restrict_subset {i j : Set α} (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hij : j ⊆ i) : v ≤[j] w :=
  restrict_le_restrict_of_subset_le v w
    fun k hk₁ hk₂ => subset_le_of_restrict_le_restrict v w hi₁ hi₂ (Set.Subset.trans hk₂ hij)

theorem le_restrict_empty : v ≤[∅] w :=
  by 
    intro j hj 
    rw [restrict_empty, restrict_empty]

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_restrict_univ_iff_le : «expr ↔ »(«expr ≤[ ] »(v, univ, w), «expr ≤ »(v, w)) :=
begin
  split,
  { intros [ident h, ident s, ident hs],
    have [] [] [":=", expr h s hs],
    rwa ["[", expr restrict_apply _ measurable_set.univ hs, ",", expr inter_univ, ",", expr restrict_apply _ measurable_set.univ hs, ",", expr inter_univ, "]"] ["at", ident this] },
  { intros [ident h, ident s, ident hs],
    rw ["[", expr restrict_apply _ measurable_set.univ hs, ",", expr inter_univ, ",", expr restrict_apply _ measurable_set.univ hs, ",", expr inter_univ, "]"] [],
    exact [expr h s hs] }
end

end 

section 

variable{M : Type _}[TopologicalSpace M][OrderedAddCommGroup M][TopologicalAddGroup M]

variable(v w : vector_measure α M)

theorem neg_le_neg {i : Set α} (hi : MeasurableSet i) (h : v ≤[i] w) : -w ≤[i] -v :=
  by 
    intro j hj₁ 
    rw [restrict_apply _ hi hj₁, restrict_apply _ hi hj₁, neg_apply, neg_apply]
    refine' neg_le_neg _ 
    rw [←restrict_apply _ hi hj₁, ←restrict_apply _ hi hj₁]
    exact h j hj₁

@[simp]
theorem neg_le_neg_iff {i : Set α} (hi : MeasurableSet i) : -w ≤[i] -v ↔ v ≤[i] w :=
  ⟨fun h => neg_negₓ v ▸ neg_negₓ w ▸ neg_le_neg _ _ hi h, fun h => neg_le_neg _ _ hi h⟩

end 

section 

variable{M : Type _}[TopologicalSpace M][OrderedAddCommMonoid M][OrderClosedTopology M]

variable(v w : vector_measure α M){i j : Set α}

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem restrict_le_restrict_Union
{f : exprℕ() → set α}
(hf₁ : ∀ n, measurable_set (f n))
(hf₂ : ∀ n, «expr ≤[ ] »(v, f n, w)) : «expr ≤[ ] »(v, «expr⋃ , »((n), f n), w) :=
begin
  refine [expr restrict_le_restrict_of_subset_le v w (λ a ha₁ ha₂, _)],
  have [ident ha₃] [":", expr «expr = »(«expr⋃ , »((n), «expr ∩ »(a, disjointed f n)), a)] [],
  { rwa ["[", "<-", expr inter_Union, ",", expr Union_disjointed, ",", expr inter_eq_left_iff_subset, "]"] [] },
  have [ident ha₄] [":", expr pairwise «expr on »(disjoint, λ n, «expr ∩ »(a, disjointed f n))] [],
  { exact [expr (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right)] },
  rw ["[", "<-", expr ha₃, ",", expr v.of_disjoint_Union_nat _ ha₄, ",", expr w.of_disjoint_Union_nat _ ha₄, "]"] [],
  refine [expr tsum_le_tsum (λ n, (restrict_le_restrict_iff v w (hf₁ n)).1 (hf₂ n) _ _) _ _],
  { exact [expr ha₁.inter (measurable_set.disjointed hf₁ n)] },
  { exact [expr set.subset.trans (set.inter_subset_right _ _) (disjointed_subset _ _)] },
  { refine [expr (v.m_Union (λ n, _) _).summable],
    { exact [expr ha₁.inter (measurable_set.disjointed hf₁ n)] },
    { exact [expr (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right)] } },
  { refine [expr (w.m_Union (λ n, _) _).summable],
    { exact [expr ha₁.inter (measurable_set.disjointed hf₁ n)] },
    { exact [expr (disjoint_disjointed _).mono (λ i j, disjoint.mono inf_le_right inf_le_right)] } },
  { intro [ident n],
    exact [expr ha₁.inter (measurable_set.disjointed hf₁ n)] },
  { exact [expr λ n, ha₁.inter (measurable_set.disjointed hf₁ n)] }
end

theorem restrict_le_restrict_encodable_Union [Encodable β] {f : β → Set α} (hf₁ : ∀ b, MeasurableSet (f b))
  (hf₂ : ∀ b, v ≤[f b] w) : v ≤[⋃b, f b] w :=
  by 
    rw [←Encodable.Union_decode₂]
    refine' restrict_le_restrict_Union v w _ _
    ·
      intro n 
      measurability
    ·
      intro n 
      cases' Encodable.decode₂ β n with b
      ·
        simp 
      ·
        simp [hf₂ b]

theorem restrict_le_restrict_union (hi₁ : MeasurableSet i) (hi₂ : v ≤[i] w) (hj₁ : MeasurableSet j) (hj₂ : v ≤[j] w) :
  v ≤[i ∪ j] w :=
  by 
    rw [union_eq_Union]
    refine' restrict_le_restrict_encodable_Union v w _ _
    ·
      measurability
    ·
      rintro (_ | _) <;> simpa

end 

section 

variable{M : Type _}[TopologicalSpace M][OrderedAddCommMonoid M]

variable(v w : vector_measure α M){i j : Set α}

theorem nonneg_of_zero_le_restrict (hi₂ : 0 ≤[i] v) : 0 ≤ v i :=
  by 
    byCases' hi₁ : MeasurableSet i
    ·
      exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
    ·
      rw [v.not_measurable hi₁]

theorem nonpos_of_restrict_le_zero (hi₂ : v ≤[i] 0) : v i ≤ 0 :=
  by 
    byCases' hi₁ : MeasurableSet i
    ·
      exact (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hi₁ Set.Subset.rfl
    ·
      rw [v.not_measurable hi₁]

theorem zero_le_restrict_not_measurable (hi : ¬MeasurableSet i) : 0 ≤[i] v :=
  by 
    rw [restrict_zero, restrict_not_measurable _ hi]
    exact le_reflₓ _

theorem restrict_le_zero_of_not_measurable (hi : ¬MeasurableSet i) : v ≤[i] 0 :=
  by 
    rw [restrict_zero, restrict_not_measurable _ hi]
    exact le_reflₓ _

theorem measurable_of_not_zero_le_restrict (hi : ¬0 ≤[i] v) : MeasurableSet i :=
  Not.imp_symm (zero_le_restrict_not_measurable _) hi

theorem measurable_of_not_restrict_le_zero (hi : ¬v ≤[i] 0) : MeasurableSet i :=
  Not.imp_symm (restrict_le_zero_of_not_measurable _) hi

theorem zero_le_restrict_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : 0 ≤[i] v) : 0 ≤[j] v :=
  restrict_le_restrict_of_subset_le _ _
    fun k hk₁ hk₂ => (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

theorem restrict_le_zero_subset (hi₁ : MeasurableSet i) (hij : j ⊆ i) (hi₂ : v ≤[i] 0) : v ≤[j] 0 :=
  restrict_le_restrict_of_subset_le _ _
    fun k hk₁ hk₂ => (restrict_le_restrict_iff _ _ hi₁).1 hi₂ hk₁ (Set.Subset.trans hk₂ hij)

end 

section 

variable{M : Type _}[TopologicalSpace M][LinearOrderedAddCommMonoid M]

variable(v w : vector_measure α M){i j : Set α}

include m

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_pos_measure_of_not_restrict_le_zero
(hi : «expr¬ »(«expr ≤[ ] »(v, i, 0))) : «expr∃ , »((j : set α), «expr ∧ »(measurable_set j, «expr ∧ »(«expr ⊆ »(j, i), «expr < »(0, v j)))) :=
begin
  have [ident hi₁] [":", expr measurable_set i] [":=", expr measurable_of_not_restrict_le_zero _ hi],
  rw ["[", expr restrict_le_restrict_iff _ _ hi₁, "]"] ["at", ident hi],
  push_neg ["at", ident hi],
  obtain ["⟨", ident j, ",", ident hj₁, ",", ident hj₂, ",", ident hj, "⟩", ":=", expr hi],
  exact [expr ⟨j, hj₁, hj₂, hj⟩]
end

end 

section 

variable{M :
    Type _}[TopologicalSpace M][AddCommMonoidₓ M][PartialOrderₓ M][CovariantClass M M (·+·) (· ≤ ·)][HasContinuousAdd M]

include m

instance covariant_add_le : CovariantClass (vector_measure α M) (vector_measure α M) (·+·) (· ≤ ·) :=
  ⟨fun u v w h i hi => add_le_add_left (h i hi) _⟩

end 

section 

variable{L M N : Type _}

variable[AddCommMonoidₓ
      L][TopologicalSpace L][AddCommMonoidₓ M][TopologicalSpace M][AddCommMonoidₓ N][TopologicalSpace N]

include m

/-- A vector measure `v` is absolutely continuous with respect to a measure `μ` if for all sets
`s`, `μ s = 0`, we have `v s = 0`. -/
def absolutely_continuous (v : vector_measure α M) (w : vector_measure α N) :=
  ∀ ⦃s : Set α⦄, w s = 0 → v s = 0

localized [MeasureTheory] infixl:50 " ≪ᵥ " => MeasureTheory.VectorMeasure.AbsolutelyContinuous

open_locale MeasureTheory

namespace AbsolutelyContinuous

variable{v : vector_measure α M}{w : vector_measure α N}

theorem mk (h : ∀ ⦃s : Set α⦄, MeasurableSet s → w s = 0 → v s = 0) : v ≪ᵥ w :=
  by 
    intro s hs 
    byCases' hmeas : MeasurableSet s
    ·
      exact h hmeas hs
    ·
      exact not_measurable v hmeas

theorem Eq {w : vector_measure α M} (h : v = w) : v ≪ᵥ w :=
  fun s hs => h.symm ▸ hs

@[refl]
theorem refl (v : vector_measure α M) : v ≪ᵥ v :=
  Eq rfl

@[trans]
theorem trans {u : vector_measure α L} (huv : u ≪ᵥ v) (hvw : v ≪ᵥ w) : u ≪ᵥ w :=
  fun _ hs => huv$ hvw hs

theorem zero (v : vector_measure α N) : (0 : vector_measure α M) ≪ᵥ v :=
  fun s _ => vector_measure.zero_apply s

theorem neg_left {M : Type _} [AddCommGroupₓ M] [TopologicalSpace M] [TopologicalAddGroup M] {v : vector_measure α M}
  {w : vector_measure α N} (h : v ≪ᵥ w) : -v ≪ᵥ w :=
  fun s hs =>
    by 
      rw [neg_apply, h hs, neg_zero]

theorem neg_right {N : Type _} [AddCommGroupₓ N] [TopologicalSpace N] [TopologicalAddGroup N] {v : vector_measure α M}
  {w : vector_measure α N} (h : v ≪ᵥ w) : v ≪ᵥ -w :=
  by 
    intro s hs 
    rw [neg_apply, neg_eq_zero] at hs 
    exact h hs

theorem add [HasContinuousAdd M] {v₁ v₂ : vector_measure α M} {w : vector_measure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) :
  (v₁+v₂) ≪ᵥ w :=
  fun s hs =>
    by 
      rw [add_apply, hv₁ hs, hv₂ hs, zero_addₓ]

theorem sub {M : Type _} [AddCommGroupₓ M] [TopologicalSpace M] [TopologicalAddGroup M] {v₁ v₂ : vector_measure α M}
  {w : vector_measure α N} (hv₁ : v₁ ≪ᵥ w) (hv₂ : v₂ ≪ᵥ w) : v₁ - v₂ ≪ᵥ w :=
  fun s hs =>
    by 
      rw [sub_apply, hv₁ hs, hv₂ hs, zero_sub, neg_zero]

theorem smul {R : Type _} [Semiringₓ R] [DistribMulAction R M] [TopologicalSpace R] [HasContinuousSmul R M] {r : R}
  {v : vector_measure α M} {w : vector_measure α N} (h : v ≪ᵥ w) : r • v ≪ᵥ w :=
  fun s hs =>
    by 
      rw [smul_apply, h hs, smul_zero]

theorem map [measure_space β] (h : v ≪ᵥ w) (f : α → β) : v.map f ≪ᵥ w.map f :=
  by 
    byCases' hf : Measurable f
    ·
      refine' mk fun s hs hws => _ 
      rw [map_apply _ hf hs] at hws⊢
      exact h hws
    ·
      intro s hs 
      rw [map_not_measurable v hf, zero_apply]

theorem ennreal_to_measure {μ : vector_measure α ℝ≥0∞} :
  (∀ ⦃s : Set α⦄, μ.ennreal_to_measure s = 0 → v s = 0) ↔ v ≪ᵥ μ :=
  by 
    split  <;> intro h
    ·
      refine' mk fun s hmeas hs => h _ 
      rw [←hs, ennreal_to_measure_apply hmeas]
    ·
      intro s hs 
      byCases' hmeas : MeasurableSet s
      ·
        rw [ennreal_to_measure_apply hmeas] at hs 
        exact h hs
      ·
        exact not_measurable v hmeas

end AbsolutelyContinuous

/-- Two vector measures `v` and `w` are said to be mutually singular if there exists a measurable
set `s`, such that for all `t ⊆ s`, `v t = 0` and for all `t ⊆ sᶜ`, `w t = 0`.

We note that we do not require the measurability of `t` in the definition since this makes it easier
to use. This is equivalent to the definition which requires measurability. To prove
`mutually_singular` with the measurability condition, use
`measure_theory.vector_measure.mutually_singular.mk`. -/
def mutually_singular (v : vector_measure α M) (w : vector_measure α N) : Prop :=
  ∃ s : Set α, MeasurableSet s ∧ (∀ t (_ : t ⊆ s), v t = 0) ∧ ∀ t (_ : t ⊆ «expr ᶜ» s), w t = 0

localized [MeasureTheory] infixl:60 " ⊥ᵥ " => MeasureTheory.VectorMeasure.MutuallySingular

namespace MutuallySingular

variable{v v₁ v₂ : vector_measure α M}{w w₁ w₂ : vector_measure α N}

theorem mk (s : Set α) (hs : MeasurableSet s) (h₁ : ∀ t (_ : t ⊆ s), MeasurableSet t → v t = 0)
  (h₂ : ∀ t (_ : t ⊆ «expr ᶜ» s), MeasurableSet t → w t = 0) : v ⊥ᵥ w :=
  by 
    refine' ⟨s, hs, fun t hst => _, fun t hst => _⟩ <;> byCases' ht : MeasurableSet t
    ·
      exact h₁ t hst ht
    ·
      exact not_measurable v ht
    ·
      exact h₂ t hst ht
    ·
      exact not_measurable w ht

theorem symm (h : v ⊥ᵥ w) : w ⊥ᵥ v :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨«expr ᶜ» s, hmeas.compl, hs₂, fun t ht => hs₁ _ (compl_compl s ▸ ht : t ⊆ s)⟩

theorem zero_right : v ⊥ᵥ (0 : vector_measure α N) :=
  ⟨∅, MeasurableSet.empty, fun t ht => (subset_empty_iff.1 ht).symm ▸ v.empty, fun _ _ => zero_apply _⟩

theorem zero_left : (0 : vector_measure α M) ⊥ᵥ w :=
  zero_right.symm

theorem add_left [T2Space N] [HasContinuousAdd M] (h₁ : v₁ ⊥ᵥ w) (h₂ : v₂ ⊥ᵥ w) : (v₁+v₂) ⊥ᵥ w :=
  by 
    obtain ⟨u, hmu, hu₁, hu₂⟩ := h₁ 
    obtain ⟨v, hmv, hv₁, hv₂⟩ := h₂ 
    refine' mk (u ∩ v) (hmu.inter hmv) (fun t ht hmt => _) fun t ht hmt => _
    ·
      rw [add_apply, hu₁ _ (subset_inter_iff.1 ht).1, hv₁ _ (subset_inter_iff.1 ht).2, zero_addₓ]
    ·
      rw [compl_inter] at ht 
      rw [(_ : t = «expr ᶜ» u ∩ t ∪ «expr ᶜ» v \ «expr ᶜ» u ∩ t),
        of_union _ (hmu.compl.inter hmt) ((hmv.compl.diff hmu.compl).inter hmt), hu₂, hv₂, add_zeroₓ]
      ·
        exact subset.trans (inter_subset_left _ _) (diff_subset _ _)
      ·
        exact inter_subset_left _ _
      ·
        infer_instance
      ·
        exact Disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _) disjoint_diff
      ·
        apply subset.antisymm <;> intro x hx
        ·
          byCases' hxu' : x ∈ «expr ᶜ» u
          ·
            exact Or.inl ⟨hxu', hx⟩
          rcases ht hx with (hxu | hxv)
          exacts[False.elim (hxu' hxu), Or.inr ⟨⟨hxv, hxu'⟩, hx⟩]
        ·
          rcases hx with ⟨⟩ <;> exact hx.2

theorem add_right [T2Space M] [HasContinuousAdd N] (h₁ : v ⊥ᵥ w₁) (h₂ : v ⊥ᵥ w₂) : v ⊥ᵥ w₁+w₂ :=
  (add_left h₁.symm h₂.symm).symm

theorem smul_right {R : Type _} [Semiringₓ R] [DistribMulAction R N] [TopologicalSpace R] [HasContinuousSmul R N]
  (r : R) (h : v ⊥ᵥ w) : v ⊥ᵥ r • w :=
  let ⟨s, hmeas, hs₁, hs₂⟩ := h
  ⟨s, hmeas, hs₁,
    fun t ht =>
      by 
        simp only [coe_smul, Pi.smul_apply, hs₂ t ht, smul_zero]⟩

theorem smul_left {R : Type _} [Semiringₓ R] [DistribMulAction R M] [TopologicalSpace R] [HasContinuousSmul R M] (r : R)
  (h : v ⊥ᵥ w) : r • v ⊥ᵥ w :=
  (smul_right r h.symm).symm

theorem neg_left {M : Type _} [AddCommGroupₓ M] [TopologicalSpace M] [TopologicalAddGroup M] {v : vector_measure α M}
  {w : vector_measure α N} (h : v ⊥ᵥ w) : -v ⊥ᵥ w :=
  by 
    obtain ⟨u, hmu, hu₁, hu₂⟩ := h 
    refine' ⟨u, hmu, fun s hs => _, hu₂⟩
    rw [neg_apply v s, neg_eq_zero]
    exact hu₁ s hs

theorem neg_right {N : Type _} [AddCommGroupₓ N] [TopologicalSpace N] [TopologicalAddGroup N] {v : vector_measure α M}
  {w : vector_measure α N} (h : v ⊥ᵥ w) : v ⊥ᵥ -w :=
  h.symm.neg_left.symm

@[simp]
theorem neg_left_iff {M : Type _} [AddCommGroupₓ M] [TopologicalSpace M] [TopologicalAddGroup M]
  {v : vector_measure α M} {w : vector_measure α N} : -v ⊥ᵥ w ↔ v ⊥ᵥ w :=
  ⟨fun h => neg_negₓ v ▸ h.neg_left, neg_left⟩

@[simp]
theorem neg_right_iff {N : Type _} [AddCommGroupₓ N] [TopologicalSpace N] [TopologicalAddGroup N]
  {v : vector_measure α M} {w : vector_measure α N} : v ⊥ᵥ -w ↔ v ⊥ᵥ w :=
  ⟨fun h => neg_negₓ w ▸ h.neg_right, neg_right⟩

end MutuallySingular

section Trim

omit m

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Restriction of a vector measure onto a sub-σ-algebra. -/
@[simps #[]]
def trim {m n : measurable_space α} (v : vector_measure α M) (hle : «expr ≤ »(m, n)) : @vector_measure α m M _ _ :=
{ measure_of' := λ i, if «exprmeasurable_set[ ]»(m) i then v i else 0,
  empty' := by rw ["[", expr if_pos measurable_set.empty, ",", expr v.empty, "]"] [],
  not_measurable' := λ i hi, by rw [expr if_neg hi] [],
  m_Union' := λ f hf₁ hf₂, begin
    have [ident hf₁'] [":", expr ∀ k, «exprmeasurable_set[ ]»(n) (f k)] [":=", expr λ k, hle _ (hf₁ k)],
    convert [] [expr v.m_Union hf₁' hf₂] [],
    { ext [] [ident n] [],
      rw [expr if_pos (hf₁ n)] [] },
    { rw [expr if_pos (@measurable_set.Union _ _ m _ _ hf₁)] [] }
  end }

variable{n : MeasurableSpace α}{v : vector_measure α M}

theorem trim_eq_self : v.trim le_rfl = v :=
  by 
    ext1 i hi 
    exact if_pos hi

@[simp]
theorem zero_trim (hle : m ≤ n) : (0 : vector_measure α M).trim hle = 0 :=
  by 
    ext1 i hi 
    exact if_pos hi

theorem trim_measurable_set_eq (hle : m ≤ n) {i : Set α} (hi : measurable_set[m] i) : v.trim hle i = v i :=
  if_pos hi

theorem restrict_trim (hle : m ≤ n) {i : Set α} (hi : measurable_set[m] i) :
  @vector_measure.restrict α m M _ _ (v.trim hle) i = (v.restrict i).trim hle :=
  by 
    ext j hj 
    rw [restrict_apply, trim_measurable_set_eq hle hj, restrict_apply, trim_measurable_set_eq]
    all_goals 
      measurability

end Trim

end 

end VectorMeasure

namespace SignedMeasure

open VectorMeasure

open_locale MeasureTheory

include m

/-- The underlying function for `signed_measure.to_measure_of_zero_le`. -/
def to_measure_of_zero_le' (s : signed_measure α) (i : Set α) (hi : 0 ≤[i] s) (j : Set α) (hj : MeasurableSet j) :
  ℝ≥0∞ :=
  @coeₓ ℝ≥0  ℝ≥0∞ _
    ⟨s.restrict i j,
      le_transₓ
        (by 
          simp )
        (hi j hj)⟩

-- error in MeasureTheory.Measure.VectorMeasure: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a signed measure `s` and a positive measurable set `i`, `to_measure_of_zero_le`
provides the measure, mapping measurable sets `j` to `s (i ∩ j)`. -/
def to_measure_of_zero_le
(s : signed_measure α)
(i : set α)
(hi₁ : measurable_set i)
(hi₂ : «expr ≤[ ] »(0, i, s)) : measure α :=
measure.of_measurable (s.to_measure_of_zero_le' i hi₂) (by { simp_rw ["[", expr to_measure_of_zero_le', ",", expr s.restrict_apply hi₁ measurable_set.empty, ",", expr set.empty_inter i, ",", expr s.empty, "]"] [],
   refl }) (begin
   intros [ident f, ident hf₁, ident hf₂],
   have [ident h₁] [":", expr ∀ n, measurable_set «expr ∩ »(i, f n)] [":=", expr λ n, hi₁.inter (hf₁ n)],
   have [ident h₂] [":", expr pairwise «expr on »(disjoint, λ n : exprℕ(), «expr ∩ »(i, f n))] [],
   { rintro [ident n, ident m, ident hnm, ident x, "⟨", "⟨", "_", ",", ident hx₁, "⟩", ",", "_", ",", ident hx₂, "⟩"],
     exact [expr hf₂ n m hnm ⟨hx₁, hx₂⟩] },
   simp [] [] ["only"] ["[", expr to_measure_of_zero_le', ",", expr s.restrict_apply hi₁ (measurable_set.Union hf₁), ",", expr set.inter_comm, ",", expr set.inter_Union, ",", expr s.of_disjoint_Union_nat h₁ h₂, ",", expr ennreal.some_eq_coe, ",", expr id.def, "]"] [] [],
   have [ident h] [":", expr ∀
    n, «expr ≤ »(0, s «expr ∩ »(i, f n))] [":=", expr λ
    n, s.nonneg_of_zero_le_restrict (s.zero_le_restrict_subset hi₁ (inter_subset_left _ _) hi₂)],
   rw ["[", expr nnreal.coe_tsum_of_nonneg h, ",", expr ennreal.coe_tsum, "]"] [],
   { refine [expr tsum_congr (λ n, _)],
     simp_rw ["[", expr s.restrict_apply hi₁ (hf₁ n), ",", expr set.inter_comm, "]"] [] },
   { exact [expr (nnreal.summable_coe_of_nonneg h).2 (s.m_Union h₁ h₂).summable] }
 end)

variable(s : signed_measure α){i j : Set α}

theorem to_measure_of_zero_le_apply (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
  s.to_measure_of_zero_le i hi₁ hi j =
    @coeₓ ℝ≥0  ℝ≥0∞ _
      ⟨s (i ∩ j), nonneg_of_zero_le_restrict s (zero_le_restrict_subset s hi₁ (Set.inter_subset_left _ _) hi)⟩ :=
  by 
    simpRw [to_measure_of_zero_le, measure.of_measurable_apply _ hj₁, to_measure_of_zero_le', s.restrict_apply hi₁ hj₁,
      Set.inter_comm]

/-- Given a signed measure `s` and a negative measurable set `i`, `to_measure_of_le_zero`
provides the measure, mapping measurable sets `j` to `-s (i ∩ j)`. -/
def to_measure_of_le_zero (s : signed_measure α) (i : Set α) (hi₁ : MeasurableSet i) (hi₂ : s ≤[i] 0) : Measureₓ α :=
  to_measure_of_zero_le (-s) i hi₁$ @neg_zero (vector_measure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi₂

theorem to_measure_of_le_zero_apply (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) (hj₁ : MeasurableSet j) :
  s.to_measure_of_le_zero i hi₁ hi j =
    @coeₓ ℝ≥0  ℝ≥0∞ _
      ⟨-s (i ∩ j),
        neg_apply s (i ∩ j) ▸
          nonneg_of_zero_le_restrict _
            (zero_le_restrict_subset _ hi₁ (Set.inter_subset_left _ _)
              (@neg_zero (vector_measure α ℝ) _ ▸ neg_le_neg _ _ hi₁ hi))⟩ :=
  by 
    erw [to_measure_of_zero_le_apply]
    ·
      simp 
    ·
      assumption

/-- `signed_measure.to_measure_of_zero_le` is a finite measure. -/
instance to_measure_of_zero_le_finite (hi : 0 ≤[i] s) (hi₁ : MeasurableSet i) :
  is_finite_measure (s.to_measure_of_zero_le i hi₁ hi) :=
  { measure_univ_lt_top :=
      by 
        rw [to_measure_of_zero_le_apply s hi hi₁ MeasurableSet.univ]
        exact Ennreal.coe_lt_top }

/-- `signed_measure.to_measure_of_le_zero` is a finite measure. -/
instance to_measure_of_le_zero_finite (hi : s ≤[i] 0) (hi₁ : MeasurableSet i) :
  is_finite_measure (s.to_measure_of_le_zero i hi₁ hi) :=
  { measure_univ_lt_top :=
      by 
        rw [to_measure_of_le_zero_apply s hi hi₁ MeasurableSet.univ]
        exact Ennreal.coe_lt_top }

theorem to_measure_of_zero_le_to_signed_measure (hs : 0 ≤[univ] s) :
  (s.to_measure_of_zero_le univ MeasurableSet.univ hs).toSignedMeasure = s :=
  by 
    ext i hi 
    simp [measure.to_signed_measure_apply_measurable hi, to_measure_of_zero_le_apply _ _ _ hi]

theorem to_measure_of_le_zero_to_signed_measure (hs : s ≤[univ] 0) :
  (s.to_measure_of_le_zero univ MeasurableSet.univ hs).toSignedMeasure = -s :=
  by 
    ext i hi 
    simp [measure.to_signed_measure_apply_measurable hi, to_measure_of_le_zero_apply _ _ _ hi]

end SignedMeasure

namespace Measureₓ

open VectorMeasure

variable(μ : Measureₓ α)[is_finite_measure μ]

theorem zero_le_to_signed_measure : 0 ≤ μ.to_signed_measure :=
  by 
    rw [←le_restrict_univ_iff_le]
    refine' restrict_le_restrict_of_subset_le _ _ fun j hj₁ _ => _ 
    simp only [measure.to_signed_measure_apply_measurable hj₁, coe_zero, Pi.zero_apply, Ennreal.to_real_nonneg,
      vector_measure.coe_zero]

theorem to_signed_measure_to_measure_of_zero_le :
  μ.to_signed_measure.to_measure_of_zero_le univ MeasurableSet.univ
      ((le_restrict_univ_iff_le _ _).2 (zero_le_to_signed_measure μ)) =
    μ :=
  by 
    refine' measure.ext fun i hi => _ 
    lift μ i to  ℝ≥0  using (measure_lt_top _ _).Ne with m hm 
    simp [signed_measure.to_measure_of_zero_le_apply _ _ _ hi, measure.to_signed_measure_apply_measurable hi, ←hm]

end Measureₓ

end MeasureTheory

