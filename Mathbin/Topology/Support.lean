/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import Topology.Separation

#align_import topology.support from "leanprover-community/mathlib"@"0ebfdb71919ac6ca5d7fbc61a082fa2519556818"

/-!
# The topological support of a function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define the topological support of a function `f`, `tsupport f`,
as the closure of the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `function.mul_tsupport` & `function.tsupport`
* `function.has_compact_mul_support` & `function.has_compact_support`

## Implementation Notes

* We write all lemmas for multiplicative functions, and use `@[to_additive]` to get the more common
  additive versions.
* We do not put the definitions in the `function` namespace, following many other topological
  definitions that are in the root namespace (compare `embedding` vs `function.embedding`).
-/


open Function Set Filter

open scoped Topology

variable {X α α' β γ δ M E R : Type _}

section One

variable [One α]

variable [TopologicalSpace X]

#print mulTSupport /-
/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive
      " The topological support of a function is the closure of its support. i.e. the closure of the\n  set of all elements where the function is nonzero. "]
def mulTSupport (f : X → α) : Set X :=
  closure (mulSupport f)
#align mul_tsupport mulTSupport
#align tsupport tsupport
-/

#print subset_mulTSupport /-
@[to_additive]
theorem subset_mulTSupport (f : X → α) : mulSupport f ⊆ mulTSupport f :=
  subset_closure
#align subset_mul_tsupport subset_mulTSupport
#align subset_tsupport subset_tsupport
-/

#print isClosed_mulTSupport /-
@[to_additive]
theorem isClosed_mulTSupport (f : X → α) : IsClosed (mulTSupport f) :=
  isClosed_closure
#align is_closed_mul_tsupport isClosed_mulTSupport
#align is_closed_tsupport isClosed_tsupport
-/

#print mulTSupport_eq_empty_iff /-
@[to_additive]
theorem mulTSupport_eq_empty_iff {f : X → α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport, closure_empty_iff, mul_support_eq_empty_iff]
#align mul_tsupport_eq_empty_iff mulTSupport_eq_empty_iff
#align tsupport_eq_empty_iff tsupport_eq_empty_iff
-/

#print image_eq_one_of_nmem_mulTSupport /-
@[to_additive]
theorem image_eq_one_of_nmem_mulTSupport {f : X → α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx
#align image_eq_one_of_nmem_mul_tsupport image_eq_one_of_nmem_mulTSupport
#align image_eq_zero_of_nmem_tsupport image_eq_zero_of_nmem_tsupport
-/

#print range_subset_insert_image_mulTSupport /-
@[to_additive]
theorem range_subset_insert_image_mulTSupport (f : X → α) :
    range f ⊆ insert 1 (f '' mulTSupport f) :=
  (range_subset_insert_image_mulSupport f).trans <|
    insert_subset_insert <| image_subset _ subset_closure
#align range_subset_insert_image_mul_tsupport range_subset_insert_image_mulTSupport
#align range_subset_insert_image_tsupport range_subset_insert_image_tsupport
-/

#print range_eq_image_mulTSupport_or /-
@[to_additive]
theorem range_eq_image_mulTSupport_or (f : X → α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)
#align range_eq_image_mul_tsupport_or range_eq_image_mulTSupport_or
#align range_eq_image_tsupport_or range_eq_image_tsupport_or
-/

#print tsupport_mul_subset_left /-
theorem tsupport_mul_subset_left {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)
#align tsupport_mul_subset_left tsupport_mul_subset_left
-/

#print tsupport_mul_subset_right /-
theorem tsupport_mul_subset_right {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)
#align tsupport_mul_subset_right tsupport_mul_subset_right
-/

end One

#print tsupport_smul_subset_left /-
theorem tsupport_smul_subset_left {M α} [TopologicalSpace X] [Zero M] [Zero α] [SMulWithZero M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g
#align tsupport_smul_subset_left tsupport_smul_subset_left
-/

section

variable [TopologicalSpace α] [TopologicalSpace α']

variable [One β] [One γ] [One δ]

variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

#print not_mem_mulTSupport_iff_eventuallyEq /-
@[to_additive]
theorem not_mem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, Classical.not_forall, not_nonempty_iff_eq_empty, ←
    disjoint_iff_inter_eq_empty, disjoint_mul_support_iff, eventually_eq_iff_exists_mem]
#align not_mem_mul_tsupport_iff_eventually_eq not_mem_mulTSupport_iff_eventuallyEq
#align not_mem_tsupport_iff_eventually_eq not_mem_tsupport_iff_eventuallyEq
-/

#print continuous_of_mulTSupport /-
@[to_additive]
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α → β}
    (hf : ∀ x ∈ mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x =>
    (em _).elim (hf x) fun hx =>
      (@continuousAt_const _ _ _ _ _ 1).congr (not_mem_mulTSupport_iff_eventuallyEq.mp hx).symm
#align continuous_of_mul_tsupport continuous_of_mulTSupport
#align continuous_of_tsupport continuous_of_tsupport
-/

#print HasCompactMulSupport /-
/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive
      " A function `f` *has compact support* or is *compactly supported* if the closure of the support\nof `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a compact\nset. "]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)
#align has_compact_mul_support HasCompactMulSupport
#align has_compact_support HasCompactSupport
-/

#print hasCompactMulSupport_def /-
@[to_additive]
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl
#align has_compact_mul_support_def hasCompactMulSupport_def
#align has_compact_support_def hasCompactSupport_def
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ∉ » K) -/
#print exists_compact_iff_hasCompactMulSupport /-
@[to_additive]
theorem exists_compact_iff_hasCompactMulSupport [T2Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ (x) (_ : x ∉ K), f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mul_support, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]
#align exists_compact_iff_has_compact_mul_support exists_compact_iff_hasCompactMulSupport
#align exists_compact_iff_has_compact_support exists_compact_iff_hasCompactSupport
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:642:2: warning: expanding binder collection (x «expr ∉ » K) -/
#print HasCompactMulSupport.intro /-
@[to_additive]
theorem HasCompactMulSupport.intro [T2Space α] {K : Set α} (hK : IsCompact K)
    (hfK : ∀ (x) (_ : x ∉ K), f x = 1) : HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩
#align has_compact_mul_support.intro HasCompactMulSupport.intro
#align has_compact_support.intro HasCompactSupport.intro
-/

#print HasCompactMulSupport.isCompact /-
@[to_additive]
theorem HasCompactMulSupport.isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) :=
  hf
#align has_compact_mul_support.is_compact HasCompactMulSupport.isCompact
#align has_compact_support.is_compact HasCompactSupport.isCompact
-/

#print hasCompactMulSupport_iff_eventuallyEq /-
@[to_additive]
theorem hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  ⟨fun h =>
    mem_coclosedCompact.mpr
      ⟨mulTSupport f, isClosed_mulTSupport _, h, fun x =>
        not_imp_comm.mpr fun hx => subset_mulTSupport f hx⟩,
    fun h =>
    let ⟨C, hC⟩ := mem_coclosed_compact'.mp h
    IsCompact.of_isClosed_subset hC.2.1 (isClosed_mulTSupport _) (closure_minimal hC.2.2 hC.1)⟩
#align has_compact_mul_support_iff_eventually_eq hasCompactMulSupport_iff_eventuallyEq
#align has_compact_support_iff_eventually_eq hasCompactSupport_iff_eventuallyEq
-/

#print HasCompactMulSupport.isCompact_range /-
@[to_additive]
theorem HasCompactMulSupport.isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  by
  cases' range_eq_image_mulTSupport_or f with h2 h2 <;> rw [h2]
  exacts [h.image hf, (h.image hf).insert 1]
#align has_compact_mul_support.is_compact_range HasCompactMulSupport.isCompact_range
#align has_compact_support.is_compact_range HasCompactSupport.isCompact_range
-/

#print HasCompactMulSupport.mono' /-
@[to_additive]
theorem HasCompactMulSupport.mono' {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulTSupport f) : HasCompactMulSupport f' :=
  IsCompact.of_isClosed_subset hf isClosed_closure <| closure_minimal hff' isClosed_closure
#align has_compact_mul_support.mono' HasCompactMulSupport.mono'
#align has_compact_support.mono' HasCompactSupport.mono'
-/

#print HasCompactMulSupport.mono /-
@[to_additive]
theorem HasCompactMulSupport.mono {f' : α → γ} (hf : HasCompactMulSupport f)
    (hff' : mulSupport f' ⊆ mulSupport f) : HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure
#align has_compact_mul_support.mono HasCompactMulSupport.mono
#align has_compact_support.mono HasCompactSupport.mono
-/

#print HasCompactMulSupport.comp_left /-
@[to_additive]
theorem HasCompactMulSupport.comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mulSupport_comp_subset hg f
#align has_compact_mul_support.comp_left HasCompactMulSupport.comp_left
#align has_compact_support.comp_left HasCompactSupport.comp_left
-/

#print hasCompactMulSupport_comp_left /-
@[to_additive]
theorem hasCompactMulSupport_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mul_support_comp_eq g (@hg) f]
#align has_compact_mul_support_comp_left hasCompactMulSupport_comp_left
#align has_compact_support_comp_left hasCompactSupport_comp_left
-/

#print HasCompactMulSupport.comp_closedEmbedding /-
@[to_additive]
theorem HasCompactMulSupport.comp_closedEmbedding (hf : HasCompactMulSupport f) {g : α' → α}
    (hg : ClosedEmbedding g) : HasCompactMulSupport (f ∘ g) :=
  by
  rw [hasCompactMulSupport_def, Function.mulSupport_comp_eq_preimage]
  refine' IsCompact.of_isClosed_subset (hg.is_compact_preimage hf) isClosed_closure _
  rw [hg.to_embedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)
#align has_compact_mul_support.comp_closed_embedding HasCompactMulSupport.comp_closedEmbedding
#align has_compact_support.comp_closed_embedding HasCompactSupport.comp_closedEmbedding
-/

#print HasCompactMulSupport.comp₂_left /-
@[to_additive]
theorem HasCompactMulSupport.comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) :=
  by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] using fun x hx hx₂ => by simp_rw [hx, hx₂, Pi.one_apply, hm]
#align has_compact_mul_support.comp₂_left HasCompactMulSupport.comp₂_left
#align has_compact_support.comp₂_left HasCompactSupport.comp₂_left
-/

end

section Monoid

variable [TopologicalSpace α] [Monoid β]

variable {f f' : α → β} {x : α}

#print HasCompactMulSupport.mul /-
@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := by apply hf.comp₂_left hf' (mul_one 1)
#align has_compact_mul_support.mul HasCompactMulSupport.mul
#align has_compact_support.add HasCompactSupport.add
-/

-- `by apply` speeds up elaboration
end Monoid

section DistribMulAction

variable [TopologicalSpace α] [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]

variable {f : α → R} {f' : α → M} {x : α}

#print HasCompactSupport.smul_left /-
theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left HasCompactSupport.smul_left
-/

end DistribMulAction

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]

variable {f : α → R} {f' : α → M} {x : α}

#print HasCompactSupport.smul_right /-
theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]
#align has_compact_support.smul_right HasCompactSupport.smul_right
-/

#print HasCompactSupport.smul_left' /-
theorem HasCompactSupport.smul_left' (hf : HasCompactSupport f') : HasCompactSupport (f • f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left' HasCompactSupport.smul_left'
-/

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]

variable {f f' : α → β} {x : α}

#print HasCompactSupport.mul_right /-
theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, MulZeroClass.zero_mul]
#align has_compact_support.mul_right HasCompactSupport.mul_right
-/

#print HasCompactSupport.mul_left /-
theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') :=
  by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, MulZeroClass.mul_zero]
#align has_compact_support.mul_left HasCompactSupport.mul_left
-/

end MulZeroClass

namespace LocallyFinite

variable {ι : Type _} {U : ι → Set X} [TopologicalSpace X] [One R]

#print LocallyFinite.exists_finset_nhd_mulSupport_subset /-
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive
      " If a family of functions `f` has locally-finite support, subordinate to a family of open sets,\nthen for any point we can find a neighbourhood on which only finitely-many members of `f` are\nnon-zero. "]
theorem exists_finset_nhd_mulSupport_subset {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι) (n : Set X) (hn₁ : n ∈ 𝓝 x) (hn₂ : n ⊆ ⋂ i ∈ is, U i),
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is :=
  by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
  let is := hnf.to_finset.filter fun i => x ∈ U i
  let js := hnf.to_finset.filter fun j => x ∉ U j
  refine'
    ⟨is, (n ∩ ⋂ j ∈ js, mulTSupport (f j)ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn _) _,
      inter_subset_right _ _, fun z hz => _⟩
  ·
    exact
      (bInter_finset_mem js).mpr fun j hj =>
        IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
          (Set.not_mem_subset (hso j) (finset.mem_filter.mp hj).2)
  · exact (bInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (finset.mem_filter.mp hi).2
  · have hzn : z ∈ n := by
      rw [inter_assoc] at hz
      exact mem_of_mem_inter_left hz
    replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
    simp only [Finset.mem_filter, finite.mem_to_finset, mem_set_of_eq, mem_Inter, and_imp] at hz
    suffices (mul_support fun i => f i z) ⊆ hnf.to_finset
      by
      refine' hnf.to_finset.subset_coe_filter_of_subset_forall _ this fun i hi => _
      specialize hz i ⟨z, ⟨hi, hzn⟩⟩
      contrapose hz
      simp [hz, subset_mulTSupport (f i) hi]
    intro i hi
    simp only [finite.coe_to_finset, mem_set_of_eq]
    exact ⟨z, ⟨hi, hzn⟩⟩
#align locally_finite.exists_finset_nhd_mul_support_subset LocallyFinite.exists_finset_nhd_mulSupport_subset
#align locally_finite.exists_finset_nhd_support_subset LocallyFinite.exists_finset_nhd_support_subset
-/

end LocallyFinite

