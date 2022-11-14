/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
import Mathbin.Topology.Separation

/-!
# The topological support of a function

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

open TopologicalSpace

variable {X α α' β γ δ M E R : Type _}

section One

variable [One α]

variable [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive
      " The topological support of a function is the closure of its support. i.e. the closure of the\n  set of all elements where the function is nonzero. "]
def mulTsupport (f : X → α) : Set X :=
  closure (mulSupport f)
#align mul_tsupport mulTsupport

@[to_additive]
theorem subset_mul_tsupport (f : X → α) : mulSupport f ⊆ mulTsupport f :=
  subset_closure
#align subset_mul_tsupport subset_mul_tsupport

@[to_additive]
theorem isClosedMulTsupport (f : X → α) : IsClosed (mulTsupport f) :=
  isClosedClosure
#align is_closed_mul_tsupport isClosedMulTsupport

@[to_additive]
theorem mul_tsupport_eq_empty_iff {f : X → α} : mulTsupport f = ∅ ↔ f = 1 := by
  rw [mulTsupport, closure_empty_iff, mul_support_eq_empty_iff]
#align mul_tsupport_eq_empty_iff mul_tsupport_eq_empty_iff

@[to_additive]
theorem image_eq_zero_of_nmem_mul_tsupport {f : X → α} {x : X} (hx : x ∉ mulTsupport f) : f x = 1 :=
  mul_support_subset_iff'.mp (subset_mul_tsupport f) x hx
#align image_eq_zero_of_nmem_mul_tsupport image_eq_zero_of_nmem_mul_tsupport

@[to_additive]
theorem range_subset_insert_image_mul_tsupport (f : X → α) : range f ⊆ insert 1 (f '' mulTsupport f) :=
  (range_subset_insert_image_mul_support f).trans <| insert_subset_insert <| image_subset _ subset_closure
#align range_subset_insert_image_mul_tsupport range_subset_insert_image_mul_tsupport

@[to_additive]
theorem range_eq_image_mul_tsupport_or (f : X → α) :
    range f = f '' mulTsupport f ∨ range f = insert 1 (f '' mulTsupport f) :=
  (wcovby_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mul_tsupport f)
#align range_eq_image_mul_tsupport_or range_eq_image_mul_tsupport_or

theorem tsupport_mul_subset_left {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)
#align tsupport_mul_subset_left tsupport_mul_subset_left

theorem tsupport_mul_subset_right {α : Type _} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)
#align tsupport_mul_subset_right tsupport_mul_subset_right

end One

theorem tsupport_smul_subset_left {M α} [TopologicalSpace X] [Zero M] [Zero α] [SmulWithZero M α] (f : X → M)
    (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g
#align tsupport_smul_subset_left tsupport_smul_subset_left

section

variable [TopologicalSpace α] [TopologicalSpace α']

variable [One β] [One γ] [One δ]

variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

@[to_additive]
theorem not_mem_mul_tsupport_iff_eventually_eq : x ∉ mulTsupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTsupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty,
    disjoint_mul_support_iff, eventually_eq_iff_exists_mem]
#align not_mem_mul_tsupport_iff_eventually_eq not_mem_mul_tsupport_iff_eventually_eq

@[to_additive]
theorem continuous_of_mul_tsupport [TopologicalSpace β] {f : α → β} (hf : ∀ x ∈ mulTsupport f, ContinuousAt f x) :
    Continuous f :=
  continuous_iff_continuous_at.2 fun x =>
    ((em _).elim (hf x)) fun hx =>
      (@continuous_at_const _ _ _ _ _ 1).congr (not_mem_mul_tsupport_iff_eventually_eq.mp hx).symm
#align continuous_of_mul_tsupport continuous_of_mul_tsupport

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive
      " A function `f` *has compact support* or is *compactly supported* if the closure of the support\nof `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a compact\nset. "]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTsupport f)
#align has_compact_mul_support HasCompactMulSupport

@[to_additive]
theorem has_compact_mul_support_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by rfl
#align has_compact_mul_support_def has_compact_mul_support_def

/- ./././Mathport/Syntax/Translate/Basic.lean:610:2: warning: expanding binder collection (x «expr ∉ » K) -/
@[to_additive]
theorem exists_compact_iff_has_compact_mul_support [T2Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ (x) (_ : x ∉ K), f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mul_support, ← mem_compl_iff, ← subset_def, compl_subset_compl, has_compact_mul_support_def,
    exists_compact_superset_iff]
#align exists_compact_iff_has_compact_mul_support exists_compact_iff_has_compact_mul_support

/- ./././Mathport/Syntax/Translate/Basic.lean:610:2: warning: expanding binder collection (x «expr ∉ » K) -/
@[to_additive]
theorem HasCompactMulSupport.intro [T2Space α] {K : Set α} (hK : IsCompact K) (hfK : ∀ (x) (_ : x ∉ K), f x = 1) :
    HasCompactMulSupport f :=
  exists_compact_iff_has_compact_mul_support.mp ⟨K, hK, hfK⟩
#align has_compact_mul_support.intro HasCompactMulSupport.intro

@[to_additive]
theorem HasCompactMulSupport.is_compact (hf : HasCompactMulSupport f) : IsCompact (mulTsupport f) :=
  hf
#align has_compact_mul_support.is_compact HasCompactMulSupport.is_compact

@[to_additive]
theorem has_compact_mul_support_iff_eventually_eq : HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  ⟨fun h =>
    mem_coclosed_compact.mpr
      ⟨mulTsupport f, isClosedMulTsupport _, h, fun x => not_imp_comm.mpr fun hx => subset_mul_tsupport f hx⟩,
    fun h =>
    let ⟨C, hC⟩ := mem_coclosed_compact'.mp h
    is_compact_of_is_closed_subset hC.2.1 (isClosedMulTsupport _) (closure_minimal hC.2.2 hC.1)⟩
#align has_compact_mul_support_iff_eventually_eq has_compact_mul_support_iff_eventually_eq

@[to_additive]
theorem HasCompactMulSupport.is_compact_range [TopologicalSpace β] (h : HasCompactMulSupport f) (hf : Continuous f) :
    IsCompact (range f) := by
  cases' range_eq_image_mul_tsupport_or f with h2 h2 <;> rw [h2]
  exacts[h.image hf, (h.image hf).insert 1]
#align has_compact_mul_support.is_compact_range HasCompactMulSupport.is_compact_range

@[to_additive]
theorem HasCompactMulSupport.mono' {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulTsupport f) :
    HasCompactMulSupport f' :=
  is_compact_of_is_closed_subset hf isClosedClosure <| closure_minimal hff' isClosedClosure
#align has_compact_mul_support.mono' HasCompactMulSupport.mono'

@[to_additive]
theorem HasCompactMulSupport.mono {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulSupport f) :
    HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure
#align has_compact_mul_support.mono HasCompactMulSupport.mono

@[to_additive]
theorem HasCompactMulSupport.comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) : HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mul_support_comp_subset hg f
#align has_compact_mul_support.comp_left HasCompactMulSupport.comp_left

@[to_additive]
theorem has_compact_mul_support_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [has_compact_mul_support_def, mul_support_comp_eq g (@hg) f]
#align has_compact_mul_support_comp_left has_compact_mul_support_comp_left

@[to_additive]
theorem HasCompactMulSupport.comp_closed_embedding (hf : HasCompactMulSupport f) {g : α' → α} (hg : ClosedEmbedding g) :
    HasCompactMulSupport (f ∘ g) := by
  rw [has_compact_mul_support_def, Function.mul_support_comp_eq_preimage]
  refine' is_compact_of_is_closed_subset (hg.is_compact_preimage hf) isClosedClosure _
  rw [hg.to_embedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)
#align has_compact_mul_support.comp_closed_embedding HasCompactMulSupport.comp_closed_embedding

@[to_additive]
theorem HasCompactMulSupport.comp₂_left (hf : HasCompactMulSupport f) (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [has_compact_mul_support_iff_eventually_eq] at hf hf₂⊢
  filter_upwards [hf, hf₂] using fun x hx hx₂ => by simp_rw [hx, hx₂, Pi.one_apply, hm]
#align has_compact_mul_support.comp₂_left HasCompactMulSupport.comp₂_left

end

section Monoid

variable [TopologicalSpace α] [Monoid β]

variable {f f' : α → β} {x : α}

@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := by apply hf.comp₂_left hf' (mul_one 1)
#align has_compact_mul_support.mul HasCompactMulSupport.mul

-- `by apply` speeds up elaboration
end Monoid

section DistribMulAction

variable [TopologicalSpace α] [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]

variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left HasCompactSupport.smul_left

end DistribMulAction

section SmulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SmulWithZero R M]

variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]
#align has_compact_support.smul_right HasCompactSupport.smul_right

theorem HasCompactSupport.smul_left' (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]
#align has_compact_support.smul_left' HasCompactSupport.smul_left'

end SmulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]

variable {f f' : α → β} {x : α}

theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]
#align has_compact_support.mul_right HasCompactSupport.mul_right

theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine' hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]
#align has_compact_support.mul_left HasCompactSupport.mul_left

end MulZeroClass

namespace LocallyFinite

variable {ι : Type _} {U : ι → Set X} [TopologicalSpace X] [One R]

/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive
      " If a family of functions `f` has locally-finite support, subordinate to a family of open sets,\nthen for any point we can find a neighbourhood on which only finitely-many members of `f` are\nnon-zero. "]
theorem exists_finset_nhd_mul_support_subset {f : ι → X → R} (hlf : LocallyFinite fun i => mulSupport (f i))
    (hso : ∀ i, mulTsupport (f i) ⊆ U i) (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι)(n : Set X)(hn₁ : n ∈ 𝓝 x)(hn₂ : n ⊆ ⋂ i ∈ is, U i), ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is :=
  by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical let is := hnf.to_finset.filter fun i => x ∈ U i
    refine'
      ⟨is, (n ∩ ⋂ j ∈ js, mulTsupport (f j)ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn _) _, inter_subset_right _ _,
        fun z hz => _⟩
    · exact (bInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (finset.mem_filter.mp hi).2
      
#align locally_finite.exists_finset_nhd_mul_support_subset LocallyFinite.exists_finset_nhd_mul_support_subset

end LocallyFinite

