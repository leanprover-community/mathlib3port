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

open_locale TopologicalSpace

variable {X α α' β γ δ M E R : Type _}

section One

variable [One α]

variable [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
  set of all elements where the function is not equal to 1. -/
@[to_additive
      " The topological support of a function is the closure of its support. i.e. the closure of the\n  set of all elements where the function is nonzero. "]
def MulTsupport (f : X → α) : Set X :=
  Closure (MulSupport f)

@[to_additive]
theorem subset_mul_tsupport (f : X → α) : MulSupport f ⊆ MulTsupport f :=
  subset_closure

@[to_additive]
theorem is_closed_mul_tsupport (f : X → α) : IsClosed (MulTsupport f) :=
  is_closed_closure

@[to_additive]
theorem mul_tsupport_eq_empty_iff {f : X → α} : MulTsupport f = ∅ ↔ f = 1 := by
  rw [MulTsupport, closure_empty_iff, mul_support_eq_empty_iff]

@[to_additive]
theorem image_eq_zero_of_nmem_mul_tsupport {f : X → α} {x : X} (hx : x ∉ MulTsupport f) : f x = 1 :=
  mul_support_subset_iff'.mp (subset_mul_tsupport f) x hx

end One

section

variable [TopologicalSpace α] [TopologicalSpace α']

variable [One β] [One γ] [One δ]

variable {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ} {x : α}

@[to_additive]
theorem not_mem_closure_mul_support_iff_eventually_eq : (x ∉ MulTsupport f) ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [MulTsupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty,
    disjoint_mul_support_iff, eventually_eq_iff_exists_mem]

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive
      " A function `f` *has compact support* or is *compactly supported* if the closure of the support\nof `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a compact\nset. "]
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (MulTsupport f)

@[to_additive]
theorem has_compact_mul_support_def : HasCompactMulSupport f ↔ IsCompact (Closure (MulSupport f)) := by
  rfl

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (x «expr ∉ » K)
@[to_additive]
theorem exists_compact_iff_has_compact_mul_support [T2Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ x _ : x ∉ K, f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← nmem_mul_support, ← mem_compl_iff, ← subset_def, compl_subset_compl, has_compact_mul_support_def,
    exists_compact_superset_iff]

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (x «expr ∉ » K)
@[to_additive]
theorem HasCompactMulSupport.intro [T2Space α] {K : Set α} (hK : IsCompact K) (hfK : ∀ x _ : x ∉ K, f x = 1) :
    HasCompactMulSupport f :=
  exists_compact_iff_has_compact_mul_support.mp ⟨K, hK, hfK⟩

@[to_additive]
theorem HasCompactMulSupport.is_compact (hf : HasCompactMulSupport f) : IsCompact (MulTsupport f) :=
  hf

@[to_additive]
theorem has_compact_mul_support_iff_eventually_eq : HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  ⟨fun h =>
    mem_coclosed_compact.mpr
      ⟨MulTsupport f, is_closed_mul_tsupport _, h, fun x => not_imp_comm.mpr fun hx => subset_mul_tsupport f hx⟩,
    fun h =>
    let ⟨C, hC⟩ := mem_coclosed_compact'.mp h
    compact_of_is_closed_subset hC.2.1 (is_closed_mul_tsupport _) (closure_minimal hC.2.2 hC.1)⟩

@[to_additive]
theorem HasCompactMulSupport.mono' {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : MulSupport f' ⊆ MulTsupport f) :
    HasCompactMulSupport f' :=
  compact_of_is_closed_subset hf is_closed_closure <| closure_minimal hff' is_closed_closure

@[to_additive]
theorem HasCompactMulSupport.mono {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : MulSupport f' ⊆ MulSupport f) :
    HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure

@[to_additive]
theorem HasCompactMulSupport.comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) : HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mul_support_comp_subset hg f

@[to_additive]
theorem has_compact_mul_support_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [has_compact_mul_support_def, mul_support_comp_eq g (@hg) f]

@[to_additive]
theorem HasCompactMulSupport.comp_closed_embedding (hf : HasCompactMulSupport f) {g : α' → α} (hg : ClosedEmbedding g) :
    HasCompactMulSupport (f ∘ g) := by
  rw [has_compact_mul_support_def, Function.mul_support_comp_eq_preimage]
  refine' compact_of_is_closed_subset (hg.is_compact_preimage hf) is_closed_closure _
  rw [hg.to_embedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]
theorem HasCompactMulSupport.comp₂_left (hf : HasCompactMulSupport f) (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [has_compact_mul_support_iff_eventually_eq] at hf hf₂⊢
  filter_upwards [hf, hf₂] using fun x hx hx₂ => by
    simp_rw [hx, hx₂, Pi.one_apply, hm]

end

section Monoidₓ

variable [TopologicalSpace α] [Monoidₓ β]

variable {f f' : α → β} {x : α}

@[to_additive]
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := by
  apply hf.comp₂_left hf' (mul_oneₓ 1)

-- `by apply` speeds up elaboration
end Monoidₓ

section DistribMulAction

variable [TopologicalSpace α] [MonoidWithZeroₓ R] [AddMonoidₓ M] [DistribMulAction R M]

variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine'
    hf.mono fun x hx => by
      simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

end DistribMulAction

section SmulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SmulWithZero R M]

variable {f : α → R} {f' : α → M} {x : α}

theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine'
    hf.mono fun x hx => by
      simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

theorem HasCompactSupport.smul_left' (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine'
    hf.mono fun x hx => by
      simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero']

end SmulWithZero

section MulZeroClassₓ

variable [TopologicalSpace α] [MulZeroClassₓ β]

variable {f f' : α → β} {x : α}

theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine'
    hf.mono fun x hx => by
      simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]

theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [has_compact_support_iff_eventually_eq] at hf⊢
  refine'
    hf.mono fun x hx => by
      simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

end MulZeroClassₓ

