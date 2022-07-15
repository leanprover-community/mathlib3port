/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathbin.Data.Finite.Basic
import Mathbin.Data.Set.Finite

/-!
# Finite instances for `set`

This module provides ways to go between `set.finite` and `finite` and also provides a number
of `finite` instances for basic set constructions such as unions, intersections, and so on.

## Main definitions

* `set.finite_of_finite` creates a `set.finite` proof from a `finite` instance
* `set.finite.finite` creates a `finite` instance from a `set.finite` proof
* `finite.set.subset` for finiteness of subsets of a finite set

## Tags

finiteness, finite sets

-/


open Set

open Classical

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

/-- Constructor for `set.finite` using a `finite` instance. -/
theorem Set.finite_of_finite (s : Set α) [Finite s] : s.Finite :=
  ⟨Fintype.ofFinite s⟩

/-- Projection of `set.finite` to its `finite` instance.
This is intended to be used with dot notation.
See also `set.finite.fintype`. -/
@[nolint dup_namespace]
protected theorem Set.Finite.finite {s : Set α} (h : s.Finite) : Finite s :=
  Finite.of_fintype h.Fintype

theorem Set.finite_iff_finite {s : Set α} : s.Finite ↔ Finite s :=
  ⟨fun h => h.Finite, fun h => Set.finite_of_finite s⟩

/-- Construct a `finite` instance for a `set` from a `finset` with the same elements. -/
protected theorem Finite.of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Finite p :=
  Finite.of_fintype (Fintype.ofFinset s H)

/-! ### Finite instances

There is seemingly some overlap between the following instances and the `fintype` instances
in `data.set.finite`. While every `fintype` instance gives a `finite` instance, those
instances that depend on `fintype` or `decidable` instances need an additional `finite` instance
to be able to generally apply.

Some set instances do not appear here since they are consequences of others, for example
`subtype.finite` for subsets of a finite type.
-/


namespace Finite.Set

example {s : Set α} [Finite α] : Finite s :=
  inferInstance

example : Finite (∅ : Set α) :=
  inferInstance

example (a : α) : Finite ({a} : Set α) :=
  inferInstance

instance finite_union (s t : Set α) [Finite s] [Finite t] : Finite (s ∪ t : Set α) := by
  have := Fintype.ofFinite s
  have := Fintype.ofFinite t
  infer_instance

instance finite_sep (s : Set α) (p : α → Prop) [Finite s] : Finite ({ a ∈ s | p a } : Set α) := by
  have := Fintype.ofFinite s
  infer_instance

protected theorem subset (s : Set α) {t : Set α} [Finite s] (h : t ⊆ s) : Finite t := by
  rw [eq_sep_of_subset h]
  infer_instance

instance finite_inter_of_right (s t : Set α) [Finite t] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset t (inter_subset_right s t)

instance finite_inter_of_left (s t : Set α) [Finite s] : Finite (s ∩ t : Set α) :=
  Finite.Set.subset s (inter_subset_left s t)

instance finite_diff (s t : Set α) [Finite s] : Finite (s \ t : Set α) :=
  Finite.Set.subset s (diff_subset s t)

instance finite_Union [Finite ι] (f : ι → Set α) [∀ i, Finite (f i)] : Finite (⋃ i, f i) := by
  convert_to Finite (⋃ i : Plift ι, f i.down)
  · congr
    ext
    simp
    
  have := Fintype.ofFinite (Plift ι)
  have := fun i => Fintype.ofFinite (f i)
  infer_instance

instance finite_sUnion {s : Set (Set α)} [Finite s] [H : ∀ t : s, Finite (t : Set α)] : Finite (⋃₀s) := by
  rw [sUnion_eq_Union]
  exact @Finite.Set.finite_Union _ _ _ _ H

theorem finite_bUnion {ι : Type _} (s : Set ι) [Finite s] (t : ι → Set α) (H : ∀, ∀ i ∈ s, ∀, Finite (t i)) :
    Finite (⋃ x ∈ s, t x) := by
  convert_to Finite (⋃ x : s, t x)
  · congr 1
    ext
    simp
    
  have : ∀ i : s, Finite (t i) := fun i => H i i.property
  infer_instance

instance finite_bUnion' {ι : Type _} (s : Set ι) [Finite s] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ x ∈ s, t x) :=
  finite_bUnion s t fun i h => inferInstance

/-- Example: `finite (⋃ (i < n), f i)` where `f : ℕ → set α` and `[∀ i, finite (f i)]`
(when given instances from `data.nat.interval`).
-/
instance finite_bUnion'' {ι : Type _} (p : ι → Prop) [h : Finite { x | p x }] (t : ι → Set α) [∀ i, Finite (t i)] :
    Finite (⋃ (x) (h : p x), t x) :=
  @Finite.Set.finite_bUnion' _ _ (SetOf p) h t _

instance finite_Inter {ι : Sort _} [Nonempty ι] (t : ι → Set α) [∀ i, Finite (t i)] : Finite (⋂ i, t i) :=
  Finite.Set.subset (t <| Classical.arbitrary ι) (Inter_subset _ _)

instance finite_insert (a : α) (s : Set α) [Finite s] : Finite (insert a s : Set α) :=
  ((Set.finite_of_finite s).insert a).Finite

instance finite_image (s : Set α) (f : α → β) [Finite s] : Finite (f '' s) :=
  ((Set.finite_of_finite s).Image f).Finite

instance finite_range (f : ι → α) [Finite ι] : Finite (Range f) := by
  have := Fintype.ofFinite (Plift ι)
  infer_instance

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: unsupported set replacement {(f x) | x : α}
instance finite_replacement [Finite α] (f : α → β) :
    Finite "./././Mathport/Syntax/Translate/Basic.lean:1087:4: unsupported set replacement {(f x) | x : α}" :=
  Finite.Set.finite_range f

instance finite_prod (s : Set α) (t : Set β) [Finite s] [Finite t] : Finite (s ×ˢ t : Set (α × β)) := by
  have := Fintype.ofFinite s
  have := Fintype.ofFinite t
  infer_instance

instance finite_image2 (f : α → β → γ) (s : Set α) (t : Set β) [Finite s] [Finite t] : Finite (Image2 f s t : Set γ) :=
  by
  rw [← image_prod]
  infer_instance

instance finite_seq (f : Set (α → β)) (s : Set α) [Finite f] [Finite s] : Finite (f.seq s) := by
  rw [seq_def]
  infer_instance

end Finite.Set

/-! ### Non-instances -/


theorem Set.finite_univ_iff : Finite (Set.Univ : Set α) ↔ Finite α :=
  (Equivₓ.Set.univ α).finite_iff

theorem Finite.of_finite_univ [Finite ↥(Univ : Set α)] : Finite α :=
  Set.finite_univ_iff.mp ‹_›

theorem Finite.Set.finite_of_finite_image (s : Set α) {f : α → β} (h : s.InjOn f) [Finite (f '' s)] : Finite s :=
  Finite.of_equiv _ (Equivₓ.ofBijective _ h.bij_on_image.Bijective).symm

theorem Finite.of_injective_finite_range {f : α → β} (hf : Function.Injective f) [Finite (Range f)] : Finite α := by
  refine' Finite.of_injective (Set.rangeFactorization f) fun x y h => hf _
  simpa only [← range_factorization_coe] using congr_arg (coe : range f → β) h

