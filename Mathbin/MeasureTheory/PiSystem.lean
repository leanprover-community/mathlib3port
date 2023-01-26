/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Martin Zinkevich, Rémy Degenne

! This file was ported from Lean 3 source module measure_theory.pi_system
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Encodable.Lattice
import Mathbin.MeasureTheory.MeasurableSpaceDef

/-!
# Induction principles for measurable sets, related to π-systems and λ-systems.

## Main statements

* The main theorem of this file is Dynkin's π-λ theorem, which appears
  here as an induction principle `induction_on_inter`. Suppose `s` is a
  collection of subsets of `α` such that the intersection of two members
  of `s` belongs to `s` whenever it is nonempty. Let `m` be the σ-algebra
  generated by `s`. In order to check that a predicate `C` holds on every
  member of `m`, it suffices to check that `C` holds on the members of `s` and
  that `C` is preserved by complementation and *disjoint* countable
  unions.

* The proof of this theorem relies on the notion of `is_pi_system`, i.e., a collection of sets
  which is closed under binary non-empty intersections. Note that this is a small variation around
  the usual notion in the literature, which often requires that a π-system is non-empty, and closed
  also under disjoint intersections. This variation turns out to be convenient for the
  formalization.

* The proof of Dynkin's π-λ theorem also requires the notion of `dynkin_system`, i.e., a collection
  of sets which contains the empty set, is closed under complementation and under countable union
  of pairwise disjoint sets. The disjointness condition is the only difference with `σ`-algebras.

* `generate_pi_system g` gives the minimal π-system containing `g`.
  This can be considered a Galois insertion into both measurable spaces and sets.

* `generate_from_generate_pi_system_eq` proves that if you start from a collection of sets `g`,
  take the generated π-system, and then the generated σ-algebra, you get the same result as
  the σ-algebra generated from `g`. This is useful because there are connections between
  independent sets that are π-systems and the generated independent spaces.

* `mem_generate_pi_system_Union_elim` and `mem_generate_pi_system_Union_elim'` show that any
  element of the π-system generated from the union of a set of π-systems can be
  represented as the intersection of a finite number of elements from these sets.

* `pi_Union_Inter` defines a new π-system from a family of π-systems `π : ι → set (set α)` and a
  set of indices `S : set ι`. `pi_Union_Inter π S` is the set of sets that can be written
  as `⋂ x ∈ t, f x` for some finset `t ∈ S` and sets `f x ∈ π x`.

## Implementation details

* `is_pi_system` is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on the subtype corresponding to `is_pi_system`.
-/


open MeasurableSpace Set

open Classical MeasureTheory

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (s t «expr ∈ » C) -/
/-- A π-system is a collection of subsets of `α` that is closed under binary intersection of
  non-disjoint sets. Usually it is also required that the collection is nonempty, but we don't do
  that here. -/
def IsPiSystem {α} (C : Set (Set α)) : Prop :=
  ∀ (s) (_ : s ∈ C) (t) (_ : t ∈ C), (s ∩ t : Set α).Nonempty → s ∩ t ∈ C
#align is_pi_system IsPiSystem

namespace MeasurableSpace

theorem isPiSystem_measurableSet {α : Type _} [MeasurableSpace α] :
    IsPiSystem { s : Set α | MeasurableSet s } := fun s hs t ht _ => hs.inter ht
#align measurable_space.is_pi_system_measurable_set MeasurableSpace.isPiSystem_measurableSet

end MeasurableSpace

theorem IsPiSystem.singleton {α} (S : Set α) : IsPiSystem ({S} : Set (Set α)) :=
  by
  intro s h_s t h_t h_ne
  rw [Set.mem_singleton_iff.1 h_s, Set.mem_singleton_iff.1 h_t, Set.inter_self,
    Set.mem_singleton_iff]
#align is_pi_system.singleton IsPiSystem.singleton

theorem IsPiSystem.insert_empty {α} {S : Set (Set α)} (h_pi : IsPiSystem S) :
    IsPiSystem (insert ∅ S) := by
  intro s hs t ht hst
  cases hs
  · simp [hs]
  · cases ht
    · simp [ht]
    · exact Set.mem_insert_of_mem _ (h_pi s hs t ht hst)
#align is_pi_system.insert_empty IsPiSystem.insert_empty

theorem IsPiSystem.insert_univ {α} {S : Set (Set α)} (h_pi : IsPiSystem S) :
    IsPiSystem (insert Set.univ S) := by
  intro s hs t ht hst
  cases hs
  · cases ht <;> simp [hs, ht]
  · cases ht
    · simp [hs, ht]
    · exact Set.mem_insert_of_mem _ (h_pi s hs t ht hst)
#align is_pi_system.insert_univ IsPiSystem.insert_univ

theorem IsPiSystem.comap {α β} {S : Set (Set β)} (h_pi : IsPiSystem S) (f : α → β) :
    IsPiSystem { s : Set α | ∃ t ∈ S, f ⁻¹' t = s } :=
  by
  rintro _ ⟨s, hs_mem, rfl⟩ _ ⟨t, ht_mem, rfl⟩ hst
  rw [← Set.preimage_inter] at hst⊢
  refine' ⟨s ∩ t, h_pi s hs_mem t ht_mem _, rfl⟩
  by_contra
  rw [Set.not_nonempty_iff_eq_empty] at h
  rw [h] at hst
  simpa using hst
#align is_pi_system.comap IsPiSystem.comap

theorem isPiSystem_unionᵢ_of_directed_le {α ι} (p : ι → Set (Set α)) (hp_pi : ∀ n, IsPiSystem (p n))
    (hp_directed : Directed (· ≤ ·) p) : IsPiSystem (⋃ n, p n) :=
  by
  intro t1 ht1 t2 ht2 h
  rw [Set.mem_unionᵢ] at ht1 ht2⊢
  cases' ht1 with n ht1
  cases' ht2 with m ht2
  obtain ⟨k, hpnk, hpmk⟩ : ∃ k, p n ≤ p k ∧ p m ≤ p k := hp_directed n m
  exact ⟨k, hp_pi k t1 (hpnk ht1) t2 (hpmk ht2) h⟩
#align is_pi_system_Union_of_directed_le isPiSystem_unionᵢ_of_directed_le

theorem isPiSystem_unionᵢ_of_monotone {α ι} [SemilatticeSup ι] (p : ι → Set (Set α))
    (hp_pi : ∀ n, IsPiSystem (p n)) (hp_mono : Monotone p) : IsPiSystem (⋃ n, p n) :=
  isPiSystem_unionᵢ_of_directed_le p hp_pi (Monotone.directed_le hp_mono)
#align is_pi_system_Union_of_monotone isPiSystem_unionᵢ_of_monotone

section Order

variable {α : Type _} {ι ι' : Sort _} [LinearOrder α]

theorem isPiSystem_image_iio (s : Set α) : IsPiSystem (Iio '' s) :=
  by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
  exact ⟨a ⊓ b, inf_ind a b ha hb, Iio_inter_Iio.symm⟩
#align is_pi_system_image_Iio isPiSystem_image_iio

theorem isPiSystem_iio : IsPiSystem (range Iio : Set (Set α)) :=
  @image_univ α _ Iio ▸ isPiSystem_image_iio univ
#align is_pi_system_Iio isPiSystem_iio

theorem isPiSystem_image_ioi (s : Set α) : IsPiSystem (Ioi '' s) :=
  @isPiSystem_image_iio αᵒᵈ _ s
#align is_pi_system_image_Ioi isPiSystem_image_ioi

theorem isPiSystem_ioi : IsPiSystem (range Ioi : Set (Set α)) :=
  @image_univ α _ Ioi ▸ isPiSystem_image_ioi univ
#align is_pi_system_Ioi isPiSystem_ioi

theorem isPiSystem_Ixx_mem {Ixx : α → α → Set α} {p : α → α → Prop}
    (Hne : ∀ {a b}, (Ixx a b).Nonempty → p a b)
    (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂)) (s t : Set α) :
    IsPiSystem { S | ∃ l ∈ s, ∃ u ∈ t, ∃ hlu : p l u, Ixx l u = S } :=
  by
  rintro _ ⟨l₁, hls₁, u₁, hut₁, hlu₁, rfl⟩ _ ⟨l₂, hls₂, u₂, hut₂, hlu₂, rfl⟩
  simp only [Hi, ← sup_eq_max, ← inf_eq_min]
  exact fun H => ⟨l₁ ⊔ l₂, sup_ind l₁ l₂ hls₁ hls₂, u₁ ⊓ u₂, inf_ind u₁ u₂ hut₁ hut₂, Hne H, rfl⟩
#align is_pi_system_Ixx_mem isPiSystem_Ixx_mem

theorem isPiSystem_Ixx {Ixx : α → α → Set α} {p : α → α → Prop}
    (Hne : ∀ {a b}, (Ixx a b).Nonempty → p a b)
    (Hi : ∀ {a₁ b₁ a₂ b₂}, Ixx a₁ b₁ ∩ Ixx a₂ b₂ = Ixx (max a₁ a₂) (min b₁ b₂)) (f : ι → α)
    (g : ι' → α) : @IsPiSystem α { S | ∃ (i j : _)(h : p (f i) (g j)), Ixx (f i) (g j) = S } := by
  simpa only [exists_range_iff] using isPiSystem_Ixx_mem (@Hne) (@Hi) (range f) (range g)
#align is_pi_system_Ixx isPiSystem_Ixx

theorem isPiSystem_ioo_mem (s t : Set α) :
    IsPiSystem { S | ∃ l ∈ s, ∃ u ∈ t, ∃ h : l < u, Ioo l u = S } :=
  isPiSystem_Ixx_mem (fun a b ⟨x, hax, hxb⟩ => hax.trans hxb) (fun _ _ _ _ => Ioo_inter_Ioo) s t
#align is_pi_system_Ioo_mem isPiSystem_ioo_mem

theorem isPiSystem_ioo (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ (l u : _)(h : f l < g u), Ioo (f l) (g u) = S } :=
  isPiSystem_Ixx (fun a b ⟨x, hax, hxb⟩ => hax.trans hxb) (fun _ _ _ _ => Ioo_inter_Ioo) f g
#align is_pi_system_Ioo isPiSystem_ioo

theorem isPiSystem_ioc_mem (s t : Set α) :
    IsPiSystem { S | ∃ l ∈ s, ∃ u ∈ t, ∃ h : l < u, Ioc l u = S } :=
  isPiSystem_Ixx_mem (fun a b ⟨x, hax, hxb⟩ => hax.trans_le hxb) (fun _ _ _ _ => Ioc_inter_Ioc) s t
#align is_pi_system_Ioc_mem isPiSystem_ioc_mem

theorem isPiSystem_ioc (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ (i j : _)(h : f i < g j), Ioc (f i) (g j) = S } :=
  isPiSystem_Ixx (fun a b ⟨x, hax, hxb⟩ => hax.trans_le hxb) (fun _ _ _ _ => Ioc_inter_Ioc) f g
#align is_pi_system_Ioc isPiSystem_ioc

theorem isPiSystem_ico_mem (s t : Set α) :
    IsPiSystem { S | ∃ l ∈ s, ∃ u ∈ t, ∃ h : l < u, Ico l u = S } :=
  isPiSystem_Ixx_mem (fun a b ⟨x, hax, hxb⟩ => hax.trans_lt hxb) (fun _ _ _ _ => Ico_inter_Ico) s t
#align is_pi_system_Ico_mem isPiSystem_ico_mem

theorem isPiSystem_ico (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ (i j : _)(h : f i < g j), Ico (f i) (g j) = S } :=
  isPiSystem_Ixx (fun a b ⟨x, hax, hxb⟩ => hax.trans_lt hxb) (fun _ _ _ _ => Ico_inter_Ico) f g
#align is_pi_system_Ico isPiSystem_ico

theorem isPiSystem_icc_mem (s t : Set α) :
    IsPiSystem { S | ∃ l ∈ s, ∃ u ∈ t, ∃ h : l ≤ u, Icc l u = S } :=
  isPiSystem_Ixx_mem (fun a b => nonempty_Icc.1) (fun _ _ _ _ => Icc_inter_Icc) s t
#align is_pi_system_Icc_mem isPiSystem_icc_mem

theorem isPiSystem_icc (f : ι → α) (g : ι' → α) :
    @IsPiSystem α { S | ∃ (i j : _)(h : f i ≤ g j), Icc (f i) (g j) = S } :=
  isPiSystem_Ixx (fun a b => nonempty_Icc.1) (fun _ _ _ _ => Icc_inter_Icc) f g
#align is_pi_system_Icc isPiSystem_icc

end Order

/-- Given a collection `S` of subsets of `α`, then `generate_pi_system S` is the smallest
π-system containing `S`. -/
inductive generatePiSystem {α} (S : Set (Set α)) : Set (Set α)
  | base {s : Set α} (h_s : s ∈ S) : generatePiSystem s
  |
  inter {s t : Set α} (h_s : generatePiSystem s) (h_t : generatePiSystem t)
    (h_nonempty : (s ∩ t).Nonempty) : generatePiSystem (s ∩ t)
#align generate_pi_system generatePiSystem

theorem isPiSystem_generatePiSystem {α} (S : Set (Set α)) : IsPiSystem (generatePiSystem S) :=
  fun s h_s t h_t h_nonempty => generatePiSystem.inter h_s h_t h_nonempty
#align is_pi_system_generate_pi_system isPiSystem_generatePiSystem

theorem subset_generatePiSystem_self {α} (S : Set (Set α)) : S ⊆ generatePiSystem S := fun s =>
  generatePiSystem.base
#align subset_generate_pi_system_self subset_generatePiSystem_self

theorem generatePiSystem_subset_self {α} {S : Set (Set α)} (h_S : IsPiSystem S) :
    generatePiSystem S ⊆ S := by
  intro x h
  induction' h with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u
  · exact h_s
  · exact h_S _ h_s _ h_u h_nonempty
#align generate_pi_system_subset_self generatePiSystem_subset_self

theorem generatePiSystem_eq {α} {S : Set (Set α)} (h_pi : IsPiSystem S) : generatePiSystem S = S :=
  Set.Subset.antisymm (generatePiSystem_subset_self h_pi) (subset_generatePiSystem_self S)
#align generate_pi_system_eq generatePiSystem_eq

theorem generatePiSystem_mono {α} {S T : Set (Set α)} (hST : S ⊆ T) :
    generatePiSystem S ⊆ generatePiSystem T :=
  by
  intro t ht
  induction' ht with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u
  · exact generatePiSystem.base (Set.mem_of_subset_of_mem hST h_s)
  · exact isPiSystem_generatePiSystem T _ h_s _ h_u h_nonempty
#align generate_pi_system_mono generatePiSystem_mono

theorem generatePiSystem_measurableSet {α} [M : MeasurableSpace α] {S : Set (Set α)}
    (h_meas_S : ∀ s ∈ S, MeasurableSet s) (t : Set α) (h_in_pi : t ∈ generatePiSystem S) :
    MeasurableSet t :=
  by
  induction' h_in_pi with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u
  · apply h_meas_S _ h_s
  · apply MeasurableSet.inter h_s h_u
#align generate_pi_system_measurable_set generatePiSystem_measurableSet

theorem generateFrom_measurableSet_of_generatePiSystem {α} {g : Set (Set α)} (t : Set α)
    (ht : t ∈ generatePiSystem g) : measurable_set[generateFrom g] t :=
  @generatePiSystem_measurableSet α (generateFrom g) g
    (fun s h_s_in_g => measurableSet_generateFrom h_s_in_g) t ht
#align generate_from_measurable_set_of_generate_pi_system generateFrom_measurableSet_of_generatePiSystem

theorem generateFrom_generatePiSystem_eq {α} {g : Set (Set α)} :
    generateFrom (generatePiSystem g) = generateFrom g :=
  by
  apply le_antisymm <;> apply generate_from_le
  · exact fun t h_t => generateFrom_measurableSet_of_generatePiSystem t h_t
  · exact fun t h_t => measurable_set_generate_from (generatePiSystem.base h_t)
#align generate_from_generate_pi_system_eq generateFrom_generatePiSystem_eq

/- Every element of the π-system generated by the union of a family of π-systems
is a finite intersection of elements from the π-systems.
For an indexed union version, see `mem_generate_pi_system_Union_elim'`. -/
theorem mem_generatePiSystem_unionᵢ_elim {α β} {g : β → Set (Set α)} (h_pi : ∀ b, IsPiSystem (g b))
    (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b, g b)) :
    ∃ (T : Finset β)(f : β → Set α), (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b :=
  by
  induction' h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t'
  · rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩
    refine' ⟨{b}, fun _ => s, _⟩
    simpa using h_s_in_t'
  · rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩⟩⟩
    use T_s ∪ T_t', fun b : β =>
      if b ∈ T_s then if b ∈ T_t' then f_s b ∩ f_t' b else f_s b
      else if b ∈ T_t' then f_t' b else (∅ : Set α)
    constructor
    · ext a
      simp_rw [Set.mem_inter_iff, Set.mem_interᵢ, Finset.mem_union, or_imp]
      rw [← forall_and]
      constructor <;> intro h1 b <;> by_cases hbs : b ∈ T_s <;> by_cases hbt : b ∈ T_t' <;>
          specialize h1 b <;>
        simp only [hbs, hbt, if_true, if_false, true_imp_iff, and_self_iff, false_imp_iff,
          and_true_iff, true_and_iff] at h1⊢
      all_goals exact h1
    intro b h_b
    split_ifs with hbs hbt hbt
    · refine' h_pi b (f_s b) (h_s b hbs) (f_t' b) (h_t' b hbt) (Set.Nonempty.mono _ h_nonempty)
      exact Set.inter_subset_inter (Set.binterᵢ_subset_of_mem hbs) (Set.binterᵢ_subset_of_mem hbt)
    · exact h_s b hbs
    · exact h_t' b hbt
    · rw [Finset.mem_union] at h_b
      apply False.elim (h_b.elim hbs hbt)
#align mem_generate_pi_system_Union_elim mem_generatePiSystem_unionᵢ_elim

/- Every element of the π-system generated by an indexed union of a family of π-systems
is a finite intersection of elements from the π-systems.
For a total union version, see `mem_generate_pi_system_Union_elim`. -/
theorem mem_generatePiSystem_unionᵢ_elim' {α β} {g : β → Set (Set α)} {s : Set β}
    (h_pi : ∀ b ∈ s, IsPiSystem (g b)) (t : Set α) (h_t : t ∈ generatePiSystem (⋃ b ∈ s, g b)) :
    ∃ (T : Finset β)(f : β → Set α), ↑T ⊆ s ∧ (t = ⋂ b ∈ T, f b) ∧ ∀ b ∈ T, f b ∈ g b :=
  by
  have : t ∈ generatePiSystem (⋃ b : Subtype s, (g ∘ Subtype.val) b) :=
    by
    suffices h1 : (⋃ b : Subtype s, (g ∘ Subtype.val) b) = ⋃ b ∈ s, g b
    · rwa [h1]
    ext x
    simp only [exists_prop, Set.mem_unionᵢ, Function.comp_apply, Subtype.exists, Subtype.coe_mk]
    rfl
  rcases@mem_generatePiSystem_unionᵢ_elim α (Subtype s) (g ∘ Subtype.val)
      (fun b => h_pi b.val b.property) t this with
    ⟨T, ⟨f, ⟨rfl, h_t'⟩⟩⟩
  refine'
    ⟨T.image Subtype.val, Function.extend Subtype.val f fun b : β => (∅ : Set α), by simp, _, _⟩
  · ext a
    constructor <;>
      · simp only [Set.mem_interᵢ, Subtype.forall, Finset.set_binterᵢ_finset_image]
        intro h1 b h_b h_b_in_T
        have h2 := h1 b h_b h_b_in_T
        revert h2
        rw [subtype.val_injective.extend_apply]
        apply id
  · intro b h_b
    simp_rw [Finset.mem_image, exists_prop, Subtype.exists, exists_and_right, exists_eq_right] at
      h_b
    cases h_b
    have h_b_alt : b = (Subtype.mk b h_b_w).val := rfl
    rw [h_b_alt, subtype.val_injective.extend_apply]
    apply h_t'
    apply h_b_h
#align mem_generate_pi_system_Union_elim' mem_generatePiSystem_unionᵢ_elim'

section UnionInter

variable {α ι : Type _}

/-! ### π-system generated by finite intersections of sets of a π-system family -/


/-- From a set of indices `S : set ι` and a family of sets of sets `π : ι → set (set α)`,
define the set of sets that can be written as `⋂ x ∈ t, f x` for some finset `t ⊆ S` and sets
`f x ∈ π x`. If `π` is a family of π-systems, then it is a π-system. -/
def piUnionInter (π : ι → Set (Set α)) (S : Set ι) : Set (Set α) :=
  { s : Set α |
    ∃ (t : Finset ι)(htS : ↑t ⊆ S)(f : ι → Set α)(hf : ∀ x, x ∈ t → f x ∈ π x), s = ⋂ x ∈ t, f x }
#align pi_Union_Inter piUnionInter

theorem piUnionInter_singleton (π : ι → Set (Set α)) (i : ι) : piUnionInter π {i} = π i ∪ {univ} :=
  by
  ext1 s
  simp only [piUnionInter, exists_prop, mem_union]
  refine' ⟨_, fun h => _⟩
  · rintro ⟨t, hti, f, hfπ, rfl⟩
    simp only [subset_singleton_iff, Finset.mem_coe] at hti
    by_cases hi : i ∈ t
    · have ht_eq_i : t = {i} := by
        ext1 x
        rw [Finset.mem_singleton]
        exact ⟨fun h => hti x h, fun h => h.symm ▸ hi⟩
      simp only [ht_eq_i, Finset.mem_singleton, Inter_Inter_eq_left]
      exact Or.inl (hfπ i hi)
    · have ht_empty : t = ∅ := by
        ext1 x
        simp only [Finset.not_mem_empty, iff_false_iff]
        exact fun hx => hi (hti x hx ▸ hx)
      simp only [ht_empty, Inter_false, Inter_univ, Set.mem_singleton univ, or_true_iff]
  · cases' h with hs hs
    · refine' ⟨{i}, _, fun _ => s, ⟨fun x hx => _, _⟩⟩
      · rw [Finset.coe_singleton]
      · rw [Finset.mem_singleton] at hx
        rwa [hx]
      · simp only [Finset.mem_singleton, Inter_Inter_eq_left]
    · refine' ⟨∅, _⟩
      simpa only [Finset.coe_empty, subset_singleton_iff, mem_empty_iff_false, IsEmpty.forall_iff,
        imp_true_iff, Finset.not_mem_empty, Inter_false, Inter_univ, true_and_iff,
        exists_const] using hs
#align pi_Union_Inter_singleton piUnionInter_singleton

theorem piUnionInter_singleton_left (s : ι → Set α) (S : Set ι) :
    piUnionInter (fun i => ({s i} : Set (Set α))) S =
      { s' : Set α | ∃ (t : Finset ι)(htS : ↑t ⊆ S), s' = ⋂ i ∈ t, s i } :=
  by
  ext1 s'
  simp_rw [piUnionInter, Set.mem_singleton_iff, exists_prop, Set.mem_setOf_eq]
  refine' ⟨fun h => _, fun ⟨t, htS, h_eq⟩ => ⟨t, htS, s, fun _ _ => rfl, h_eq⟩⟩
  obtain ⟨t, htS, f, hft_eq, rfl⟩ := h
  refine' ⟨t, htS, _⟩
  congr with (i x)
  simp_rw [Set.mem_interᵢ]
  exact
    ⟨fun h hit => by
      rw [← hft_eq i hit]
      exact h hit, fun h hit => by
      rw [hft_eq i hit]
      exact h hit⟩
#align pi_Union_Inter_singleton_left piUnionInter_singleton_left

theorem generateFrom_piUnionInter_singleton_left (s : ι → Set α) (S : Set ι) :
    generateFrom (piUnionInter (fun k => {s k}) S) = generateFrom { t | ∃ k ∈ S, s k = t } :=
  by
  refine' le_antisymm (generate_from_le _) (generate_from_mono _)
  · rintro _ ⟨I, hI, f, hf, rfl⟩
    refine' Finset.measurableSet_bInter _ fun m hm => measurable_set_generate_from _
    exact ⟨m, hI hm, (hf m hm).symm⟩
  · rintro _ ⟨k, hk, rfl⟩
    refine' ⟨{k}, fun m hm => _, s, fun i hi => _, _⟩
    · rw [Finset.mem_coe, Finset.mem_singleton] at hm
      rwa [hm]
    · exact Set.mem_singleton _
    · simp only [Finset.mem_singleton, Set.interᵢ_interᵢ_eq_left]
#align generate_from_pi_Union_Inter_singleton_left generateFrom_piUnionInter_singleton_left

/-- If `π` is a family of π-systems, then `pi_Union_Inter π S` is a π-system. -/
theorem isPiSystem_piUnionInter (π : ι → Set (Set α)) (hpi : ∀ x, IsPiSystem (π x)) (S : Set ι) :
    IsPiSystem (piUnionInter π S) :=
  by
  rintro t1 ⟨p1, hp1S, f1, hf1m, ht1_eq⟩ t2 ⟨p2, hp2S, f2, hf2m, ht2_eq⟩ h_nonempty
  simp_rw [piUnionInter, Set.mem_setOf_eq]
  let g n := ite (n ∈ p1) (f1 n) Set.univ ∩ ite (n ∈ p2) (f2 n) Set.univ
  have hp_union_ss : ↑(p1 ∪ p2) ⊆ S := by
    simp only [hp1S, hp2S, Finset.coe_union, union_subset_iff, and_self_iff]
  use p1 ∪ p2, hp_union_ss, g
  have h_inter_eq : t1 ∩ t2 = ⋂ i ∈ p1 ∪ p2, g i :=
    by
    rw [ht1_eq, ht2_eq]
    simp_rw [← Set.inf_eq_inter, g]
    ext1 x
    simp only [inf_eq_inter, mem_inter_iff, mem_Inter, Finset.mem_union]
    refine' ⟨fun h i hi_mem_union => _, fun h => ⟨fun i hi1 => _, fun i hi2 => _⟩⟩
    · split_ifs
      exacts[⟨h.1 i h_1, h.2 i h_2⟩, ⟨h.1 i h_1, Set.mem_univ _⟩, ⟨Set.mem_univ _, h.2 i h_2⟩,
        ⟨Set.mem_univ _, Set.mem_univ _⟩]
    · specialize h i (Or.inl hi1)
      rw [if_pos hi1] at h
      exact h.1
    · specialize h i (Or.inr hi2)
      rw [if_pos hi2] at h
      exact h.2
  refine' ⟨fun n hn => _, h_inter_eq⟩
  simp_rw [g]
  split_ifs with hn1 hn2
  · refine' hpi n (f1 n) (hf1m n hn1) (f2 n) (hf2m n hn2) (Set.nonempty_iff_ne_empty.2 fun h => _)
    rw [h_inter_eq] at h_nonempty
    suffices h_empty : (⋂ i ∈ p1 ∪ p2, g i) = ∅
    exact (set.not_nonempty_iff_eq_empty.mpr h_empty) h_nonempty
    refine' le_antisymm (Set.interᵢ_subset_of_subset n _) (Set.empty_subset _)
    refine' Set.interᵢ_subset_of_subset hn _
    simp_rw [g, if_pos hn1, if_pos hn2]
    exact h.subset
  · simp [hf1m n hn1]
  · simp [hf2m n h]
  · exact absurd hn (by simp [hn1, h])
#align is_pi_system_pi_Union_Inter isPiSystem_piUnionInter

theorem piUnionInter_mono_left {π π' : ι → Set (Set α)} (h_le : ∀ i, π i ⊆ π' i) (S : Set ι) :
    piUnionInter π S ⊆ piUnionInter π' S := fun s ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩ =>
  ⟨t, ht_mem, ft, fun x hxt => h_le x (hft_mem_pi x hxt), h_eq⟩
#align pi_Union_Inter_mono_left piUnionInter_mono_left

theorem piUnionInter_mono_right {π : ι → Set (Set α)} {S T : Set ι} (hST : S ⊆ T) :
    piUnionInter π S ⊆ piUnionInter π T := fun s ⟨t, ht_mem, ft, hft_mem_pi, h_eq⟩ =>
  ⟨t, ht_mem.trans hST, ft, hft_mem_pi, h_eq⟩
#align pi_Union_Inter_mono_right piUnionInter_mono_right

theorem generateFrom_piUnionInter_le {m : MeasurableSpace α} (π : ι → Set (Set α))
    (h : ∀ n, generateFrom (π n) ≤ m) (S : Set ι) : generateFrom (piUnionInter π S) ≤ m :=
  by
  refine' generate_from_le _
  rintro t ⟨ht_p, ht_p_mem, ft, hft_mem_pi, rfl⟩
  refine' Finset.measurableSet_bInter _ fun x hx_mem => (h x) _ _
  exact measurable_set_generate_from (hft_mem_pi x hx_mem)
#align generate_from_pi_Union_Inter_le generateFrom_piUnionInter_le

theorem subset_piUnionInter {π : ι → Set (Set α)} {S : Set ι} {i : ι} (his : i ∈ S) :
    π i ⊆ piUnionInter π S :=
  by
  have h_ss : {i} ⊆ S := by
    intro j hj
    rw [mem_singleton_iff] at hj
    rwa [hj]
  refine' subset.trans _ (piUnionInter_mono_right h_ss)
  rw [piUnionInter_singleton]
  exact subset_union_left _ _
#align subset_pi_Union_Inter subset_piUnionInter

theorem mem_piUnionInter_of_measurableSet (m : ι → MeasurableSpace α) {S : Set ι} {i : ι}
    (hiS : i ∈ S) (s : Set α) (hs : measurable_set[m i] s) :
    s ∈ piUnionInter (fun n => { s | measurable_set[m n] s }) S :=
  subset_piUnionInter hiS hs
#align mem_pi_Union_Inter_of_measurable_set mem_piUnionInter_of_measurableSet

theorem le_generateFrom_piUnionInter {π : ι → Set (Set α)} (S : Set ι) {x : ι} (hxS : x ∈ S) :
    generateFrom (π x) ≤ generateFrom (piUnionInter π S) :=
  generateFrom_mono (subset_piUnionInter hxS)
#align le_generate_from_pi_Union_Inter le_generateFrom_piUnionInter

theorem measurableSet_supᵢ_of_mem_piUnionInter (m : ι → MeasurableSpace α) (S : Set ι) (t : Set α)
    (ht : t ∈ piUnionInter (fun n => { s | measurable_set[m n] s }) S) :
    measurable_set[⨆ i ∈ S, m i] t :=
  by
  rcases ht with ⟨pt, hpt, ft, ht_m, rfl⟩
  refine' pt.measurable_set_bInter fun i hi => _
  suffices h_le : m i ≤ ⨆ i ∈ S, m i; exact h_le (ft i) (ht_m i hi)
  have hi' : i ∈ S := hpt hi
  exact le_supᵢ₂ i hi'
#align measurable_set_supr_of_mem_pi_Union_Inter measurableSet_supᵢ_of_mem_piUnionInter

theorem generateFrom_piUnionInter_measurableSet (m : ι → MeasurableSpace α) (S : Set ι) :
    generateFrom (piUnionInter (fun n => { s | measurable_set[m n] s }) S) = ⨆ i ∈ S, m i :=
  by
  refine' le_antisymm _ _
  · rw [← @generate_from_measurable_set α (⨆ i ∈ S, m i)]
    exact generate_from_mono (measurableSet_supᵢ_of_mem_piUnionInter m S)
  · refine' supᵢ₂_le fun i hi => _
    rw [← @generate_from_measurable_set α (m i)]
    exact generate_from_mono (mem_piUnionInter_of_measurableSet m hi)
#align generate_from_pi_Union_Inter_measurable_set generateFrom_piUnionInter_measurableSet

end UnionInter

namespace MeasurableSpace

variable {α : Type _}

/-! ## Dynkin systems and Π-λ theorem -/


/-- A Dynkin system is a collection of subsets of a type `α` that contains the empty set,
  is closed under complementation and under countable union of pairwise disjoint sets.
  The disjointness condition is the only difference with `σ`-algebras.

  The main purpose of Dynkin systems is to provide a powerful induction rule for σ-algebras
  generated by a collection of sets which is stable under intersection.

  A Dynkin system is also known as a "λ-system" or a "d-system".
-/
structure DynkinSystem (α : Type _) where
  Has : Set α → Prop
  hasEmpty : has ∅
  HasCompl : ∀ {a}, has a → has (aᶜ)
  hasUnionNat : ∀ {f : ℕ → Set α}, Pairwise (Disjoint on f) → (∀ i, has (f i)) → has (⋃ i, f i)
#align measurable_space.dynkin_system MeasurableSpace.DynkinSystem

namespace DynkinSystem

@[ext]
theorem ext : ∀ {d₁ d₂ : DynkinSystem α}, (∀ s : Set α, d₁.Has s ↔ d₂.Has s) → d₁ = d₂
  | ⟨s₁, _, _, _⟩, ⟨s₂, _, _, _⟩, h =>
    by
    have : s₁ = s₂ := funext fun x => propext <| h x
    subst this
#align measurable_space.dynkin_system.ext MeasurableSpace.DynkinSystem.ext

variable (d : DynkinSystem α)

theorem has_compl_iff {a} : d.Has (aᶜ) ↔ d.Has a :=
  ⟨fun h => by simpa using d.has_compl h, fun h => d.HasCompl h⟩
#align measurable_space.dynkin_system.has_compl_iff MeasurableSpace.DynkinSystem.has_compl_iff

theorem hasUniv : d.Has univ := by simpa using d.has_compl d.has_empty
#align measurable_space.dynkin_system.has_univ MeasurableSpace.DynkinSystem.hasUniv

theorem hasUnion {β} [Countable β] {f : β → Set α} (hd : Pairwise (Disjoint on f))
    (h : ∀ i, d.Has (f i)) : d.Has (⋃ i, f i) :=
  by
  cases nonempty_encodable β
  rw [← Encodable.unionᵢ_decode₂]
  exact
    d.has_Union_nat (Encodable.unionᵢ_decode₂_disjoint_on hd) fun n =>
      Encodable.unionᵢ_decode₂_cases d.has_empty h
#align measurable_space.dynkin_system.has_Union MeasurableSpace.DynkinSystem.hasUnion

/- warning: measurable_space.dynkin_system.has_union clashes with measurable_space.dynkin_system.has_Union -> MeasurableSpace.DynkinSystem.hasUnion
warning: measurable_space.dynkin_system.has_union -> MeasurableSpace.DynkinSystem.hasUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} (d : MeasurableSpace.DynkinSystem.{u_1} α) {s₁ : Set.{u_1} α} {s₂ : Set.{u_1} α}, (MeasurableSpace.DynkinSystem.Has.{u_1} α d s₁) -> (MeasurableSpace.DynkinSystem.Has.{u_1} α d s₂) -> (Disjoint.{u_1} (Set.{u_1} α) (CompleteSemilatticeInf.toPartialOrder.{u_1} (Set.{u_1} α) (CompleteLattice.toCompleteSemilatticeInf.{u_1} (Set.{u_1} α) (Order.Coframe.toCompleteLattice.{u_1} (Set.{u_1} α) (CompleteDistribLattice.toCoframe.{u_1} (Set.{u_1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u_1} (Set.{u_1} α) (Set.completeBooleanAlgebra.{u_1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u_1} (Set.{u_1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u_1} (Set.{u_1} α) (Set.booleanAlgebra.{u_1} α))) s₁ s₂) -> (MeasurableSpace.DynkinSystem.Has.{u_1} α d (Union.union.{u_1} (Set.{u_1} α) (Set.hasUnion.{u_1} α) s₁ s₂))
but is expected to have type
  PUnit.{0}
Case conversion may be inaccurate. Consider using '#align measurable_space.dynkin_system.has_union MeasurableSpace.DynkinSystem.hasUnionₓ'. -/
theorem hasUnion {s₁ s₂ : Set α} (h₁ : d.Has s₁) (h₂ : d.Has s₂) (h : Disjoint s₁ s₂) :
    d.Has (s₁ ∪ s₂) := by
  rw [union_eq_Union]
  exact d.has_Union (pairwise_disjoint_on_bool.2 h) (Bool.forall_bool.2 ⟨h₂, h₁⟩)
#align measurable_space.dynkin_system.has_union MeasurableSpace.DynkinSystem.hasUnion

theorem hasDiff {s₁ s₂ : Set α} (h₁ : d.Has s₁) (h₂ : d.Has s₂) (h : s₂ ⊆ s₁) : d.Has (s₁ \ s₂) :=
  by
  apply d.has_compl_iff.1
  simp [diff_eq, compl_inter]
  exact d.has_union (d.has_compl h₁) h₂ (disjoint_compl_left.mono_right h)
#align measurable_space.dynkin_system.has_diff MeasurableSpace.DynkinSystem.hasDiff

instance : LE (DynkinSystem α) where le m₁ m₂ := m₁.Has ≤ m₂.Has

theorem le_def {α} {a b : DynkinSystem α} : a ≤ b ↔ a.Has ≤ b.Has :=
  Iff.rfl
#align measurable_space.dynkin_system.le_def MeasurableSpace.DynkinSystem.le_def

instance : PartialOrder (DynkinSystem α) :=
  { DynkinSystem.hasLe with
    le_refl := fun a b => le_rfl
    le_trans := fun a b c hab hbc => le_def.mpr (le_trans hab hbc)
    le_antisymm := fun a b h₁ h₂ => ext fun s => ⟨h₁ s, h₂ s⟩ }

/-- Every measurable space (σ-algebra) forms a Dynkin system -/
def ofMeasurableSpace (m : MeasurableSpace α) : DynkinSystem α
    where
  Has := m.MeasurableSet'
  hasEmpty := m.measurable_set_empty
  HasCompl := m.measurable_set_compl
  hasUnionNat f _ hf := m.measurable_set_Union f hf
#align measurable_space.dynkin_system.of_measurable_space MeasurableSpace.DynkinSystem.ofMeasurableSpace

theorem ofMeasurableSpace_le_ofMeasurableSpace_iff {m₁ m₂ : MeasurableSpace α} :
    ofMeasurableSpace m₁ ≤ ofMeasurableSpace m₂ ↔ m₁ ≤ m₂ :=
  Iff.rfl
#align measurable_space.dynkin_system.of_measurable_space_le_of_measurable_space_iff MeasurableSpace.DynkinSystem.ofMeasurableSpace_le_ofMeasurableSpace_iff

/-- The least Dynkin system containing a collection of basic sets.
  This inductive type gives the underlying collection of sets. -/
inductive GenerateHas (s : Set (Set α)) : Set α → Prop
  | basic : ∀ t ∈ s, generate_has t
  | Empty : generate_has ∅
  | compl : ∀ {a}, generate_has a → generate_has (aᶜ)
  |
  Union :
    ∀ {f : ℕ → Set α},
      Pairwise (Disjoint on f) → (∀ i, generate_has (f i)) → generate_has (⋃ i, f i)
#align measurable_space.dynkin_system.generate_has MeasurableSpace.DynkinSystem.GenerateHas

theorem generateHas_compl {C : Set (Set α)} {s : Set α} : GenerateHas C (sᶜ) ↔ GenerateHas C s :=
  by
  refine' ⟨_, generate_has.compl⟩
  intro h
  convert generate_has.compl h
  simp
#align measurable_space.dynkin_system.generate_has_compl MeasurableSpace.DynkinSystem.generateHas_compl

/-- The least Dynkin system containing a collection of basic sets. -/
def generate (s : Set (Set α)) : DynkinSystem α
    where
  Has := GenerateHas s
  hasEmpty := GenerateHas.empty
  HasCompl a := GenerateHas.compl
  hasUnionNat f := GenerateHas.Union
#align measurable_space.dynkin_system.generate MeasurableSpace.DynkinSystem.generate

theorem generateHas_def {C : Set (Set α)} : (generate C).Has = GenerateHas C :=
  rfl
#align measurable_space.dynkin_system.generate_has_def MeasurableSpace.DynkinSystem.generateHas_def

instance : Inhabited (DynkinSystem α) :=
  ⟨generate univ⟩

/-- If a Dynkin system is closed under binary intersection, then it forms a `σ`-algebra. -/
def toMeasurableSpace (h_inter : ∀ s₁ s₂, d.Has s₁ → d.Has s₂ → d.Has (s₁ ∩ s₂))
    where
  MeasurableSet' := d.Has
  measurable_set_empty := d.hasEmpty
  measurable_set_compl s h := d.HasCompl h
  measurable_set_Union f hf := by
    rw [← unionᵢ_disjointed]
    exact
      d.has_Union (disjoint_disjointed _) fun n =>
        disjointedRec (fun t i h => h_inter _ _ h <| d.has_compl <| hf i) (hf n)
#align measurable_space.dynkin_system.to_measurable_space MeasurableSpace.DynkinSystem.toMeasurableSpace

theorem ofMeasurableSpace_toMeasurableSpace
    (h_inter : ∀ s₁ s₂, d.Has s₁ → d.Has s₂ → d.Has (s₁ ∩ s₂)) :
    ofMeasurableSpace (d.toMeasurableSpace h_inter) = d :=
  ext fun s => Iff.rfl
#align measurable_space.dynkin_system.of_measurable_space_to_measurable_space MeasurableSpace.DynkinSystem.ofMeasurableSpace_toMeasurableSpace

/-- If `s` is in a Dynkin system `d`, we can form the new Dynkin system `{s ∩ t | t ∈ d}`. -/
def restrictOn {s : Set α} (h : d.Has s) : DynkinSystem α
    where
  Has t := d.Has (t ∩ s)
  hasEmpty := by simp [d.has_empty]
  HasCompl t hts :=
    by
    have : tᶜ ∩ s = (t ∩ s)ᶜ \ sᶜ := Set.ext fun x => by by_cases x ∈ s <;> simp [h]
    rw [this]
    exact
      d.has_diff (d.has_compl hts) (d.has_compl h)
        (compl_subset_compl.mpr <| inter_subset_right _ _)
  hasUnionNat f hd hf := by
    rw [Union_inter]
    refine' d.has_Union_nat _ hf
    exact hd.mono fun i j => Disjoint.mono (inter_subset_left _ _) (inter_subset_left _ _)
#align measurable_space.dynkin_system.restrict_on MeasurableSpace.DynkinSystem.restrictOn

theorem generate_le {s : Set (Set α)} (h : ∀ t ∈ s, d.Has t) : generate s ≤ d := fun t ht =>
  ht.recOn h d.hasEmpty (fun a _ h => d.HasCompl h) fun f hd _ hf => d.hasUnion hd hf
#align measurable_space.dynkin_system.generate_le MeasurableSpace.DynkinSystem.generate_le

theorem generate_has_subset_generate_measurable {C : Set (Set α)} {s : Set α}
    (hs : (generate C).Has s) : measurable_set[generateFrom C] s :=
  generate_le (ofMeasurableSpace (generateFrom C)) (fun t => measurableSet_generateFrom) s hs
#align measurable_space.dynkin_system.generate_has_subset_generate_measurable MeasurableSpace.DynkinSystem.generate_has_subset_generate_measurable

theorem generateInter {s : Set (Set α)} (hs : IsPiSystem s) {t₁ t₂ : Set α}
    (ht₁ : (generate s).Has t₁) (ht₂ : (generate s).Has t₂) : (generate s).Has (t₁ ∩ t₂) :=
  have : generate s ≤ (generate s).restrictOn ht₂ :=
    generate_le _ fun s₁ hs₁ =>
      have : (generate s).Has s₁ := GenerateHas.basic s₁ hs₁
      have : generate s ≤ (generate s).restrictOn this :=
        generate_le _ fun s₂ hs₂ =>
          show (generate s).Has (s₂ ∩ s₁) from
            (s₂ ∩ s₁).eq_empty_or_nonempty.elim (fun h => h.symm ▸ generate_has.empty) fun h =>
              GenerateHas.basic _ <| hs _ hs₂ _ hs₁ h
      have : (generate s).Has (t₂ ∩ s₁) := this _ ht₂
      show (generate s).Has (s₁ ∩ t₂) by rwa [inter_comm]
  this _ ht₁
#align measurable_space.dynkin_system.generate_inter MeasurableSpace.DynkinSystem.generateInter

/-- **Dynkin's π-λ theorem**:
  Given a collection of sets closed under binary intersections, then the Dynkin system it
  generates is equal to the σ-algebra it generates.
  This result is known as the π-λ theorem.
  A collection of sets closed under binary intersection is called a π-system (often requiring
  additionnally that is is non-empty, but we drop this condition in the formalization).
-/
theorem generateFrom_eq {s : Set (Set α)} (hs : IsPiSystem s) :
    generateFrom s = (generate s).toMeasurableSpace fun t₁ t₂ => generateInter hs :=
  le_antisymm (generate_from_le fun t ht => GenerateHas.basic t ht)
    (ofMeasurableSpace_le_ofMeasurableSpace_iff.mp <|
      by
      rw [of_measurable_space_to_measurable_space]
      exact generate_le _ fun t ht => measurable_set_generate_from ht)
#align measurable_space.dynkin_system.generate_from_eq MeasurableSpace.DynkinSystem.generateFrom_eq

end DynkinSystem

theorem induction_on_inter {C : Set α → Prop} {s : Set (Set α)} [m : MeasurableSpace α]
    (h_eq : m = generateFrom s) (h_inter : IsPiSystem s) (h_empty : C ∅) (h_basic : ∀ t ∈ s, C t)
    (h_compl : ∀ t, MeasurableSet t → C t → C (tᶜ))
    (h_union :
      ∀ f : ℕ → Set α,
        Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) → (∀ i, C (f i)) → C (⋃ i, f i)) :
    ∀ ⦃t⦄, MeasurableSet t → C t :=
  have eq : MeasurableSet = DynkinSystem.GenerateHas s :=
    by
    rw [h_eq, dynkin_system.generate_from_eq h_inter]
    rfl
  fun t ht =>
  have : DynkinSystem.GenerateHas s t := by rwa [Eq] at ht
  this.recOn h_basic h_empty
    (fun t ht =>
      h_compl t <| by
        rw [Eq]
        exact ht)
    fun f hf ht =>
    h_union f hf fun i => by
      rw [Eq]
      exact ht _
#align measurable_space.induction_on_inter MeasurableSpace.induction_on_inter

end MeasurableSpace

