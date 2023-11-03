/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex Kontorovich
-/
import Order.Filter.Bases

#align_import order.filter.pi from "leanprover-community/mathlib"@"ce64cd319bb6b3e82f31c2d38e79080d377be451"

/-!
# (Co)product of a family of filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define two filters on `Π i, α i` and prove some basic properties of these filters.

* `filter.pi (f : Π i, filter (α i))` to be the maximal filter on `Π i, α i` such that
  `∀ i, filter.tendsto (function.eval i) (filter.pi f) (f i)`. It is defined as
  `Π i, filter.comap (function.eval i) (f i)`. This is a generalization of `filter.prod` to indexed
  products.

* `filter.Coprod (f : Π i, filter (α i))`: a generalization of `filter.coprod`; it is the supremum
  of `comap (eval i) (f i)`.
-/


open Set Function

open scoped Classical Filter

namespace Filter

variable {ι : Type _} {α : ι → Type _} {f f₁ f₂ : ∀ i, Filter (α i)} {s : ∀ i, Set (α i)}
  {p : ∀ i, α i → Prop}

section Pi

#print Filter.pi /-
/-- The product of an indexed family of filters. -/
def pi (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨅ i, comap (eval i) (f i)
#align filter.pi Filter.pi
-/

#print Filter.pi.isCountablyGenerated /-
instance pi.isCountablyGenerated [Countable ι] [∀ i, IsCountablyGenerated (f i)] :
    IsCountablyGenerated (pi f) :=
  iInf.isCountablyGenerated _
#align filter.pi.is_countably_generated Filter.pi.isCountablyGenerated
-/

#print Filter.tendsto_eval_pi /-
theorem tendsto_eval_pi (f : ∀ i, Filter (α i)) (i : ι) : Tendsto (eval i) (pi f) (f i) :=
  tendsto_iInf' i tendsto_comap
#align filter.tendsto_eval_pi Filter.tendsto_eval_pi
-/

#print Filter.tendsto_pi /-
theorem tendsto_pi {β : Type _} {m : β → ∀ i, α i} {l : Filter β} :
    Tendsto m l (pi f) ↔ ∀ i, Tendsto (fun x => m x i) l (f i) := by
  simp only [pi, tendsto_infi, tendsto_comap_iff]
#align filter.tendsto_pi Filter.tendsto_pi
-/

#print Filter.le_pi /-
theorem le_pi {g : Filter (∀ i, α i)} : g ≤ pi f ↔ ∀ i, Tendsto (eval i) g (f i) :=
  tendsto_pi
#align filter.le_pi Filter.le_pi
-/

#print Filter.pi_mono /-
@[mono]
theorem pi_mono (h : ∀ i, f₁ i ≤ f₂ i) : pi f₁ ≤ pi f₂ :=
  iInf_mono fun i => comap_mono <| h i
#align filter.pi_mono Filter.pi_mono
-/

#print Filter.mem_pi_of_mem /-
theorem mem_pi_of_mem (i : ι) {s : Set (α i)} (hs : s ∈ f i) : eval i ⁻¹' s ∈ pi f :=
  mem_iInf_of_mem i <| preimage_mem_comap hs
#align filter.mem_pi_of_mem Filter.mem_pi_of_mem
-/

#print Filter.pi_mem_pi /-
theorem pi_mem_pi {I : Set ι} (hI : I.Finite) (h : ∀ i ∈ I, s i ∈ f i) : I.pi s ∈ pi f :=
  by
  rw [pi_def, bInter_eq_Inter]
  refine' mem_infi_of_Inter hI (fun i => _) subset.rfl
  exact preimage_mem_comap (h i i.2)
#align filter.pi_mem_pi Filter.pi_mem_pi
-/

#print Filter.mem_pi /-
theorem mem_pi {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Set ι, I.Finite ∧ ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ I.pi t ⊆ s :=
  by
  constructor
  · simp only [pi, mem_infi', mem_comap, pi_def]
    rintro ⟨I, If, V, hVf, hVI, rfl, -⟩; choose t htf htV using hVf
    exact ⟨I, If, t, htf, Inter₂_mono fun i _ => htV i⟩
  · rintro ⟨I, If, t, htf, hts⟩
    exact mem_of_superset (pi_mem_pi If fun i _ => htf i) hts
#align filter.mem_pi Filter.mem_pi
-/

#print Filter.mem_pi' /-
theorem mem_pi' {s : Set (∀ i, α i)} :
    s ∈ pi f ↔ ∃ I : Finset ι, ∃ t : ∀ i, Set (α i), (∀ i, t i ∈ f i) ∧ Set.pi (↑I) t ⊆ s :=
  mem_pi.trans exists_finite_iff_finset
#align filter.mem_pi' Filter.mem_pi'
-/

#print Filter.mem_of_pi_mem_pi /-
theorem mem_of_pi_mem_pi [∀ i, NeBot (f i)] {I : Set ι} (h : I.pi s ∈ pi f) {i : ι} (hi : i ∈ I) :
    s i ∈ f i := by
  rcases mem_pi.1 h with ⟨I', I'f, t, htf, hts⟩
  refine' mem_of_superset (htf i) fun x hx => _
  have : ∀ i, (t i).Nonempty := fun i => nonempty_of_mem (htf i)
  choose g hg
  have : update g i x ∈ I'.pi t := by intro j hj; rcases eq_or_ne j i with (rfl | hne) <;> simp [*]
  simpa using hts this i hi
#align filter.mem_of_pi_mem_pi Filter.mem_of_pi_mem_pi
-/

#print Filter.pi_mem_pi_iff /-
@[simp]
theorem pi_mem_pi_iff [∀ i, NeBot (f i)] {I : Set ι} (hI : I.Finite) :
    I.pi s ∈ pi f ↔ ∀ i ∈ I, s i ∈ f i :=
  ⟨fun h i hi => mem_of_pi_mem_pi h hi, pi_mem_pi hI⟩
#align filter.pi_mem_pi_iff Filter.pi_mem_pi_iff
-/

#print Filter.Eventually.eval_pi /-
theorem Eventually.eval_pi {i : ι} (hf : ∀ᶠ x : α i in f i, p i x) :
    ∀ᶠ x : ∀ i : ι, α i in pi f, p i (x i) :=
  (tendsto_eval_pi _ _).Eventually hf
#align filter.eventually.eval_pi Filter.Eventually.eval_pi
-/

#print Filter.eventually_pi /-
theorem eventually_pi [Finite ι] (hf : ∀ i, ∀ᶠ x in f i, p i x) :
    ∀ᶠ x : ∀ i, α i in pi f, ∀ i, p i (x i) :=
  eventually_all.2 fun i => (hf _).eval_pi
#align filter.eventually_pi Filter.eventually_pi
-/

#print Filter.hasBasis_pi /-
theorem hasBasis_pi {ι' : ι → Type} {s : ∀ i, ι' i → Set (α i)} {p : ∀ i, ι' i → Prop}
    (h : ∀ i, (f i).HasBasis (p i) (s i)) :
    (pi f).HasBasis (fun If : Set ι × ∀ i, ι' i => If.1.Finite ∧ ∀ i ∈ If.1, p i (If.2 i))
      fun If : Set ι × ∀ i, ι' i => If.1.pi fun i => s i <| If.2 i :=
  by
  have : (pi f).HasBasis _ _ := has_basis_infi' fun i => (h i).comap (eval i : (∀ j, α j) → α i)
  convert this
  ext
  simp
#align filter.has_basis_pi Filter.hasBasis_pi
-/

#print Filter.pi_inf_principal_univ_pi_eq_bot /-
@[simp]
theorem pi_inf_principal_univ_pi_eq_bot : pi f ⊓ 𝓟 (Set.pi univ s) = ⊥ ↔ ∃ i, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  constructor
  · simp only [inf_principal_eq_bot, mem_pi]; contrapose!
    rintro (hsf : ∀ i, ∃ᶠ x in f i, x ∈ s i) I If t htf hts
    have : ∀ i, (s i ∩ t i).Nonempty := fun i => ((hsf i).and_eventually (htf i)).exists
    choose x hxs hxt
    exact hts (fun i hi => hxt i) (mem_univ_pi.2 hxs)
  · simp only [inf_principal_eq_bot]
    rintro ⟨i, hi⟩
    filter_upwards [mem_pi_of_mem i hi] with x using mt fun h => h i trivial
#align filter.pi_inf_principal_univ_pi_eq_bot Filter.pi_inf_principal_univ_pi_eq_bot
-/

#print Filter.pi_inf_principal_pi_eq_bot /-
@[simp]
theorem pi_inf_principal_pi_eq_bot [∀ i, NeBot (f i)] {I : Set ι} :
    pi f ⊓ 𝓟 (Set.pi I s) = ⊥ ↔ ∃ i ∈ I, f i ⊓ 𝓟 (s i) = ⊥ :=
  by
  rw [← univ_pi_piecewise I, pi_inf_principal_univ_pi_eq_bot]
  refine' exists_congr fun i => _
  by_cases hi : i ∈ I <;> simp [hi, (‹∀ i, ne_bot (f i)› i).Ne]
#align filter.pi_inf_principal_pi_eq_bot Filter.pi_inf_principal_pi_eq_bot
-/

#print Filter.pi_inf_principal_univ_pi_neBot /-
@[simp]
theorem pi_inf_principal_univ_pi_neBot :
    NeBot (pi f ⊓ 𝓟 (Set.pi univ s)) ↔ ∀ i, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_univ_pi_ne_bot Filter.pi_inf_principal_univ_pi_neBot
-/

#print Filter.pi_inf_principal_pi_neBot /-
@[simp]
theorem pi_inf_principal_pi_neBot [∀ i, NeBot (f i)] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) ↔ ∀ i ∈ I, NeBot (f i ⊓ 𝓟 (s i)) := by simp [ne_bot_iff]
#align filter.pi_inf_principal_pi_ne_bot Filter.pi_inf_principal_pi_neBot
-/

#print Filter.PiInfPrincipalPi.neBot /-
instance PiInfPrincipalPi.neBot [h : ∀ i, NeBot (f i ⊓ 𝓟 (s i))] {I : Set ι} :
    NeBot (pi f ⊓ 𝓟 (I.pi s)) :=
  (pi_inf_principal_univ_pi_neBot.2 ‹_›).mono <|
    inf_le_inf_left _ <| principal_mono.2 fun x hx i hi => hx i trivial
#align filter.pi_inf_principal_pi.ne_bot Filter.PiInfPrincipalPi.neBot
-/

#print Filter.pi_eq_bot /-
@[simp]
theorem pi_eq_bot : pi f = ⊥ ↔ ∃ i, f i = ⊥ := by
  simpa using @pi_inf_principal_univ_pi_eq_bot ι α f fun _ => univ
#align filter.pi_eq_bot Filter.pi_eq_bot
-/

#print Filter.pi_neBot /-
@[simp]
theorem pi_neBot : NeBot (pi f) ↔ ∀ i, NeBot (f i) := by simp [ne_bot_iff]
#align filter.pi_ne_bot Filter.pi_neBot
-/

instance [∀ i, NeBot (f i)] : NeBot (pi f) :=
  pi_neBot.2 ‹_›

#print Filter.map_eval_pi /-
@[simp]
theorem map_eval_pi (f : ∀ i, Filter (α i)) [∀ i, NeBot (f i)] (i : ι) :
    map (eval i) (pi f) = f i :=
  by
  refine' le_antisymm (tendsto_eval_pi f i) fun s hs => _
  rcases mem_pi.1 (mem_map.1 hs) with ⟨I, hIf, t, htf, hI⟩
  rw [← image_subset_iff] at hI 
  refine' mem_of_superset (htf i) ((subset_eval_image_pi _ _).trans hI)
  exact nonempty_of_mem (pi_mem_pi hIf fun i hi => htf i)
#align filter.map_eval_pi Filter.map_eval_pi
-/

#print Filter.pi_le_pi /-
@[simp]
theorem pi_le_pi [∀ i, NeBot (f₁ i)] : pi f₁ ≤ pi f₂ ↔ ∀ i, f₁ i ≤ f₂ i :=
  ⟨fun h i => map_eval_pi f₁ i ▸ (tendsto_eval_pi _ _).mono_left h, pi_mono⟩
#align filter.pi_le_pi Filter.pi_le_pi
-/

#print Filter.pi_inj /-
@[simp]
theorem pi_inj [∀ i, NeBot (f₁ i)] : pi f₁ = pi f₂ ↔ f₁ = f₂ :=
  by
  refine' ⟨fun h => _, congr_arg pi⟩
  have hle : f₁ ≤ f₂ := pi_le_pi.1 h.le
  haveI : ∀ i, ne_bot (f₂ i) := fun i => ne_bot_of_le (hle i)
  exact hle.antisymm (pi_le_pi.1 h.ge)
#align filter.pi_inj Filter.pi_inj
-/

end Pi

/-! ### `n`-ary coproducts of filters -/


section Coprod

#print Filter.coprodᵢ /-
/-- Coproduct of filters. -/
protected def coprodᵢ (f : ∀ i, Filter (α i)) : Filter (∀ i, α i) :=
  ⨆ i : ι, comap (eval i) (f i)
#align filter.Coprod Filter.coprodᵢ
-/

#print Filter.mem_coprodᵢ_iff /-
theorem mem_coprodᵢ_iff {s : Set (∀ i, α i)} :
    s ∈ Filter.coprodᵢ f ↔ ∀ i : ι, ∃ t₁ ∈ f i, eval i ⁻¹' t₁ ⊆ s := by simp [Filter.coprodᵢ]
#align filter.mem_Coprod_iff Filter.mem_coprodᵢ_iff
-/

#print Filter.compl_mem_coprodᵢ /-
theorem compl_mem_coprodᵢ {s : Set (∀ i, α i)} :
    sᶜ ∈ Filter.coprodᵢ f ↔ ∀ i, (eval i '' s)ᶜ ∈ f i := by
  simp only [Filter.coprodᵢ, mem_supr, compl_mem_comap]
#align filter.compl_mem_Coprod Filter.compl_mem_coprodᵢ
-/

#print Filter.coprodᵢ_neBot_iff' /-
theorem coprodᵢ_neBot_iff' : NeBot (Filter.coprodᵢ f) ↔ (∀ i, Nonempty (α i)) ∧ ∃ d, NeBot (f d) :=
  by simp only [Filter.coprodᵢ, supr_ne_bot, ← exists_and_left, ← comap_eval_ne_bot_iff']
#align filter.Coprod_ne_bot_iff' Filter.coprodᵢ_neBot_iff'
-/

#print Filter.coprodᵢ_neBot_iff /-
@[simp]
theorem coprodᵢ_neBot_iff [∀ i, Nonempty (α i)] : NeBot (Filter.coprodᵢ f) ↔ ∃ d, NeBot (f d) := by
  simp [Coprod_ne_bot_iff', *]
#align filter.Coprod_ne_bot_iff Filter.coprodᵢ_neBot_iff
-/

#print Filter.coprodᵢ_eq_bot_iff' /-
theorem coprodᵢ_eq_bot_iff' : Filter.coprodᵢ f = ⊥ ↔ (∃ i, IsEmpty (α i)) ∨ f = ⊥ := by
  simpa [not_and_or, funext_iff] using not_congr Coprod_ne_bot_iff'
#align filter.Coprod_eq_bot_iff' Filter.coprodᵢ_eq_bot_iff'
-/

#print Filter.coprodᵢ_eq_bot_iff /-
@[simp]
theorem coprodᵢ_eq_bot_iff [∀ i, Nonempty (α i)] : Filter.coprodᵢ f = ⊥ ↔ f = ⊥ := by
  simpa [funext_iff] using not_congr Coprod_ne_bot_iff
#align filter.Coprod_eq_bot_iff Filter.coprodᵢ_eq_bot_iff
-/

#print Filter.coprodᵢ_bot' /-
@[simp]
theorem coprodᵢ_bot' : Filter.coprodᵢ (⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_eq_bot_iff'.2 (Or.inr rfl)
#align filter.Coprod_bot' Filter.coprodᵢ_bot'
-/

#print Filter.coprodᵢ_bot /-
@[simp]
theorem coprodᵢ_bot : Filter.coprodᵢ (fun _ => ⊥ : ∀ i, Filter (α i)) = ⊥ :=
  coprodᵢ_bot'
#align filter.Coprod_bot Filter.coprodᵢ_bot
-/

#print Filter.NeBot.coprodᵢ /-
theorem NeBot.coprodᵢ [∀ i, Nonempty (α i)] {i : ι} (h : NeBot (f i)) : NeBot (Filter.coprodᵢ f) :=
  coprodᵢ_neBot_iff.2 ⟨i, h⟩
#align filter.ne_bot.Coprod Filter.NeBot.coprodᵢ
-/

#print Filter.coprodᵢ_neBot /-
@[instance]
theorem coprodᵢ_neBot [∀ i, Nonempty (α i)] [Nonempty ι] (f : ∀ i, Filter (α i))
    [H : ∀ i, NeBot (f i)] : NeBot (Filter.coprodᵢ f) :=
  (H (Classical.arbitrary ι)).coprodᵢ
#align filter.Coprod_ne_bot Filter.coprodᵢ_neBot
-/

#print Filter.coprodᵢ_mono /-
@[mono]
theorem coprodᵢ_mono (hf : ∀ i, f₁ i ≤ f₂ i) : Filter.coprodᵢ f₁ ≤ Filter.coprodᵢ f₂ :=
  iSup_mono fun i => comap_mono (hf i)
#align filter.Coprod_mono Filter.coprodᵢ_mono
-/

variable {β : ι → Type _} {m : ∀ i, α i → β i}

#print Filter.map_pi_map_coprodᵢ_le /-
theorem map_pi_map_coprodᵢ_le :
    map (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) ≤
      Filter.coprodᵢ fun i => map (m i) (f i) :=
  by
  simp only [le_def, mem_map, mem_Coprod_iff]
  intro s h i
  obtain ⟨t, H, hH⟩ := h i
  exact ⟨{x : α i | m i x ∈ t}, H, fun x hx => hH hx⟩
#align filter.map_pi_map_Coprod_le Filter.map_pi_map_coprodᵢ_le
-/

#print Filter.Tendsto.pi_map_coprodᵢ /-
theorem Tendsto.pi_map_coprodᵢ {g : ∀ i, Filter (β i)} (h : ∀ i, Tendsto (m i) (f i) (g i)) :
    Tendsto (fun k : ∀ i, α i => fun i => m i (k i)) (Filter.coprodᵢ f) (Filter.coprodᵢ g) :=
  map_pi_map_coprodᵢ_le.trans (coprodᵢ_mono h)
#align filter.tendsto.pi_map_Coprod Filter.Tendsto.pi_map_coprodᵢ
-/

end Coprod

end Filter

