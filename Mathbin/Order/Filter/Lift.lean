/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Order.Filter.Bases

/-!
# Lift filters along filter and set functions
-/


open Set

open_locale Classical Filter

namespace Filter

variable {α : Type _} {β : Type _} {γ : Type _} {ι : Sort _}

section lift

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : Filter α) (g : Set α → Filter β) :=
  ⨅ s ∈ f, g s

variable {f f₁ f₂ : Filter α} {g g₁ g₂ : Set α → Filter β}

@[simp]
theorem lift_top (g : Set α → Filter β) : (⊤ : Filter α).lift g = g Univ := by
  simp [Filter.lift]

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type, see `filter.has_basis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
theorem HasBasis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α} (hf : f.HasBasis p s) {β : ι → Type _}
    {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ} {g : Set α → Filter γ} (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i))
    (gm : Monotone g) {s : Set γ} : s ∈ f.lift g ↔ ∃ (i : ι)(hi : p i)(x : β i)(hx : pg i x), sg i x ⊆ s := by
  refine' (mem_binfi_of_directed _ ⟨univ, univ_sets _⟩).trans _
  · intro t₁ ht₁ t₂ ht₂
    exact ⟨t₁ ∩ t₂, inter_mem ht₁ ht₂, gm <| inter_subset_left _ _, gm <| inter_subset_right _ _⟩
    
  · simp only [← (hg _).mem_iff]
    exact hf.exists_iff fun t₁ t₂ ht H => gm ht H
    

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `filter.has_basis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
theorem HasBasis.lift {ι} {p : ι → Prop} {s : ι → Set α} {f : Filter α} (hf : f.HasBasis p s) {β : ι → Type _}
    {pg : ∀ i, β i → Prop} {sg : ∀ i, β i → Set γ} {g : Set α → Filter γ} (hg : ∀ i, (g <| s i).HasBasis (pg i) (sg i))
    (gm : Monotone g) : (f.lift g).HasBasis (fun i : Σi, β i => p i.1 ∧ pg i.1 i.2) fun i : Σi, β i => sg i.1 i.2 := by
  refine' ⟨fun t => (hf.mem_lift_iff hg gm).trans _⟩
  simp [Sigma.exists, and_assoc, exists_and_distrib_left]

theorem mem_lift_sets (hg : Monotone g) {s : Set β} : s ∈ f.lift g ↔ ∃ t ∈ f, s ∈ g t :=
  (f.basis_sets.mem_lift_iff (fun s => (g s).basis_sets) hg).trans <| by
    simp only [id, exists_mem_subset_iff]

theorem mem_lift {s : Set β} {t : Set α} (ht : t ∈ f) (hs : s ∈ g t) : s ∈ f.lift g :=
  le_principal_iff.mp <| show f.lift g ≤ 𝓟 s from infi_le_of_le t <| infi_le_of_le ht <| le_principal_iff.mpr hs

theorem lift_le {f : Filter α} {g : Set α → Filter β} {h : Filter β} {s : Set α} (hs : s ∈ f) (hg : g s ≤ h) :
    f.lift g ≤ h :=
  infi_le_of_le s <| infi_le_of_le hs <| hg

theorem le_lift {f : Filter α} {g : Set α → Filter β} {h : Filter β} (hh : ∀, ∀ s ∈ f, ∀, h ≤ g s) : h ≤ f.lift g :=
  le_infi fun s => le_infi fun hs => hh s hs

theorem lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
  infi_le_infi fun s => infi_le_infi2 fun hs => ⟨hf hs, hg s⟩

theorem lift_mono' (hg : ∀, ∀ s ∈ f, ∀, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
  infi_le_infi fun s => infi_le_infi fun hs => hg s hs

theorem tendsto_lift {m : γ → β} {l : Filter γ} : Tendsto m l (f.lift g) ↔ ∀, ∀ s ∈ f, ∀, Tendsto m l (g s) := by
  simp only [Filter.lift, tendsto_infi]

theorem map_lift_eq {m : β → γ} (hg : Monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
  have : Monotone (map m ∘ g) := map_mono.comp hg
  Filter.ext fun s => by
    simp only [mem_lift_sets hg, mem_lift_sets this, exists_prop, mem_map, Function.comp_app]

theorem comap_lift_eq {m : γ → β} (hg : Monotone g) : comap m (f.lift g) = f.lift (comap m ∘ g) := by
  have : Monotone (comap m ∘ g) := comap_mono.comp hg
  ext
  simp only [mem_lift_sets hg, mem_lift_sets this, mem_comap, exists_prop, mem_lift_sets]
  exact ⟨fun ⟨b, ⟨a, ha, hb⟩, hs⟩ => ⟨a, ha, b, hb, hs⟩, fun ⟨a, ha, b, hb, hs⟩ => ⟨b, ⟨a, ha, hb⟩, hs⟩⟩

theorem comap_lift_eq2 {m : β → α} {g : Set β → Filter γ} (hg : Monotone g) :
    (comap m f).lift g = f.lift (g ∘ Preimage m) :=
  le_antisymmₓ (le_infi fun s => le_infi fun hs => infi_le_of_le (Preimage m s) <| infi_le _ ⟨s, hs, Subset.refl _⟩)
    (le_infi fun s =>
      le_infi fun ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩ => infi_le_of_le s' <| infi_le_of_le hs' <| hg h_sub)

theorem map_lift_eq2 {g : Set β → Filter γ} {m : α → β} (hg : Monotone g) : (map m f).lift g = f.lift (g ∘ Image m) :=
  le_antisymmₓ
    (infi_le_infi2 fun s =>
      ⟨Image m s, infi_le_infi2 fun hs => ⟨(f.sets_of_superset hs) fun a h => mem_image_of_mem _ h, le_rfl⟩⟩)
    (infi_le_infi2 fun t =>
      ⟨Preimage m t,
        infi_le_infi2 fun ht =>
          ⟨ht,
            hg fun x => fun h : x ∈ m '' Preimage m t =>
              let ⟨y, hy, h_eq⟩ := h
              show x ∈ t from h_eq ▸ hy⟩⟩)

theorem lift_comm {g : Filter β} {h : Set α → Set β → Filter γ} :
    (f.lift fun s => g.lift (h s)) = g.lift fun t => f.lift fun s => h s t :=
  le_antisymmₓ
    (le_infi fun i =>
      le_infi fun hi =>
        le_infi fun j => le_infi fun hj => infi_le_of_le j <| infi_le_of_le hj <| infi_le_of_le i <| infi_le _ hi)
    (le_infi fun i =>
      le_infi fun hi =>
        le_infi fun j => le_infi fun hj => infi_le_of_le j <| infi_le_of_le hj <| infi_le_of_le i <| infi_le _ hi)

theorem lift_assoc {h : Set β → Filter γ} (hg : Monotone g) : (f.lift g).lift h = f.lift fun s => (g s).lift h :=
  le_antisymmₓ
    (le_infi fun s =>
      le_infi fun hs =>
        le_infi fun t => le_infi fun ht => infi_le_of_le t <| infi_le _ <| (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
    (le_infi fun t =>
      le_infi fun ht =>
        let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht
        infi_le_of_le s <| infi_le_of_le hs <| infi_le_of_le t <| infi_le _ h')

theorem lift_lift_same_le_lift {g : Set α → Set α → Filter β} :
    (f.lift fun s => f.lift (g s)) ≤ f.lift fun s => g s s :=
  le_infi fun s => le_infi fun hs => infi_le_of_le s <| infi_le_of_le hs <| infi_le_of_le s <| infi_le _ hs

theorem lift_lift_same_eq_lift {g : Set α → Set α → Filter β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) : (f.lift fun s => f.lift (g s)) = f.lift fun s => g s s :=
  le_antisymmₓ lift_lift_same_le_lift
    (le_infi fun s =>
      le_infi fun hs =>
        le_infi fun t =>
          le_infi fun ht =>
            infi_le_of_le (s ∩ t) <|
              infi_le_of_le (inter_mem hs ht) <|
                calc
                  g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) := hg₂ (s ∩ t) (inter_subset_left _ _)
                  _ ≤ g s t := hg₁ s (inter_subset_right _ _)
                  )

theorem lift_principal {s : Set α} (hg : Monotone g) : (𝓟 s).lift g = g s :=
  le_antisymmₓ (infi_le_of_le s <| infi_le _ <| Subset.refl _) (le_infi fun t => le_infi fun hi => hg hi)

theorem monotone_lift [Preorderₓ γ] {f : γ → Filter α} {g : γ → Set α → Filter β} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun c => (f c).lift (g c) := fun a b h => lift_mono (hf h) (hg h)

theorem lift_ne_bot_iff (hm : Monotone g) : (ne_bot <| f.lift g) ↔ ∀, ∀ s ∈ f, ∀, NeBot (g s) := by
  rw [Filter.lift, infi_subtype', infi_ne_bot_iff_of_directed', Subtype.forall']
  · rintro ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨⟨s ∩ t, inter_mem hs ht⟩, hm (inter_subset_left s t), hm (inter_subset_right s t)⟩
    

@[simp]
theorem lift_const {f : Filter α} {g : Filter β} : (f.lift fun x => g) = g :=
  le_antisymmₓ (lift_le univ_mem <| le_reflₓ g) (le_lift fun s hs => le_reflₓ g)

@[simp]
theorem lift_inf {f : Filter α} {g h : Set α → Filter β} : (f.lift fun x => g x⊓h x) = f.lift g⊓f.lift h := by
  simp only [Filter.lift, infi_inf_eq, eq_self_iff_true]

@[simp]
theorem lift_principal2 {f : Filter α} : f.lift 𝓟 = f :=
  le_antisymmₓ (fun s hs => mem_lift hs (mem_principal_self s))
    (le_infi fun s =>
      le_infi fun hs => by
        simp only [hs, le_principal_iff])

theorem lift_infi {f : ι → Filter α} {g : Set α → Filter β} [hι : Nonempty ι] (hg : ∀ {s t}, g s⊓g t = g (s ∩ t)) :
    (infi f).lift g = ⨅ i, (f i).lift g :=
  le_antisymmₓ (le_infi fun i => lift_mono (infi_le _ _) le_rfl) fun s => by
    have g_mono : Monotone g := fun s t h =>
      le_of_inf_eq <| Eq.trans hg <| congr_argₓ g <| inter_eq_self_of_subset_left h
    have : ∀, ∀ t ∈ infi f, ∀, (⨅ i : ι, Filter.lift (f i) g) ≤ g t := fun t ht =>
      infi_sets_induct ht
        (let ⟨i⟩ := hι
        infi_le_of_le i <| infi_le_of_le Univ <| infi_le _ univ_mem)
        fun i s₁ s₂ hs₁ hs₂ => @hg s₁ s₂ ▸ le_inf (infi_le_of_le i <| infi_le_of_le s₁ <| infi_le _ hs₁) hs₂
    simp only [mem_lift_sets g_mono, exists_imp_distrib]
    exact fun t ht hs => this t ht hs

end lift

section Lift'

/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : Filter α) (h : Set α → Set β) :=
  f.lift (𝓟 ∘ h)

variable {f f₁ f₂ : Filter α} {h h₁ h₂ : Set α → Set β}

@[simp]
theorem lift'_top (h : Set α → Set β) : (⊤ : Filter α).lift' h = 𝓟 (h Univ) :=
  lift_top _

theorem mem_lift' {t : Set α} (ht : t ∈ f) : h t ∈ f.lift' h :=
  le_principal_iff.mp <| show f.lift' h ≤ 𝓟 (h t) from infi_le_of_le t <| infi_le_of_le ht <| le_rfl

theorem tendsto_lift' {m : γ → β} {l : Filter γ} : Tendsto m l (f.lift' h) ↔ ∀, ∀ s ∈ f, ∀, ∀ᶠ a in l, m a ∈ h s := by
  simp only [Filter.lift', tendsto_lift, tendsto_principal]

theorem HasBasis.lift' {ι} {p : ι → Prop} {s} (hf : f.HasBasis p s) (hh : Monotone h) :
    (f.lift' h).HasBasis p (h ∘ s) := by
  refine' ⟨fun t => (hf.mem_lift_iff _ (monotone_principal.comp hh)).trans _⟩
  show ∀ i, (𝓟 (h (s i))).HasBasis (fun j : Unit => True) fun j : Unit => h (s i)
  exact fun i => has_basis_principal _
  simp only [exists_const]

theorem mem_lift'_sets (hh : Monotone h) {s : Set β} : s ∈ f.lift' h ↔ ∃ t ∈ f, h t ⊆ s :=
  mem_lift_sets <| monotone_principal.comp hh

theorem eventually_lift'_iff (hh : Monotone h) {p : β → Prop} :
    (∀ᶠ y in f.lift' h, p y) ↔ ∃ t ∈ f, ∀, ∀ y ∈ h t, ∀, p y :=
  mem_lift'_sets hh

theorem lift'_le {f : Filter α} {g : Set α → Set β} {h : Filter β} {s : Set α} (hs : s ∈ f) (hg : 𝓟 (g s) ≤ h) :
    f.lift' g ≤ h :=
  lift_le hs hg

theorem lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
  (lift_mono hf) fun s => principal_mono.mpr <| hh s

theorem lift'_mono' (hh : ∀, ∀ s ∈ f, ∀, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
  infi_le_infi fun s => infi_le_infi fun hs => principal_mono.mpr <| hh s hs

theorem lift'_cong (hh : ∀, ∀ s ∈ f, ∀, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
  le_antisymmₓ (lift'_mono' fun s hs => le_of_eqₓ <| hh s hs) (lift'_mono' fun s hs => le_of_eqₓ <| (hh s hs).symm)

theorem map_lift'_eq {m : β → γ} (hh : Monotone h) : map m (f.lift' h) = f.lift' (Image m ∘ h) :=
  calc
    map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) := map_lift_eq <| monotone_principal.comp hh
    _ = f.lift' (Image m ∘ h) := by
      simp only [(· ∘ ·), Filter.lift', map_principal, eq_self_iff_true]
    

theorem map_lift'_eq2 {g : Set β → Set γ} {m : α → β} (hg : Monotone g) : (map m f).lift' g = f.lift' (g ∘ Image m) :=
  map_lift_eq2 <| monotone_principal.comp hg

theorem comap_lift'_eq {m : γ → β} (hh : Monotone h) : comap m (f.lift' h) = f.lift' (Preimage m ∘ h) :=
  calc
    comap m (f.lift' h) = f.lift (comap m ∘ 𝓟 ∘ h) := comap_lift_eq <| monotone_principal.comp hh
    _ = f.lift' (Preimage m ∘ h) := by
      simp only [(· ∘ ·), Filter.lift', comap_principal, eq_self_iff_true]
    

theorem comap_lift'_eq2 {m : β → α} {g : Set β → Set γ} (hg : Monotone g) :
    (comap m f).lift' g = f.lift' (g ∘ Preimage m) :=
  comap_lift_eq2 <| monotone_principal.comp hg

theorem lift'_principal {s : Set α} (hh : Monotone h) : (𝓟 s).lift' h = 𝓟 (h s) :=
  lift_principal <| monotone_principal.comp hh

theorem lift'_pure {a : α} (hh : Monotone h) : (pure a : Filter α).lift' h = 𝓟 (h {a}) := by
  rw [← principal_singleton, lift'_principal hh]

theorem lift'_bot (hh : Monotone h) : (⊥ : Filter α).lift' h = 𝓟 (h ∅) := by
  rw [← principal_empty, lift'_principal hh]

theorem principal_le_lift' {t : Set β} (hh : ∀, ∀ s ∈ f, ∀, t ⊆ h s) : 𝓟 t ≤ f.lift' h :=
  le_infi fun s => le_infi fun hs => principal_mono.mpr (hh s hs)

theorem monotone_lift' [Preorderₓ γ] {f : γ → Filter α} {g : γ → Set α → Set β} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun c => (f c).lift' (g c) := fun a b h => lift'_mono (hf h) (hg h)

theorem lift_lift'_assoc {g : Set α → Set β} {h : Set β → Filter γ} (hg : Monotone g) (hh : Monotone h) :
    (f.lift' g).lift h = f.lift fun s => h (g s) :=
  calc
    (f.lift' g).lift h = f.lift fun s => (𝓟 (g s)).lift h := lift_assoc (monotone_principal.comp hg)
    _ = f.lift fun s => h (g s) := by
      simp only [lift_principal, hh, eq_self_iff_true]
    

theorem lift'_lift'_assoc {g : Set α → Set β} {h : Set β → Set γ} (hg : Monotone g) (hh : Monotone h) :
    (f.lift' g).lift' h = f.lift' fun s => h (g s) :=
  lift_lift'_assoc hg (monotone_principal.comp hh)

theorem lift'_lift_assoc {g : Set α → Filter β} {h : Set β → Set γ} (hg : Monotone g) :
    (f.lift g).lift' h = f.lift fun s => (g s).lift' h :=
  lift_assoc hg

theorem lift_lift'_same_le_lift' {g : Set α → Set α → Set β} :
    (f.lift fun s => f.lift' (g s)) ≤ f.lift' fun s => g s s :=
  lift_lift_same_le_lift

theorem lift_lift'_same_eq_lift' {g : Set α → Set α → Set β} (hg₁ : ∀ s, Monotone fun t => g s t)
    (hg₂ : ∀ t, Monotone fun s => g s t) : (f.lift fun s => f.lift' (g s)) = f.lift' fun s => g s s :=
  lift_lift_same_eq_lift (fun s => monotone_principal.comp (hg₁ s)) fun t => monotone_principal.comp (hg₂ t)

theorem lift'_inf_principal_eq {h : Set α → Set β} {s : Set β} : f.lift' h⊓𝓟 s = f.lift' fun t => h t ∩ s := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), ← inf_principal, infi_subtype', ← infi_inf]

theorem lift'_ne_bot_iff (hh : Monotone h) : NeBot (f.lift' h) ↔ ∀, ∀ s ∈ f, ∀, (h s).Nonempty :=
  calc
    NeBot (f.lift' h) ↔ ∀, ∀ s ∈ f, ∀, NeBot (𝓟 (h s)) := lift_ne_bot_iff (monotone_principal.comp hh)
    _ ↔ ∀, ∀ s ∈ f, ∀, (h s).Nonempty := by
      simp only [principal_ne_bot_iff]
    

@[simp]
theorem lift'_id {f : Filter α} : f.lift' id = f :=
  lift_principal2

theorem le_lift' {f : Filter α} {h : Set α → Set β} {g : Filter β} (h_le : ∀, ∀ s ∈ f, ∀, h s ∈ g) : g ≤ f.lift' h :=
  le_infi fun s =>
    le_infi fun hs => by
      simpa only [h_le, le_principal_iff, Function.comp_app] using h_le s hs

theorem lift_infi' {f : ι → Filter α} {g : Set α → Filter β} [Nonempty ι] (hf : Directed (· ≥ ·) f) (hg : Monotone g) :
    (infi f).lift g = ⨅ i, (f i).lift g :=
  le_antisymmₓ (le_infi fun i => lift_mono (infi_le _ _) le_rfl) fun s => by
    rw [mem_lift_sets hg]
    simp only [exists_imp_distrib, mem_infi_of_directed hf]
    exact fun t i ht hs => mem_infi_of_mem i <| mem_lift ht hs

theorem lift'_infi {f : ι → Filter α} {g : Set α → Set β} [Nonempty ι] (hg : ∀ {s t}, g s ∩ g t = g (s ∩ t)) :
    (infi f).lift' g = ⨅ i, (f i).lift' g :=
  lift_infi fun s t => by
    simp only [principal_eq_iff_eq, inf_principal, (· ∘ ·), hg]

theorem lift'_inf (f g : Filter α) {s : Set α → Set β} (hs : ∀ {t₁ t₂}, s t₁ ∩ s t₂ = s (t₁ ∩ t₂)) :
    (f⊓g).lift' s = f.lift' s⊓g.lift' s := by
  have : (⨅ b : Bool, cond b f g).lift' s = ⨅ b : Bool, (cond b f g).lift' s := lift'_infi @hs
  simpa only [infi_bool_eq]

theorem comap_eq_lift' {f : Filter β} {m : α → β} : comap m f = f.lift' (Preimage m) :=
  Filter.ext fun s => (mem_lift'_sets monotone_preimage).symm

theorem lift'_infi_powerset {f : ι → Filter α} : (infi f).lift' Powerset = ⨅ i, (f i).lift' Powerset := by
  cases' is_empty_or_nonempty ι
  · rw [infi_of_empty f, infi_of_empty, lift'_top, powerset_univ, principal_univ]
    
  · exact lift'_infi fun _ _ => (powerset_inter _ _).symm
    

theorem lift'_inf_powerset (f g : Filter α) : (f⊓g).lift' Powerset = f.lift' Powerset⊓g.lift' Powerset :=
  (lift'_inf f g) fun _ _ => (powerset_inter _ _).symm

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem eventually_lift'_powerset {f : Filter α} {p : Set α → Prop} :
    (∀ᶠ s in f.lift' Powerset, p s) ↔ ∃ s ∈ f, ∀ t _ : t ⊆ s, p t :=
  eventually_lift'_iff monotone_powerset

theorem eventually_lift'_powerset' {f : Filter α} {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in f.lift' Powerset, p s) ↔ ∃ s ∈ f, p s :=
  eventually_lift'_powerset.trans <| exists₂_congrₓ fun s hsf => ⟨fun H => H s (Subset.refl s), fun hs t ht => hp ht hs⟩

instance lift'_powerset_ne_bot (f : Filter α) : NeBot (f.lift' Powerset) :=
  (lift'_ne_bot_iff monotone_powerset).2 fun _ _ => powerset_nonempty

theorem tendsto_lift'_powerset_mono {la : Filter α} {lb : Filter β} {s t : α → Set β}
    (ht : Tendsto t la (lb.lift' Powerset)) (hst : ∀ᶠ x in la, s x ⊆ t x) : Tendsto s la (lb.lift' Powerset) := by
  simp only [Filter.lift', Filter.lift, (· ∘ ·), tendsto_infi, tendsto_principal] at ht⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun a hst ht => subset.trans hst ht)

@[simp]
theorem eventually_lift'_powerset_forall {f : Filter α} {p : α → Prop} :
    (∀ᶠ s in f.lift' Powerset, ∀, ∀ x ∈ s, ∀, p x) ↔ ∀ᶠ x in f, p x :=
  Iff.trans (eventually_lift'_powerset' fun s t hst ht x hx => ht x (hst hx)) exists_mem_subset_iff

alias eventually_lift'_powerset_forall ↔ Filter.Eventually.of_lift'_powerset Filter.Eventually.lift'_powerset

@[simp]
theorem eventually_lift'_powerset_eventually {f g : Filter α} {p : α → Prop} :
    (∀ᶠ s in f.lift' Powerset, ∀ᶠ x in g, x ∈ s → p x) ↔ ∀ᶠ x in f⊓g, p x :=
  calc
    _ ↔ ∃ s ∈ f, ∀ᶠ x in g, x ∈ s → p x :=
      eventually_lift'_powerset' fun s t hst ht => ht.mono fun x hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ f, ∃ t ∈ g, ∀ x, x ∈ t → x ∈ s → p x := by
      simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in f⊓g, p x := by
      simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]
    

end Lift'

section Prod

variable {f : Filter α}

theorem prod_def {f : Filter α} {g : Filter β} : f ×ᶠ g = f.lift fun s => g.lift' fun t => s ×ˢ t := by
  have : ∀ s : Set α t : Set β, 𝓟 (s ×ˢ t) = (𝓟 s).comap Prod.fst⊓(𝓟 t).comap Prod.snd := by
    simp only [principal_eq_iff_eq, comap_principal, inf_principal] <;> intros <;> rfl
  simp only [Filter.lift', Function.comp, this, lift_inf, lift_const, lift_inf]
  rw [← comap_lift_eq monotone_principal, ← comap_lift_eq monotone_principal]
  simp only [Filter.prod, lift_principal2, eq_self_iff_true]

theorem prod_same_eq : f ×ᶠ f = f.lift' fun t : Set α => t ×ˢ t := by
  rw [prod_def] <;>
    exact
      lift_lift'_same_eq_lift' (fun s => Set.monotone_prod monotone_const monotone_id) fun t =>
        Set.monotone_prod monotone_id monotone_const

theorem mem_prod_same_iff {s : Set (α × α)} : s ∈ f ×ᶠ f ↔ ∃ t ∈ f, t ×ˢ t ⊆ s := by
  rw [prod_same_eq, mem_lift'_sets] <;> exact Set.monotone_prod monotone_id monotone_id

theorem tendsto_prod_self_iff {f : α × α → β} {x : Filter α} {y : Filter β} :
    Filter.Tendsto f (x ×ᶠ x) y ↔ ∀, ∀ W ∈ y, ∀, ∃ U ∈ x, ∀ x x' : α, x ∈ U → x' ∈ U → f (x, x') ∈ W := by
  simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_selfₓ]

variable {α₁ : Type _} {α₂ : Type _} {β₁ : Type _} {β₂ : Type _}

theorem prod_lift_lift {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Filter β₁} {g₂ : Set α₂ → Filter β₂}
    (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift g₁ ×ᶠ f₂.lift g₂ = f₁.lift fun s => f₂.lift fun t => g₁ s ×ᶠ g₂ t := by
  simp only [prod_def]
  rw [lift_assoc]
  apply congr_argₓ
  funext x
  rw [lift_comm]
  apply congr_argₓ
  funext y
  rw [lift'_lift_assoc]
  exact hg₂
  exact hg₁

theorem prod_lift'_lift' {f₁ : Filter α₁} {f₂ : Filter α₂} {g₁ : Set α₁ → Set β₁} {g₂ : Set α₂ → Set β₂}
    (hg₁ : Monotone g₁) (hg₂ : Monotone g₂) :
    f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift fun s => f₂.lift' fun t => g₁ s ×ˢ g₂ t := by
  rw [prod_def, lift_lift'_assoc]
  apply congr_argₓ
  funext x
  rw [lift'_lift'_assoc]
  exact hg₂
  exact Set.monotone_prod monotone_const monotone_id
  exact hg₁
  exact monotone_lift' monotone_const <| monotone_lam fun x => Set.monotone_prod monotone_id monotone_const

end Prod

end Filter

