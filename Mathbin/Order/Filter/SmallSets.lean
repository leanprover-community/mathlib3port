/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn, Yury Kudryashov
-/
import Mathbin.Order.Filter.Lift

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → E → ℝ` is a family of nonnegative functions with integral 1,
then saying that `λ i, support (f i)` tendsto `(𝓝 0).small_sets` is a way of saying that 
`f` tends to the Dirac delta distribution.
-/


open Filter

open Filter Set

variable {α β : Type _} {ι : Sort _}

namespace Filter

variable {l l' la : Filter α} {lb : Filter β}

/-- The filter `l.small_sets` is the largest filter containing all powersets of members of `l`. -/
def smallSets (l : Filter α) : Filter (Set α) :=
  l.lift' Powerset

theorem small_sets_eq_generate {f : Filter α} : f.smallSets = generate (powerset '' f.Sets) := by
  simp_rw [generate_eq_binfi, small_sets, infi_image]
  rfl

theorem HasBasis.small_sets {p : ι → Prop} {s : ι → Set α} (h : HasBasis l p s) :
    HasBasis l.smallSets p fun i => 𝒫 s i :=
  h.lift' monotone_powerset

theorem has_basis_small_sets (l : Filter α) : HasBasis l.smallSets (fun t : Set α => t ∈ l) Powerset :=
  l.basis_sets.smallSets

/-- `g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
theorem tendsto_small_sets_iff {f : α → Set β} : Tendsto f la lb.smallSets ↔ ∀, ∀ t ∈ lb, ∀, ∀ᶠ x in la, f x ⊆ t :=
  (has_basis_small_sets lb).tendsto_right_iff

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (t «expr ⊆ » s)
theorem eventually_small_sets {p : Set α → Prop} : (∀ᶠ s in l.lift' Powerset, p s) ↔ ∃ s ∈ l, ∀ t _ : t ⊆ s, p t :=
  eventually_lift'_iff monotone_powerset

theorem eventually_small_sets' {p : Set α → Prop} (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
    (∀ᶠ s in l.lift' Powerset, p s) ↔ ∃ s ∈ l, p s :=
  eventually_small_sets.trans <| exists₂_congrₓ fun s hsf => ⟨fun H => H s (Subset.refl s), fun hs t ht => hp ht hs⟩

@[mono]
theorem monotone_small_sets : Monotone (@smallSets α) :=
  monotone_lift' monotone_id monotone_const

@[simp]
theorem small_sets_bot : (⊥ : Filter α).smallSets = pure ∅ := by
  rw [small_sets, lift'_bot monotone_powerset, powerset_empty, principal_singleton]

@[simp]
theorem small_sets_top : (⊤ : Filter α).smallSets = ⊤ := by
  rw [small_sets, lift'_top, powerset_univ, principal_univ]

@[simp]
theorem small_sets_principal (s : Set α) : (𝓟 s).smallSets = 𝓟 (𝒫 s) :=
  lift'_principal monotone_powerset

theorem small_sets_comap (l : Filter β) (f : α → β) : (comap f l).smallSets = l.lift' (powerset ∘ Preimage f) :=
  comap_lift'_eq2 monotone_powerset

theorem comap_small_sets (l : Filter β) (f : α → Set β) : comap f l.smallSets = l.lift' (Preimage f ∘ powerset) :=
  comap_lift'_eq monotone_powerset

theorem small_sets_infi {f : ι → Filter α} : (infi f).smallSets = ⨅ i, (f i).smallSets := by
  cases is_empty_or_nonempty ι
  · rw [infi_of_empty f, infi_of_empty, small_sets_top]
    
  · exact lift'_infi fun _ _ => (powerset_inter _ _).symm
    

theorem small_sets_inf (l₁ l₂ : Filter α) : (l₁⊓l₂).smallSets = l₁.smallSets⊓l₂.smallSets :=
  (lift'_inf _ _) fun _ _ => (powerset_inter _ _).symm

instance small_sets_ne_bot (l : Filter α) : NeBot l.smallSets :=
  (lift'_ne_bot_iff monotone_powerset).2 fun _ _ => powerset_nonempty

theorem Tendsto.small_sets_mono {s t : α → Set β} (ht : Tendsto t la lb.smallSets) (hst : ∀ᶠ x in la, s x ⊆ t x) :
    Tendsto s la lb.smallSets := by
  rw [tendsto_small_sets_iff] at ht⊢
  exact fun u hu => (ht u hu).mp (hst.mono fun a hst ht => subset.trans hst ht)

@[simp]
theorem eventually_small_sets_eventually {p : α → Prop} :
    (∀ᶠ s in l.smallSets, ∀ᶠ x in l', x ∈ s → p x) ↔ ∀ᶠ x in l⊓l', p x :=
  calc
    _ ↔ ∃ s ∈ l, ∀ᶠ x in l', x ∈ s → p x := eventually_small_sets' fun s t hst ht => ht.mono fun x hx hs => hx (hst hs)
    _ ↔ ∃ s ∈ l, ∃ t ∈ l', ∀ x, x ∈ t → x ∈ s → p x := by
      simp only [eventually_iff_exists_mem]
    _ ↔ ∀ᶠ x in l⊓l', p x := by
      simp only [eventually_inf, and_comm, mem_inter_iff, ← and_imp]
    

@[simp]
theorem eventually_small_sets_forall {p : α → Prop} : (∀ᶠ s in l.smallSets, ∀, ∀ x ∈ s, ∀, p x) ↔ ∀ᶠ x in l, p x := by
  simpa only [inf_top_eq, eventually_top] using @eventually_small_sets_eventually α l ⊤ p

alias eventually_small_sets_forall ↔ Filter.Eventually.of_small_sets Filter.Eventually.small_sets

end Filter

