import Mathbin.Data.Set.Finite 
import Mathbin.Algebra.BigOperators.Basic

/-!
# Preimage of a `finset` under an injective map.
-/


open Set Function

open_locale BigOperators

universe u v w x

variable {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : Finset α :=
  (s.finite_to_set.preimage hf).toFinset

@[simp]
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' ↑s)} {x : α} : x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_to_finset _

@[simp, normCast]
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' ↑s)) : (↑preimage s f hf : Set α) = f ⁻¹' ↑s :=
  Set.Finite.coe_to_finset _

@[simp]
theorem preimage_empty {f : α → β} :
  preimage ∅ f
      (by 
        simp [inj_on]) =
    ∅ :=
  Finset.coe_injective
    (by 
      simp )

@[simp]
theorem preimage_univ {f : α → β} [Fintype α] [Fintype β] hf : preimage univ f hf = univ :=
  Finset.coe_injective
    (by 
      simp )

@[simp]
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} (hs : Set.InjOn f (f ⁻¹' ↑s))
  (ht : Set.InjOn f (f ⁻¹' ↑t)) :
  (preimage (s ∩ t) f fun x₁ hx₁ x₂ hx₂ => hs (mem_of_mem_inter_left hx₁) (mem_of_mem_inter_left hx₂)) =
    preimage s f hs ∩ preimage t f ht :=
  Finset.coe_injective
    (by 
      simp )

@[simp]
theorem preimage_union [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β} hst :
  preimage (s ∪ t) f hst =
    (preimage s f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_left _ hx₁) (mem_union_left _ hx₂)) ∪
      preimage t f fun x₁ hx₁ x₂ hx₂ => hst (mem_union_right _ hx₁) (mem_union_right _ hx₂) :=
  Finset.coe_injective
    (by 
      simp )

@[simp]
theorem preimage_compl [DecidableEq α] [DecidableEq β] [Fintype α] [Fintype β] {f : α → β} (s : Finset β)
  (hf : Function.Injective f) : preimage (sᶜ) f (hf.inj_on _) = preimage s f (hf.inj_on _)ᶜ :=
  Finset.coe_injective
    (by 
      simp )

theorem monotone_preimage {f : α → β} (h : injective f) : Monotone fun s => preimage s f (h.inj_on _) :=
  fun s t hst x hx => mem_preimage.2 (hst$ mem_preimage.1 hx)

theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
  (hf : Set.InjOn f (f ⁻¹' ↑t)) : s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
  image_subset_iff.trans$
    by 
      simp only [subset_iff, mem_preimage]

theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
  s.map f ⊆ t ↔ s ⊆ t.preimage f (f.injective.inj_on _) :=
  by 
    classical <;> rw [map_eq_image, image_subset_iff_subset_preimage]

theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.Range f)]
  (hf : Set.InjOn f (f ⁻¹' ↑s)) : image f (preimage s f hf) = s.filter fun x => x ∈ Set.Range f :=
  Finset.coe_inj.1$
    by 
      simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range, Set.sep_mem_eq]

theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β) (hf : Set.BijOn f (f ⁻¹' ↑s) (↑s)) :
  image f (preimage s f hf.inj_on) = s :=
  Finset.coe_inj.1$
    by 
      simpa using hf.image_eq

theorem preimage_subset {f : α ↪ β} {s : Finset β} {t : Finset α} (hs : s ⊆ t.map f) :
  s.preimage f (f.injective.inj_on _) ⊆ t :=
  fun x hx => (mem_map' f).1 (hs (mem_preimage.1 hx))

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (u «expr ⊆ » t)
theorem subset_map_iff {f : α ↪ β} {s : Finset β} {t : Finset α} : s ⊆ t.map f ↔ ∃ (u : _)(_ : u ⊆ t), s = u.map f :=
  by 
    classical 
    refine' ⟨fun h => ⟨_, preimage_subset h, _⟩, _⟩
    ·
      rw [map_eq_image, image_preimage, filter_true_of_mem fun x hx => _]
      exact coe_map_subset_range _ _ (h hx)
    ·
      rintro ⟨u, hut, rfl⟩
      exact map_subset_map.2 hut

theorem sigma_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σ a, β a)) (t : Finset α) :
  (t.sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s.filter fun a => a.1 ∈ t :=
  by 
    ext x 
    simp [and_comm]

theorem sigma_preimage_mk_of_subset {β : α → Type _} [DecidableEq α] (s : Finset (Σ a, β a)) {t : Finset α}
  (ht : s.image Sigma.fst ⊆ t) : (t.sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s :=
  by 
    rw [sigma_preimage_mk, filter_true_of_mem$ image_subset_iff.1 ht]

theorem sigma_image_fst_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σ a, β a)) :
  ((s.image Sigma.fst).Sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s :=
  s.sigma_preimage_mk_of_subset (subset.refl _)

end Preimage

@[toAdditive]
theorem prod_preimage' [CommMonoidₓ β] (f : α → γ) [DecidablePred$ fun x => x ∈ Set.Range f] (s : Finset γ)
  (hf : Set.InjOn f (f ⁻¹' ↑s)) (g : γ → β) :
  (∏ x in s.preimage f hf, g (f x)) = ∏ x in s.filter fun x => x ∈ Set.Range f, g x :=
  by 
    have  := Classical.decEq γ <;>
      calc (∏ x in preimage s f hf, g (f x)) = ∏ x in image f (preimage s f hf), g x :=
        Eq.symm$
          prod_image$
            by 
              simpa only [mem_preimage, inj_on] using hf _ = ∏ x in s.filter fun x => x ∈ Set.Range f, g x :=
        by 
          rw [image_preimage]

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (x «expr ∈ » s)
@[toAdditive]
theorem prod_preimage [CommMonoidₓ β] (f : α → γ) (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' ↑s)) (g : γ → β)
  (hg : ∀ x _ : x ∈ s, x ∉ Set.Range f → g x = 1) : (∏ x in s.preimage f hf, g (f x)) = ∏ x in s, g x :=
  by 
    classical 
    rw [prod_preimage', prod_filter_of_ne]
    exact fun x hx => Not.imp_symm (hg x hx)

@[toAdditive]
theorem prod_preimage_of_bij [CommMonoidₓ β] (f : α → γ) (s : Finset γ) (hf : Set.BijOn f (f ⁻¹' ↑s) (↑s)) (g : γ → β) :
  (∏ x in s.preimage f hf.inj_on, g (f x)) = ∏ x in s, g x :=
  prod_preimage _ _ hf.inj_on g$ fun x hxs hxf => (hxf$ hf.subset_range hxs).elim

end Finset

