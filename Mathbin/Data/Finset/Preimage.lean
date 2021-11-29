import Mathbin.Data.Set.Finite 
import Mathbin.Algebra.BigOperators.Basic

/-!
# Preimage of a `finset` under an injective map.
-/


open Set Function

open_locale BigOperators

universe u v w x

variable{α : Type u}{β : Type v}{ι : Sort w}{γ : Type x}

namespace Finset

section Preimage

/-- Preimage of `s : finset β` under a map `f` injective of `f ⁻¹' s` as a `finset`.  -/
noncomputable def preimage (s : Finset β) (f : α → β) (hf : Set.InjOn f (f ⁻¹' «expr↑ » s)) : Finset α :=
  (s.finite_to_set.preimage hf).toFinset

@[simp]
theorem mem_preimage {f : α → β} {s : Finset β} {hf : Set.InjOn f (f ⁻¹' «expr↑ » s)} {x : α} :
  x ∈ preimage s f hf ↔ f x ∈ s :=
  Set.Finite.mem_to_finset _

@[simp, normCast]
theorem coe_preimage {f : α → β} (s : Finset β) (hf : Set.InjOn f (f ⁻¹' «expr↑ » s)) :
  («expr↑ » (preimage s f hf) : Set α) = f ⁻¹' «expr↑ » s :=
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
theorem preimage_inter [DecidableEq α] [DecidableEq β] {f : α → β} {s t : Finset β}
  (hs : Set.InjOn f (f ⁻¹' «expr↑ » s)) (ht : Set.InjOn f (f ⁻¹' «expr↑ » t)) :
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
  (hf : Function.Injective f) : preimage («expr ᶜ» s) f (hf.inj_on _) = «expr ᶜ» (preimage s f (hf.inj_on _)) :=
  Finset.coe_injective
    (by 
      simp )

theorem monotone_preimage {f : α → β} (h : injective f) : Monotone fun s => preimage s f (h.inj_on _) :=
  fun s t hst x hx => mem_preimage.2 (hst$ mem_preimage.1 hx)

theorem image_subset_iff_subset_preimage [DecidableEq β] {f : α → β} {s : Finset α} {t : Finset β}
  (hf : Set.InjOn f (f ⁻¹' «expr↑ » t)) : s.image f ⊆ t ↔ s ⊆ t.preimage f hf :=
  image_subset_iff.trans$
    by 
      simp only [subset_iff, mem_preimage]

theorem map_subset_iff_subset_preimage {f : α ↪ β} {s : Finset α} {t : Finset β} :
  s.map f ⊆ t ↔ s ⊆ t.preimage f (f.injective.inj_on _) :=
  by 
    classical <;> rw [map_eq_image, image_subset_iff_subset_preimage]

theorem image_preimage [DecidableEq β] (f : α → β) (s : Finset β) [∀ x, Decidable (x ∈ Set.Range f)]
  (hf : Set.InjOn f (f ⁻¹' «expr↑ » s)) : image f (preimage s f hf) = s.filter fun x => x ∈ Set.Range f :=
  Finset.coe_inj.1$
    by 
      simp only [coe_image, coe_preimage, coe_filter, Set.image_preimage_eq_inter_range, Set.sep_mem_eq]

theorem image_preimage_of_bij [DecidableEq β] (f : α → β) (s : Finset β)
  (hf : Set.BijOn f (f ⁻¹' «expr↑ » s) («expr↑ » s)) : image f (preimage s f hf.inj_on) = s :=
  Finset.coe_inj.1$
    by 
      simpa using hf.image_eq

theorem sigma_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a)) (t : Finset α) :
  (t.sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s.filter fun a => a.1 ∈ t :=
  by 
    ext x 
    simp [and_comm]

theorem sigma_preimage_mk_of_subset {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a)) {t : Finset α}
  (ht : s.image Sigma.fst ⊆ t) : (t.sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s :=
  by 
    rw [sigma_preimage_mk, filter_true_of_mem$ image_subset_iff.1 ht]

theorem sigma_image_fst_preimage_mk {β : α → Type _} [DecidableEq α] (s : Finset (Σa, β a)) :
  ((s.image Sigma.fst).Sigma fun a => s.preimage (Sigma.mk a)$ sigma_mk_injective.InjOn _) = s :=
  s.sigma_preimage_mk_of_subset (subset.refl _)

end Preimage

-- error in Data.Finset.Preimage: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[to_additive #[]]
theorem prod_preimage'
[comm_monoid β]
(f : α → γ)
[«expr $ »(decidable_pred, λ x, «expr ∈ »(x, set.range f))]
(s : finset γ)
(hf : set.inj_on f «expr ⁻¹' »(f, «expr↑ »(s)))
(g : γ → β) : «expr = »(«expr∏ in , »((x), s.preimage f hf, g (f x)), «expr∏ in , »((x), s.filter (λ
   x, «expr ∈ »(x, set.range f)), g x)) :=
by haveI [] [] [":=", expr classical.dec_eq γ]; calc
  «expr = »(«expr∏ in , »((x), preimage s f hf, g (f x)), «expr∏ in , »((x), image f (preimage s f hf), g x)) : «expr $ »(eq.symm, «expr $ »(prod_image, by simpa [] [] ["only"] ["[", expr mem_preimage, ",", expr inj_on, "]"] [] ["using", expr hf]))
  «expr = »(..., «expr∏ in , »((x), s.filter (λ
     x, «expr ∈ »(x, set.range f)), g x)) : by rw ["[", expr image_preimage, "]"] []

@[toAdditive]
theorem prod_preimage [CommMonoidₓ β] (f : α → γ) (s : Finset γ) (hf : Set.InjOn f (f ⁻¹' «expr↑ » s)) (g : γ → β)
  (hg : ∀ x (_ : x ∈ s), x ∉ Set.Range f → g x = 1) : (∏x in s.preimage f hf, g (f x)) = ∏x in s, g x :=
  by 
    classical 
    rw [prod_preimage', prod_filter_of_ne]
    exact fun x hx => Not.imp_symm (hg x hx)

@[toAdditive]
theorem prod_preimage_of_bij [CommMonoidₓ β] (f : α → γ) (s : Finset γ)
  (hf : Set.BijOn f (f ⁻¹' «expr↑ » s) («expr↑ » s)) (g : γ → β) :
  (∏x in s.preimage f hf.inj_on, g (f x)) = ∏x in s, g x :=
  prod_preimage _ _ hf.inj_on g$ fun x hxs hxf => (hxf$ hf.subset_range hxs).elim

end Finset

