/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johanes Hölzl, Patrick Massot, Yury Kudryashov, Kevin Wilson, Heather Macbeth

! This file was ported from Lean 3 source module order.filter.prod
! leanprover-community/mathlib commit 63f84d91dd847f50bae04a01071f3a5491934e36
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.Filter.Basic

/-!
# Product and coproduct filters

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `filter.prod f g` (notation: `f ×ᶠ g`) and `filter.coprod f g`. The product
of two filters is the largest filter `l` such that `filter.tendsto prod.fst l f` and
`filter.tendsto prod.snd l g`.

## Implementation details

The product filter cannot be defined using the monad structure on filters. For example:

```lean
F := do {x ← seq, y ← top, return (x, y)}
G := do {y ← top, x ← seq, return (x, y)}
```
hence:
```lean
s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s
s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
```
Now `⋃ i, [i..∞] × {i}` is in `G` but not in `F`.
As product filter we want to have `F` as result.

## Notations

* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`.

-/


open Set

open Filter

namespace Filter

variable {α β γ δ : Type _} {ι : Sort _}

section Prod

variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

#print Filter.prod /-
/-- Product of filters. This is the filter generated by cartesian products
of elements of the component filters. -/
protected def prod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst ⊓ g.comap Prod.snd
#align filter.prod Filter.prod
-/

-- mathport name: filter.prod
scoped infixl:60 " ×ᶠ " => Filter.prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mem_prod {s : Set α} {t : Set β} {f : Filter α} {g : Filter β} (hs : s ∈ f)
    (ht : t ∈ g) : s ×ˢ t ∈ f ×ᶠ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)
#align filter.prod_mem_prod Filter.prod_mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ᶠ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s :=
  by
  simp only [Filter.prod]
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h
#align filter.mem_prod_iff Filter.mem_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_mem_prod_iff {s : Set α} {t : Set β} {f : Filter α} {g : Filter β} [f.ne_bot]
    [g.ne_bot] : s ×ˢ t ∈ f ×ᶠ g ↔ s ∈ f ∧ t ∈ g :=
  ⟨fun h =>
    let ⟨s', hs', t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_of_mem ht').ne_empty,
    fun h => prod_mem_prod h.1 h.2⟩
#align filter.prod_mem_prod_iff Filter.prod_mem_prod_iff

theorem mem_prod_principal {f : Filter α} {s : Set (α × β)} {t : Set β} :
    s ∈ f ×ᶠ 𝓟 t ↔ { a | ∀ b ∈ t, (a, b) ∈ s } ∈ f :=
  by
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff]
  refine' exists₂_congr fun u u_in => ⟨_, fun h => ⟨t, mem_principal_self t, _⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy
#align filter.mem_prod_principal Filter.mem_prod_principal

theorem mem_prod_top {f : Filter α} {s : Set (α × β)} :
    s ∈ f ×ᶠ (⊤ : Filter β) ↔ { a | ∀ b, (a, b) ∈ s } ∈ f :=
  by
  rw [← principal_univ, mem_prod_principal]
  simp only [mem_univ, forall_true_left]
#align filter.mem_prod_top Filter.mem_prod_top

theorem eventually_prod_principal_iff {p : α × β → Prop} {s : Set β} :
    (∀ᶠ x : α × β in f ×ᶠ 𝓟 s, p x) ↔ ∀ᶠ x : α in f, ∀ y : β, y ∈ s → p (x, y) := by
  rw [eventually_iff, eventually_iff, mem_prod_principal]; simp only [mem_set_of_eq]
#align filter.eventually_prod_principal_iff Filter.eventually_prod_principal_iff

theorem comap_prod (f : α → β × γ) (b : Filter β) (c : Filter γ) :
    comap f (b ×ᶠ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c := by
  erw [comap_inf, Filter.comap_comap, Filter.comap_comap]
#align filter.comap_prod Filter.comap_prod

theorem prod_top {f : Filter α} : f ×ᶠ (⊤ : Filter β) = f.comap Prod.fst := by
  rw [Filter.prod, comap_top, inf_top_eq]
#align filter.prod_top Filter.prod_top

theorem sup_prod (f₁ f₂ : Filter α) (g : Filter β) : f₁ ⊔ f₂ ×ᶠ g = (f₁ ×ᶠ g) ⊔ (f₂ ×ᶠ g) := by
  rw [Filter.prod, comap_sup, inf_sup_right, ← Filter.prod, ← Filter.prod]
#align filter.sup_prod Filter.sup_prod

theorem prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ᶠ g₁ ⊔ g₂ = (f ×ᶠ g₁) ⊔ (f ×ᶠ g₂) := by
  rw [Filter.prod, comap_sup, inf_sup_left, ← Filter.prod, ← Filter.prod]
#align filter.prod_sup Filter.prod_sup

theorem eventually_prod_iff {p : α × β → Prop} {f : Filter α} {g : Filter β} :
    (∀ᶠ x in f ×ᶠ g, p x) ↔
      ∃ (pa : α → Prop)(ha : ∀ᶠ x in f, pa x)(pb : β → Prop)(hb : ∀ᶠ y in g, pb y),
        ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) :=
  by simpa only [Set.prod_subset_iff] using @mem_prod_iff α β p f g
#align filter.eventually_prod_iff Filter.eventually_prod_iff

theorem tendsto_fst {f : Filter α} {g : Filter β} : Tendsto Prod.fst (f ×ᶠ g) f :=
  tendsto_inf_left tendsto_comap
#align filter.tendsto_fst Filter.tendsto_fst

theorem tendsto_snd {f : Filter α} {g : Filter β} : Tendsto Prod.snd (f ×ᶠ g) g :=
  tendsto_inf_right tendsto_comap
#align filter.tendsto_snd Filter.tendsto_snd

theorem Tendsto.prod_mk {f : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ}
    (h₁ : Tendsto m₁ f g) (h₂ : Tendsto m₂ f h) : Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ᶠ h) :=
  tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩
#align filter.tendsto.prod_mk Filter.Tendsto.prod_mk

theorem tendsto_prod_swap {α1 α2 : Type _} {a1 : Filter α1} {a2 : Filter α2} :
    Tendsto (Prod.swap : α1 × α2 → α2 × α1) (a1 ×ᶠ a2) (a2 ×ᶠ a1) :=
  tendsto_snd.prod_mk tendsto_fst
#align filter.tendsto_prod_swap Filter.tendsto_prod_swap

theorem Eventually.prod_inl {la : Filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : Filter β) :
    ∀ᶠ x in la ×ᶠ lb, p (x : α × β).1 :=
  tendsto_fst.Eventually h
#align filter.eventually.prod_inl Filter.Eventually.prod_inl

#print Filter.Eventually.prod_inr /-
theorem Eventually.prod_inr {lb : Filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : Filter α) :
    ∀ᶠ x in la ×ᶠ lb, p (x : α × β).2 :=
  tendsto_snd.Eventually h
#align filter.eventually.prod_inr Filter.Eventually.prod_inr
-/

theorem Eventually.prod_mk {la : Filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x) {lb : Filter β}
    {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) : ∀ᶠ p in la ×ᶠ lb, pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl lb).And (hb.prod_inr la)
#align filter.eventually.prod_mk Filter.Eventually.prod_mk

theorem EventuallyEq.prod_map {δ} {la : Filter α} {fa ga : α → γ} (ha : fa =ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb =ᶠ[lb] gb) :
    Prod.map fa fb =ᶠ[la ×ᶠ lb] Prod.map ga gb :=
  (Eventually.prod_mk ha hb).mono fun x h => Prod.ext h.1 h.2
#align filter.eventually_eq.prod_map Filter.EventuallyEq.prod_map

theorem EventuallyLE.prod_map {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α → γ} (ha : fa ≤ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb ≤ᶠ[lb] gb) :
    Prod.map fa fb ≤ᶠ[la ×ᶠ lb] Prod.map ga gb :=
  Eventually.prod_mk ha hb
#align filter.eventually_le.prod_map Filter.EventuallyLE.prod_map

theorem Eventually.curry {la : Filter α} {lb : Filter β} {p : α × β → Prop}
    (h : ∀ᶠ x in la ×ᶠ lb, p x) : ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) :=
  by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb
#align filter.eventually.curry Filter.Eventually.curry

#print Filter.Eventually.diag_of_prod /-
/-- A fact that is eventually true about all pairs `l ×ᶠ l` is eventually true about
all diagonal pairs `(i, i)` -/
theorem Eventually.diag_of_prod {f : Filter α} {p : α × α → Prop} (h : ∀ᶠ i in f ×ᶠ f, p i) :
    ∀ᶠ i in f, p (i, i) :=
  by
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  apply (ht.and hs).mono fun x hx => hst hx.1 hx.2
#align filter.eventually.diag_of_prod Filter.Eventually.diag_of_prod
-/

theorem Eventually.diag_of_prod_left {f : Filter α} {g : Filter γ} {p : (α × α) × γ → Prop} :
    (∀ᶠ x in f ×ᶠ f ×ᶠ g, p x) → ∀ᶠ x : α × γ in f ×ᶠ g, p ((x.1, x.1), x.2) :=
  by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  refine' (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2, Prod.mk.eta]
#align filter.eventually.diag_of_prod_left Filter.Eventually.diag_of_prod_left

theorem Eventually.diag_of_prod_right {f : Filter α} {g : Filter γ} {p : α × γ × γ → Prop} :
    (∀ᶠ x in f ×ᶠ (g ×ᶠ g), p x) → ∀ᶠ x : α × γ in f ×ᶠ g, p (x.1, x.2, x.2) :=
  by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  refine' (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2, Prod.mk.eta]
#align filter.eventually.diag_of_prod_right Filter.Eventually.diag_of_prod_right

#print Filter.tendsto_diag /-
theorem tendsto_diag : Tendsto (fun i => (i, i)) f (f ×ᶠ f) :=
  tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod
#align filter.tendsto_diag Filter.tendsto_diag
-/

theorem prod_iInf_left [Nonempty ι] {f : ι → Filter α} {g : Filter β} :
    (⨅ i, f i) ×ᶠ g = ⨅ i, f i ×ᶠ g := by rw [Filter.prod, comap_infi, iInf_inf];
  simp only [Filter.prod, eq_self_iff_true]
#align filter.prod_infi_left Filter.prod_iInf_left

theorem prod_iInf_right [Nonempty ι] {f : Filter α} {g : ι → Filter β} :
    (f ×ᶠ ⨅ i, g i) = ⨅ i, f ×ᶠ g i := by rw [Filter.prod, comap_infi, inf_iInf];
  simp only [Filter.prod, eq_self_iff_true]
#align filter.prod_infi_right Filter.prod_iInf_right

@[mono]
theorem prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)
#align filter.prod_mono Filter.prod_mono

theorem prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ ≤ f₂) : f₁ ×ᶠ g ≤ f₂ ×ᶠ g :=
  Filter.prod_mono hf rfl.le
#align filter.prod_mono_left Filter.prod_mono_left

theorem prod_mono_right (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ ≤ g₂) : f ×ᶠ g₁ ≤ f ×ᶠ g₂ :=
  Filter.prod_mono rfl.le hf
#align filter.prod_mono_right Filter.prod_mono_right

#print Filter.prod_comap_comap_eq /-
theorem prod_comap_comap_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
    comap m₁ f₁ ×ᶠ comap m₂ f₂ = comap (fun p : β₁ × β₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) := by
  simp only [Filter.prod, comap_comap, eq_self_iff_true, comap_inf]
#align filter.prod_comap_comap_eq Filter.prod_comap_comap_eq
-/

#print Filter.prod_comm' /-
theorem prod_comm' : f ×ᶠ g = comap Prod.swap (g ×ᶠ f) := by
  simp only [Filter.prod, comap_comap, (· ∘ ·), inf_comm, Prod.fst_swap, eq_self_iff_true,
    Prod.snd_swap, comap_inf]
#align filter.prod_comm' Filter.prod_comm'
-/

#print Filter.prod_comm /-
theorem prod_comm : f ×ᶠ g = map (fun p : β × α => (p.2, p.1)) (g ×ᶠ f) := by
  rw [prod_comm', ← map_swap_eq_comap_swap]; rfl
#align filter.prod_comm Filter.prod_comm
-/

@[simp]
theorem map_fst_prod (f : Filter α) (g : Filter β) [NeBot g] : map Prod.fst (f ×ᶠ g) = f :=
  by
  refine' le_antisymm tendsto_fst fun s hs => _
  rw [mem_map, mem_prod_iff] at hs
  rcases hs with ⟨t₁, h₁, t₂, h₂, hs⟩
  rw [← image_subset_iff, fst_image_prod] at hs
  exacts[mem_of_superset h₁ hs, nonempty_of_mem h₂]
#align filter.map_fst_prod Filter.map_fst_prod

@[simp]
theorem map_snd_prod (f : Filter α) (g : Filter β) [NeBot f] : map Prod.snd (f ×ᶠ g) = g := by
  rw [prod_comm, map_map, (· ∘ ·), map_fst_prod]
#align filter.map_snd_prod Filter.map_snd_prod

@[simp]
theorem prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ ↔ f₁ ≤ f₂ ∧ g₁ ≤ g₂ :=
  ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩
#align filter.prod_le_prod Filter.prod_le_prod

@[simp]
theorem prod_inj {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ᶠ g₁ = f₂ ×ᶠ g₂ ↔ f₁ = f₂ ∧ g₁ = g₂ :=
  by
  refine' ⟨fun h => _, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ ≤ f₂ ∧ g₁ ≤ g₂ := prod_le_prod.1 h.le
  haveI := ne_bot_of_le hle.1; haveI := ne_bot_of_le hle.2
  exact ⟨hle.1.antisymm <| (prod_le_prod.1 h.ge).1, hle.2.antisymm <| (prod_le_prod.1 h.ge).2⟩
#align filter.prod_inj Filter.prod_inj

theorem eventually_swap_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in f ×ᶠ g, p x) ↔ ∀ᶠ y : β × α in g ×ᶠ f, p y.symm := by
  rw [prod_comm, eventually_map]; simpa
#align filter.eventually_swap_iff Filter.eventually_swap_iff

theorem prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ) (f ×ᶠ g ×ᶠ h) = f ×ᶠ (g ×ᶠ h) := by
  simp_rw [← comap_equiv_symm, Filter.prod, comap_inf, comap_comap, inf_assoc, Function.comp,
    Equiv.prodAssoc_symm_apply]
#align filter.prod_assoc Filter.prod_assoc

theorem prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) = f ×ᶠ g ×ᶠ h := by
  simp_rw [map_equiv_symm, Filter.prod, comap_inf, comap_comap, inf_assoc, Function.comp,
    Equiv.prodAssoc_apply]
#align filter.prod_assoc_symm Filter.prod_assoc_symm

theorem tendsto_prodAssoc {f : Filter α} {g : Filter β} {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ) (f ×ᶠ g ×ᶠ h) (f ×ᶠ (g ×ᶠ h)) :=
  (prod_assoc f g h).le
#align filter.tendsto_prod_assoc Filter.tendsto_prodAssoc

theorem tendsto_prodAssoc_symm {f : Filter α} {g : Filter β} {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ).symm (f ×ᶠ (g ×ᶠ h)) (f ×ᶠ g ×ᶠ h) :=
  (prod_assoc_symm f g h).le
#align filter.tendsto_prod_assoc_symm Filter.tendsto_prodAssoc_symm

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_prod {f : Filter α} {g : Filter β} {h : Filter γ} {k : Filter δ} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (f ×ᶠ g ×ᶠ (h ×ᶠ k)) =
      f ×ᶠ h ×ᶠ (g ×ᶠ k) :=
  by simp_rw [map_swap4_eq_comap, Filter.prod, comap_inf, comap_comap, inf_assoc, inf_left_comm]
#align filter.map_swap4_prod Filter.map_swap4_prod

theorem tendsto_swap4_prod {f : Filter α} {g : Filter β} {h : Filter γ} {k : Filter δ} :
    Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) (f ×ᶠ g ×ᶠ (h ×ᶠ k))
      (f ×ᶠ h ×ᶠ (g ×ᶠ k)) :=
  map_swap4_prod.le
#align filter.tendsto_swap4_prod Filter.tendsto_swap4_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Filter.prod_map_map_eq /-
theorem prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map m₁ f₁ ×ᶠ map m₂ f₂ = map (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
  le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
      Filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) <|
        calc
          (m₁ '' s₁) ×ˢ (m₂ '' s₂) = (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) '' s₁ ×ˢ s₂ :=
            Set.prod_image_image_eq
          _ ⊆ _ := by rwa [image_subset_iff]
          )
    ((Tendsto.comp le_rfl tendsto_fst).prod_mk (Tendsto.comp le_rfl tendsto_snd))
#align filter.prod_map_map_eq Filter.prod_map_map_eq
-/

theorem prod_map_map_eq' {α₁ : Type _} {α₂ : Type _} {β₁ : Type _} {β₂ : Type _} (f : α₁ → α₂)
    (g : β₁ → β₂) (F : Filter α₁) (G : Filter β₁) :
    map f F ×ᶠ map g G = map (Prod.map f g) (F ×ᶠ G) :=
  prod_map_map_eq
#align filter.prod_map_map_eq' Filter.prod_map_map_eq'

theorem le_prod_map_fst_snd {f : Filter (α × β)} : f ≤ map Prod.fst f ×ᶠ map Prod.snd f :=
  le_inf le_comap_map le_comap_map
#align filter.le_prod_map_fst_snd Filter.le_prod_map_fst_snd

theorem Tendsto.prod_map {δ : Type _} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a ×ᶠ b) (c ×ᶠ d) :=
  by
  erw [tendsto, ← prod_map_map_eq]
  exact Filter.prod_mono hf hg
#align filter.tendsto.prod_map Filter.Tendsto.prod_map

protected theorem map_prod (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map m (f ×ᶠ g) = (f.map fun a b => m (a, b)).seq g :=
  by
  simp [Filter.ext_iff, mem_prod_iff, mem_map_seq_iff]
  intro s
  constructor
  exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩
#align filter.map_prod Filter.map_prod

theorem prod_eq {f : Filter α} {g : Filter β} : f ×ᶠ g = (f.map Prod.mk).seq g :=
  by
  have h := f.map_prod id g
  rwa [map_id] at h
#align filter.prod_eq Filter.prod_eq

theorem prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} :
    (f₁ ×ᶠ g₁) ⊓ (f₂ ×ᶠ g₂) = f₁ ⊓ f₂ ×ᶠ g₁ ⊓ g₂ := by
  simp only [Filter.prod, comap_inf, inf_comm, inf_assoc, inf_left_comm]
#align filter.prod_inf_prod Filter.prod_inf_prod

@[simp]
theorem prod_bot {f : Filter α} : f ×ᶠ (⊥ : Filter β) = ⊥ := by simp [Filter.prod]
#align filter.prod_bot Filter.prod_bot

@[simp]
theorem bot_prod {g : Filter β} : (⊥ : Filter α) ×ᶠ g = ⊥ := by simp [Filter.prod]
#align filter.bot_prod Filter.bot_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ᶠ 𝓟 t = 𝓟 (s ×ˢ t) := by
  simp only [Filter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal] <;>
    rfl
#align filter.prod_principal_principal Filter.prod_principal_principal

#print Filter.pure_prod /-
@[simp]
theorem pure_prod {a : α} {f : Filter β} : pure a ×ᶠ f = map (Prod.mk a) f := by
  rw [prod_eq, map_pure, pure_seq_eq_map]
#align filter.pure_prod Filter.pure_prod
-/

theorem map_pure_prod (f : α → β → γ) (a : α) (B : Filter β) :
    Filter.map (Function.uncurry f) (pure a ×ᶠ B) = Filter.map (f a) B := by rw [Filter.pure_prod];
  rfl
#align filter.map_pure_prod Filter.map_pure_prod

@[simp]
theorem prod_pure {f : Filter α} {b : β} : f ×ᶠ pure b = map (fun a => (a, b)) f := by
  rw [prod_eq, seq_pure, map_map]
#align filter.prod_pure Filter.prod_pure

theorem prod_pure_pure {a : α} {b : β} : pure a ×ᶠ pure b = pure (a, b) := by simp
#align filter.prod_pure_pure Filter.prod_pure_pure

theorem prod_eq_bot {f : Filter α} {g : Filter β} : f ×ᶠ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ :=
  by
  constructor
  · intro h
    rcases mem_prod_iff.1 (empty_mem_iff_bot.2 h) with ⟨s, hs, t, ht, hst⟩
    rw [subset_empty_iff, Set.prod_eq_empty_iff] at hst
    cases' hst with s_eq t_eq
    · left; exact empty_mem_iff_bot.1 (s_eq ▸ hs)
    · right; exact empty_mem_iff_bot.1 (t_eq ▸ ht)
  · rintro (rfl | rfl)
    exact bot_prod
    exact prod_bot
#align filter.prod_eq_bot Filter.prod_eq_bot

theorem prod_neBot {f : Filter α} {g : Filter β} : NeBot (f ×ᶠ g) ↔ NeBot f ∧ NeBot g := by
  simp only [ne_bot_iff, Ne, prod_eq_bot, not_or]
#align filter.prod_ne_bot Filter.prod_neBot

theorem NeBot.prod {f : Filter α} {g : Filter β} (hf : NeBot f) (hg : NeBot g) : NeBot (f ×ᶠ g) :=
  prod_neBot.2 ⟨hf, hg⟩
#align filter.ne_bot.prod Filter.NeBot.prod

#print Filter.prod_neBot' /-
instance prod_neBot' {f : Filter α} {g : Filter β} [hf : NeBot f] [hg : NeBot g] : NeBot (f ×ᶠ g) :=
  hf.Prod hg
#align filter.prod_ne_bot' Filter.prod_neBot'
-/

theorem tendsto_prod_iff {f : α × β → γ} {x : Filter α} {y : Filter β} {z : Filter γ} :
    Filter.Tendsto f (x ×ᶠ y) z ↔ ∀ W ∈ z, ∃ U ∈ x, ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
  by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self_iff]
#align filter.tendsto_prod_iff Filter.tendsto_prod_iff

theorem tendsto_prod_iff' {f : Filter α} {g : Filter β} {g' : Filter γ} {s : α → β × γ} :
    Tendsto s f (g ×ᶠ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g' := by
  unfold Filter.prod; simp only [tendsto_inf, tendsto_comap_iff, iff_self_iff]
#align filter.tendsto_prod_iff' Filter.tendsto_prod_iff'

end Prod

/-! ### Coproducts of filters -/


section Coprod

variable {f : Filter α} {g : Filter β}

#print Filter.coprod /-
/-- Coproduct of filters. -/
protected def coprod (f : Filter α) (g : Filter β) : Filter (α × β) :=
  f.comap Prod.fst ⊔ g.comap Prod.snd
#align filter.coprod Filter.coprod
-/

theorem mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f.coprod g ↔ (∃ t₁ ∈ f, Prod.fst ⁻¹' t₁ ⊆ s) ∧ ∃ t₂ ∈ g, Prod.snd ⁻¹' t₂ ⊆ s := by
  simp [Filter.coprod]
#align filter.mem_coprod_iff Filter.mem_coprod_iff

@[simp]
theorem bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l := by
  simp [Filter.coprod]
#align filter.bot_coprod Filter.bot_coprod

@[simp]
theorem coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l := by
  simp [Filter.coprod]
#align filter.coprod_bot Filter.coprod_bot

theorem bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥ := by simp
#align filter.bot_coprod_bot Filter.bot_coprod_bot

theorem compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} :
    sᶜ ∈ la.coprod lb ↔ (Prod.fst '' s)ᶜ ∈ la ∧ (Prod.snd '' s)ᶜ ∈ lb := by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]
#align filter.compl_mem_coprod Filter.compl_mem_coprod

@[mono]
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.coprod g₁ ≤ f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)
#align filter.coprod_mono Filter.coprod_mono

theorem coprod_neBot_iff : (f.coprod g).ne_bot ↔ f.ne_bot ∧ Nonempty β ∨ Nonempty α ∧ g.ne_bot := by
  simp [Filter.coprod]
#align filter.coprod_ne_bot_iff Filter.coprod_neBot_iff

@[instance]
theorem coprod_neBot_left [NeBot f] [Nonempty β] : (f.coprod g).ne_bot :=
  coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)
#align filter.coprod_ne_bot_left Filter.coprod_neBot_left

#print Filter.coprod_neBot_right /-
@[instance]
theorem coprod_neBot_right [NeBot g] [Nonempty α] : (f.coprod g).ne_bot :=
  coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)
#align filter.coprod_ne_bot_right Filter.coprod_neBot_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem principal_coprod_principal (s : Set α) (t : Set β) : (𝓟 s).coprod (𝓟 t) = 𝓟 ((sᶜ ×ˢ tᶜ)ᶜ) :=
  by
  rw [Filter.coprod, comap_principal, comap_principal, sup_principal, Set.prod_eq, compl_inter,
    preimage_compl, preimage_compl, compl_compl, compl_compl]
#align filter.principal_coprod_principal Filter.principal_coprod_principal

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prod_map_const_id_principal_coprod_principal` below.
theorem map_prod_map_coprod_le.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map (Prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) :=
  by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine' ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ _⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ _⟩⟩ <;> convert hx
#align filter.map_prod_map_coprod_le Filter.map_prod_map_coprod_le

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Characterization of the coproduct of the `filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `λ a, b` and the second under the identity function.
Together with the next lemma, `map_prod_map_const_id_principal_coprod_principal`, this provides an
example showing that the inequality in the lemma `map_prod_map_coprod_le` can be strict. -/
theorem map_const_principal_coprod_map_id_principal {α β ι : Type _} (a : α) (b : β) (i : ι) :
    (map (fun _ : α => b) (𝓟 {a})).coprod (map id (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ univ ∪ univ ×ˢ ({i} : Set ι)) :=
  by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    image_id, prod_univ, univ_prod]
#align filter.map_const_principal_coprod_map_id_principal Filter.map_const_principal_coprod_map_id_principal

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Characterization of the `filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `prod.map` of two functions, respectively the constant function `λ a, b` and the
identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prod_map_coprod_le` can be strict. -/
theorem map_prod_map_const_id_principal_coprod_principal {α β ι : Type _} (a : α) (b : β) (i : ι) :
    map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ (univ : Set ι)) :=
  by
  rw [principal_coprod_principal, map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, h₁, h₂, h₃⟩
    simp
  · rintro ⟨h₁, h₂⟩
    use (a, i')
    simpa using h₁.symm
#align filter.map_prod_map_const_id_principal_coprod_principal Filter.map_prod_map_const_id_principal_coprod_principal

theorem Tendsto.prod_map_coprod {δ : Type _} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a.coprod b) (c.coprod d) :=
  map_prod_map_coprod_le.trans (coprod_mono hf hg)
#align filter.tendsto.prod_map_coprod Filter.Tendsto.prod_map_coprod

end Coprod

end Filter

