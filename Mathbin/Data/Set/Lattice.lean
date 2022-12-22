/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Johannes Hölzl, Mario Carneiro

! This file was ported from Lean 3 source module data.set.lattice
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteBooleanAlgebra
import Mathbin.Order.Directed
import Mathbin.Order.GaloisConnection

/-!
# The set lattice

This file provides usual set notation for unions and intersections, a `complete_lattice` instance
for `set α`, and some more set constructions.

## Main declarations

* `set.Union`: Union of an indexed family of sets.
* `set.Inter`: Intersection of an indexed family of sets.
* `set.sInter`: **s**et **Inter**. Intersection of sets belonging to a set of sets.
* `set.sUnion`: **s**et **Union**. Union of sets belonging to a set of sets. This is actually
  defined in core Lean.
* `set.sInter_eq_bInter`, `set.sUnion_eq_bInter`: Shows that `⋂₀ s = ⋂ x ∈ s, x` and
  `⋃₀ s = ⋃ x ∈ s, x`.
* `set.complete_boolean_algebra`: `set α` is a `complete_boolean_algebra` with `≤ = ⊆`, `< = ⊂`,
  `⊓ = ∩`, `⊔ = ∪`, `⨅ = ⋂`, `⨆ = ⋃` and `\` as the set difference. See `set.boolean_algebra`.
* `set.kern_image`: For a function `f : α → β`, `s.kern_image f` is the set of `y` such that
  `f ⁻¹ y ⊆ s`.
* `set.seq`: Union of the image of a set under a **seq**uence of functions. `seq s t` is the union
  of `f '' t` over all `f ∈ s`, where `t : set α` and `s : set (α → β)`.
* `set.Union_eq_sigma_of_disjoint`: Equivalence between `⋃ i, t i` and `Σ i, t i`, where `t` is an
  indexed family of disjoint sets.

## Naming convention

In lemma names,
* `⋃ i, s i` is called `Union`
* `⋂ i, s i` is called `Inter`
* `⋃ i j, s i j` is called `Union₂`. This is a `Union` inside a `Union`.
* `⋂ i j, s i j` is called `Inter₂`. This is an `Inter` inside an `Inter`.
* `⋃ i ∈ s, t i` is called `bUnion` for "bounded `Union`". This is the special case of `Union₂`
  where `j : i ∈ s`.
* `⋂ i ∈ s, t i` is called `bInter` for "bounded `Inter`". This is the special case of `Inter₂`
  where `j : i ∈ s`.

## Notation

* `⋃`: `set.Union`
* `⋂`: `set.Inter`
* `⋃₀`: `set.sUnion`
* `⋂₀`: `set.sInter`
-/


open Function Tactic Set

universe u

variable {α β γ : Type _} {ι ι' ι₂ : Sort _} {κ κ₁ κ₂ : ι → Sort _} {κ' : ι' → Sort _}

namespace Set

/-! ### Complete lattice and complete Boolean algebra instances -/


instance : InfSet (Set α) :=
  ⟨fun s => { a | ∀ t ∈ s, a ∈ t }⟩

instance : SupSet (Set α) :=
  ⟨fun s => { a | ∃ t ∈ s, a ∈ t }⟩

/-- Intersection of a set of sets. -/
def sInter (S : Set (Set α)) : Set α :=
  infₛ S
#align set.sInter Set.sInter

#print Set.sUnion /-
/-- Union of a set of sets. -/
def sUnion (S : Set (Set α)) : Set α :=
  supₛ S
#align set.sUnion Set.sUnion
-/

-- mathport name: «expr⋂₀ »
prefix:110 "⋂₀ " => sInter

@[simp]
theorem mem_sInter {x : α} {S : Set (Set α)} : x ∈ ⋂₀ S ↔ ∀ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sInter Set.mem_sInter

@[simp]
theorem mem_sUnion {x : α} {S : Set (Set α)} : x ∈ ⋃₀S ↔ ∃ t ∈ S, x ∈ t :=
  Iff.rfl
#align set.mem_sUnion Set.mem_sUnion

/- warning: set.Union -> Set.union is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u_2}} {ι : Sort.{u_4}}, (ι -> (Set.{u_2} β)) -> (Set.{u_2} β)
but is expected to have type
  forall {β : Type.{u_1}}, (Set.{u_1} β) -> (Set.{u_1} β) -> (Set.{u_1} β)
Case conversion may be inaccurate. Consider using '#align set.Union Set.unionₓ'. -/
/-- Indexed union of a family of sets -/
def union (s : ι → Set β) : Set β :=
  supᵢ s
#align set.Union Set.union

/- warning: set.Inter -> Set.inter is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u_2}} {ι : Sort.{u_4}}, (ι -> (Set.{u_2} β)) -> (Set.{u_2} β)
but is expected to have type
  forall {β : Type.{u_1}}, (Set.{u_1} β) -> (Set.{u_1} β) -> (Set.{u_1} β)
Case conversion may be inaccurate. Consider using '#align set.Inter Set.interₓ'. -/
/-- Indexed intersection of a family of sets -/
def inter (s : ι → Set β) : Set β :=
  infi s
#align set.Inter Set.inter

-- mathport name: «expr⋃ , »
notation3"⋃ "(...)", "r:(scoped f => union f) => r

-- mathport name: «expr⋂ , »
notation3"⋂ "(...)", "r:(scoped f => inter f) => r

@[simp]
theorem Sup_eq_sUnion (S : Set (Set α)) : supₛ S = ⋃₀S :=
  rfl
#align set.Sup_eq_sUnion Set.Sup_eq_sUnion

@[simp]
theorem Inf_eq_sInter (S : Set (Set α)) : infₛ S = ⋂₀ S :=
  rfl
#align set.Inf_eq_sInter Set.Inf_eq_sInter

@[simp]
theorem supr_eq_Union (s : ι → Set α) : supᵢ s = union s :=
  rfl
#align set.supr_eq_Union Set.supr_eq_Union

@[simp]
theorem infi_eq_Inter (s : ι → Set α) : infi s = inter s :=
  rfl
#align set.infi_eq_Inter Set.infi_eq_Inter

@[simp]
theorem mem_Union {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i :=
  ⟨fun ⟨t, ⟨⟨a, (t_eq : s a = t)⟩, (h : x ∈ t)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
#align set.mem_Union Set.mem_Union

@[simp]
theorem mem_Inter {x : α} {s : ι → Set α} : (x ∈ ⋂ i, s i) ↔ ∀ i, x ∈ s i :=
  ⟨fun (h : ∀ a ∈ { a : Set α | ∃ i, s i = a }, x ∈ a) a => h (s a) ⟨a, rfl⟩,
    fun h t ⟨a, (Eq : s a = t)⟩ => Eq ▸ h a⟩
#align set.mem_Inter Set.mem_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_Union₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋃ (i) (j), s i j) ↔ ∃ i j, x ∈ s i j := by
  simp_rw [mem_Union]
#align set.mem_Union₂ Set.mem_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_Inter₂ {x : γ} {s : ∀ i, κ i → Set γ} : (x ∈ ⋂ (i) (j), s i j) ↔ ∀ i j, x ∈ s i j := by
  simp_rw [mem_Inter]
#align set.mem_Inter₂ Set.mem_Inter₂

theorem mem_Union_of_mem {s : ι → Set α} {a : α} (i : ι) (ha : a ∈ s i) : a ∈ ⋃ i, s i :=
  mem_Union.2 ⟨i, ha⟩
#align set.mem_Union_of_mem Set.mem_Union_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_Union₂_of_mem {s : ∀ i, κ i → Set α} {a : α} {i : ι} (j : κ i) (ha : a ∈ s i j) :
    a ∈ ⋃ (i) (j), s i j :=
  mem_Union₂.2 ⟨i, j, ha⟩
#align set.mem_Union₂_of_mem Set.mem_Union₂_of_mem

theorem mem_Inter_of_mem {s : ι → Set α} {a : α} (h : ∀ i, a ∈ s i) : a ∈ ⋂ i, s i :=
  mem_Inter.2 h
#align set.mem_Inter_of_mem Set.mem_Inter_of_mem

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem mem_Inter₂_of_mem {s : ∀ i, κ i → Set α} {a : α} (h : ∀ i j, a ∈ s i j) :
    a ∈ ⋂ (i) (j), s i j :=
  mem_Inter₂.2 h
#align set.mem_Inter₂_of_mem Set.mem_Inter₂_of_mem

instance : CompleteBooleanAlgebra (Set α) :=
  { Set.booleanAlgebra with 
    sup := supₛ
    inf := infₛ
    le_Sup := fun s t t_in a a_in => ⟨t, ⟨t_in, a_in⟩⟩
    Sup_le := fun s t h a ⟨t', ⟨t'_in, a_in⟩⟩ => h t' t'_in a_in
    le_Inf := fun s t h a a_in t' t'_in => h t' t'_in a_in
    Inf_le := fun s t t_in a h => h _ t_in
    infi_sup_le_sup_Inf := fun s S x => Iff.mp <| by simp [forall_or_left]
    inf_Sup_le_supr_inf := fun s S x => Iff.mp <| by simp [exists_and_left] }

section GaloisConnection

variable {f : α → β}

protected theorem image_preimage : GaloisConnection (image f) (preimage f) := fun a b =>
  image_subset_iff
#align set.image_preimage Set.image_preimage

/-- `kern_image f s` is the set of `y` such that `f ⁻¹ y ⊆ s`. -/
def kernImage (f : α → β) (s : Set α) : Set β :=
  { y | ∀ ⦃x⦄, f x = y → x ∈ s }
#align set.kern_image Set.kernImage

protected theorem preimage_kern_image : GaloisConnection (preimage f) (kernImage f) := fun a b =>
  ⟨fun h x hx y hy =>
    have : f y ∈ a := hy.symm ▸ hx
    h this,
    fun h x (hx : f x ∈ a) => h hx rfl⟩
#align set.preimage_kern_image Set.preimage_kern_image

end GaloisConnection

/-! ### Union and intersection over an indexed family of sets -/


instance : OrderTop (Set α) where 
  top := univ
  le_top := by simp

@[congr]
theorem Union_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : union f₁ = union f₂ :=
  supᵢ_congr_Prop pq f
#align set.Union_congr_Prop Set.Union_congr_Prop

@[congr]
theorem Inter_congr_Prop {p q : Prop} {f₁ : p → Set α} {f₂ : q → Set α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : inter f₁ = inter f₂ :=
  infᵢ_congr_Prop pq f
#align set.Inter_congr_Prop Set.Inter_congr_Prop

theorem Union_plift_up (f : PLift ι → Set α) : (⋃ i, f (PLift.up i)) = ⋃ i, f i :=
  supᵢ_plift_up _
#align set.Union_plift_up Set.Union_plift_up

theorem Union_plift_down (f : ι → Set α) : (⋃ i, f (PLift.down i)) = ⋃ i, f i :=
  supᵢ_plift_down _
#align set.Union_plift_down Set.Union_plift_down

theorem Inter_plift_up (f : PLift ι → Set α) : (⋂ i, f (PLift.up i)) = ⋂ i, f i :=
  infᵢ_plift_up _
#align set.Inter_plift_up Set.Inter_plift_up

theorem Inter_plift_down (f : ι → Set α) : (⋂ i, f (PLift.down i)) = ⋂ i, f i :=
  infᵢ_plift_down _
#align set.Inter_plift_down Set.Inter_plift_down

theorem Union_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋃ h : p, s) = if p then s else ∅ :=
  supᵢ_eq_if _
#align set.Union_eq_if Set.Union_eq_if

theorem Union_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋃ h : p, s h) = if h : p then s h else ∅ :=
  supᵢ_eq_dif _
#align set.Union_eq_dif Set.Union_eq_dif

theorem Inter_eq_if {p : Prop} [Decidable p] (s : Set α) : (⋂ h : p, s) = if p then s else univ :=
  infᵢ_eq_if _
#align set.Inter_eq_if Set.Inter_eq_if

theorem Infi_eq_dif {p : Prop} [Decidable p] (s : p → Set α) :
    (⋂ h : p, s h) = if h : p then s h else univ :=
  infᵢ_eq_dif _
#align set.Infi_eq_dif Set.Infi_eq_dif

theorem exists_set_mem_of_union_eq_top {ι : Type _} (t : Set ι) (s : ι → Set β)
    (w : (⋃ i ∈ t, s i) = ⊤) (x : β) : ∃ i ∈ t, x ∈ s i := by
  have p : x ∈ ⊤ := Set.mem_univ x
  simpa only [← w, Set.mem_Union] using p
#align set.exists_set_mem_of_union_eq_top Set.exists_set_mem_of_union_eq_top

theorem nonempty_of_union_eq_top_of_nonempty {ι : Type _} (t : Set ι) (s : ι → Set α)
    (H : Nonempty α) (w : (⋃ i ∈ t, s i) = ⊤) : t.Nonempty := by
  obtain ⟨x, m, -⟩ := exists_set_mem_of_union_eq_top t s w H.some
  exact ⟨x, m⟩
#align set.nonempty_of_union_eq_top_of_nonempty Set.nonempty_of_union_eq_top_of_nonempty

theorem set_of_exists (p : ι → β → Prop) : { x | ∃ i, p i x } = ⋃ i, { x | p i x } :=
  ext fun i => mem_Union.symm
#align set.set_of_exists Set.set_of_exists

theorem set_of_forall (p : ι → β → Prop) : { x | ∀ i, p i x } = ⋂ i, { x | p i x } :=
  ext fun i => mem_Inter.symm
#align set.set_of_forall Set.set_of_forall

theorem Union_subset {s : ι → Set α} {t : Set α} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
  @supᵢ_le (Set α) _ _ _ _ h
#align set.Union_subset Set.Union_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_subset {s : ∀ i, κ i → Set α} {t : Set α} (h : ∀ i j, s i j ⊆ t) :
    (⋃ (i) (j), s i j) ⊆ t :=
  Union_subset fun x => Union_subset (h x)
#align set.Union₂_subset Set.Union₂_subset

theorem subset_Inter {t : Set β} {s : ι → Set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
  @le_infᵢ (Set β) _ _ _ _ h
#align set.subset_Inter Set.subset_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_Inter₂ {s : Set α} {t : ∀ i, κ i → Set α} (h : ∀ i j, s ⊆ t i j) :
    s ⊆ ⋂ (i) (j), t i j :=
  subset_Inter fun x => subset_Inter <| h x
#align set.subset_Inter₂ Set.subset_Inter₂

@[simp]
theorem Union_subset_iff {s : ι → Set α} {t : Set α} : (⋃ i, s i) ⊆ t ↔ ∀ i, s i ⊆ t :=
  ⟨fun h i => Subset.trans (le_supᵢ s _) h, Union_subset⟩
#align set.Union_subset_iff Set.Union_subset_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_subset_iff {s : ∀ i, κ i → Set α} {t : Set α} :
    (⋃ (i) (j), s i j) ⊆ t ↔ ∀ i j, s i j ⊆ t := by simp_rw [Union_subset_iff]
#align set.Union₂_subset_iff Set.Union₂_subset_iff

@[simp]
theorem subset_Inter_iff {s : Set α} {t : ι → Set α} : (s ⊆ ⋂ i, t i) ↔ ∀ i, s ⊆ t i :=
  @le_infᵢ_iff (Set α) _ _ _ _
#align set.subset_Inter_iff Set.subset_Inter_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem subset_Inter₂_iff {s : Set α} {t : ∀ i, κ i → Set α} :
    (s ⊆ ⋂ (i) (j), t i j) ↔ ∀ i j, s ⊆ t i j := by simp_rw [subset_Inter_iff]
#align set.subset_Inter₂_iff Set.subset_Inter₂_iff

theorem subset_Union : ∀ (s : ι → Set β) (i : ι), s i ⊆ ⋃ i, s i :=
  le_supᵢ
#align set.subset_Union Set.subset_Union

theorem Inter_subset : ∀ (s : ι → Set β) (i : ι), (⋂ i, s i) ⊆ s i :=
  infᵢ_le
#align set.Inter_subset Set.Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem subset_Union₂ {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : s i j ⊆ ⋃ (i) (j), s i j :=
  @le_supᵢ₂ (Set α) _ _ _ _ i j
#align set.subset_Union₂ Set.subset_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_subset {s : ∀ i, κ i → Set α} (i : ι) (j : κ i) : (⋂ (i) (j), s i j) ⊆ s i j :=
  @infᵢ₂_le (Set α) _ _ _ _ i j
#align set.Inter₂_subset Set.Inter₂_subset

/-- This rather trivial consequence of `subset_Union`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem subset_Union_of_subset {s : Set α} {t : ι → Set α} (i : ι) (h : s ⊆ t i) : s ⊆ ⋃ i, t i :=
  @le_supᵢ_of_le (Set α) _ _ _ _ i h
#align set.subset_Union_of_subset Set.subset_Union_of_subset

/-- This rather trivial consequence of `Inter_subset`is convenient with `apply`, and has `i`
explicit for this purpose. -/
theorem Inter_subset_of_subset {s : ι → Set α} {t : Set α} (i : ι) (h : s i ⊆ t) : (⋂ i, s i) ⊆ t :=
  @infᵢ_le_of_le (Set α) _ _ _ _ i h
#align set.Inter_subset_of_subset Set.Inter_subset_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `subset_Union₂` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem subset_Union₂_of_subset {s : Set α} {t : ∀ i, κ i → Set α} (i : ι) (j : κ i)
    (h : s ⊆ t i j) : s ⊆ ⋃ (i) (j), t i j :=
  @le_supᵢ₂_of_le (Set α) _ _ _ _ _ i j h
#align set.subset_Union₂_of_subset Set.subset_Union₂_of_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- This rather trivial consequence of `Inter₂_subset` is convenient with `apply`, and has `i` and
`j` explicit for this purpose. -/
theorem Inter₂_subset_of_subset {s : ∀ i, κ i → Set α} {t : Set α} (i : ι) (j : κ i)
    (h : s i j ⊆ t) : (⋂ (i) (j), s i j) ⊆ t :=
  @infᵢ₂_le_of_le (Set α) _ _ _ _ _ i j h
#align set.Inter₂_subset_of_subset Set.Inter₂_subset_of_subset

theorem Union_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supᵢ_mono (Set α) _ _ s t h
#align set.Union_mono Set.Union_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋃ (i) (j), s i j) ⊆ ⋃ (i) (j), t i j :=
  @supᵢ₂_mono (Set α) _ _ _ s t h
#align set.Union₂_mono Set.Union₂_mono

theorem Inter_mono {s t : ι → Set α} (h : ∀ i, s i ⊆ t i) : (⋂ i, s i) ⊆ ⋂ i, t i :=
  @infᵢ_mono (Set α) _ _ s t h
#align set.Inter_mono Set.Inter_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_mono {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j ⊆ t i j) :
    (⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), t i j :=
  @infᵢ₂_mono (Set α) _ _ _ s t h
#align set.Inter₂_mono Set.Inter₂_mono

theorem Union_mono' {s : ι → Set α} {t : ι₂ → Set α} (h : ∀ i, ∃ j, s i ⊆ t j) :
    (⋃ i, s i) ⊆ ⋃ i, t i :=
  @supᵢ_mono' (Set α) _ _ _ s t h
#align set.Union_mono' Set.Union_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem Union₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i j, ∃ i' j', s i j ⊆ t i' j') : (⋃ (i) (j), s i j) ⊆ ⋃ (i') (j'), t i' j' :=
  @supᵢ₂_mono' (Set α) _ _ _ _ _ s t h
#align set.Union₂_mono' Set.Union₂_mono'

theorem Inter_mono' {s : ι → Set α} {t : ι' → Set α} (h : ∀ j, ∃ i, s i ⊆ t j) :
    (⋂ i, s i) ⊆ ⋂ j, t j :=
  Set.subset_Inter fun j =>
    let ⟨i, hi⟩ := h j
    Inter_subset_of_subset i hi
#align set.Inter_mono' Set.Inter_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' j') -/
theorem Inter₂_mono' {s : ∀ i, κ i → Set α} {t : ∀ i', κ' i' → Set α}
    (h : ∀ i' j', ∃ i j, s i j ⊆ t i' j') : (⋂ (i) (j), s i j) ⊆ ⋂ (i') (j'), t i' j' :=
  subset_Inter₂_iff.2 fun i' j' =>
    let ⟨i, j, hst⟩ := h i' j'
    (Inter₂_subset _ _).trans hst
#align set.Inter₂_mono' Set.Inter₂_mono'

theorem Union₂_subset_Union (κ : ι → Sort _) (s : ι → Set α) : (⋃ (i) (j : κ i), s i) ⊆ ⋃ i, s i :=
  Union_mono fun i => Union_subset fun h => Subset.rfl
#align set.Union₂_subset_Union Set.Union₂_subset_Union

theorem Inter_subset_Inter₂ (κ : ι → Sort _) (s : ι → Set α) : (⋂ i, s i) ⊆ ⋂ (i) (j : κ i), s i :=
  Inter_mono fun i => subset_Inter fun h => Subset.rfl
#align set.Inter_subset_Inter₂ Set.Inter_subset_Inter₂

theorem Union_set_of (P : ι → α → Prop) : (⋃ i, { x : α | P i x }) = { x : α | ∃ i, P i x } := by
  ext
  exact mem_Union
#align set.Union_set_of Set.Union_set_of

theorem Inter_set_of (P : ι → α → Prop) : (⋂ i, { x : α | P i x }) = { x : α | ∀ i, P i x } := by
  ext
  exact mem_Inter
#align set.Inter_set_of Set.Inter_set_of

theorem Union_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋃ x, f x) = ⋃ y, g y :=
  h1.supr_congr h h2
#align set.Union_congr_of_surjective Set.Union_congr_of_surjective

theorem Inter_congr_of_surjective {f : ι → Set α} {g : ι₂ → Set α} (h : ι → ι₂) (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⋂ x, f x) = ⋂ y, g y :=
  h1.infi_congr h h2
#align set.Inter_congr_of_surjective Set.Inter_congr_of_surjective

theorem Union_const [Nonempty ι] (s : Set β) : (⋃ i : ι, s) = s :=
  supᵢ_const
#align set.Union_const Set.Union_const

theorem Inter_const [Nonempty ι] (s : Set β) : (⋂ i : ι, s) = s :=
  infᵢ_const
#align set.Inter_const Set.Inter_const

@[simp]
theorem compl_Union (s : ι → Set β) : (⋃ i, s i)ᶜ = ⋂ i, s iᶜ :=
  compl_supᵢ
#align set.compl_Union Set.compl_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_Union₂ (s : ∀ i, κ i → Set α) : (⋃ (i) (j), s i j)ᶜ = ⋂ (i) (j), s i jᶜ := by
  simp_rw [compl_Union]
#align set.compl_Union₂ Set.compl_Union₂

@[simp]
theorem compl_Inter (s : ι → Set β) : (⋂ i, s i)ᶜ = ⋃ i, s iᶜ :=
  compl_infᵢ
#align set.compl_Inter Set.compl_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem compl_Inter₂ (s : ∀ i, κ i → Set α) : (⋂ (i) (j), s i j)ᶜ = ⋃ (i) (j), s i jᶜ := by
  simp_rw [compl_Inter]
#align set.compl_Inter₂ Set.compl_Inter₂

-- classical -- complete_boolean_algebra
theorem Union_eq_compl_Inter_compl (s : ι → Set β) : (⋃ i, s i) = (⋂ i, s iᶜ)ᶜ := by
  simp only [compl_Inter, compl_compl]
#align set.Union_eq_compl_Inter_compl Set.Union_eq_compl_Inter_compl

-- classical -- complete_boolean_algebra
theorem Inter_eq_compl_Union_compl (s : ι → Set β) : (⋂ i, s i) = (⋃ i, s iᶜ)ᶜ := by
  simp only [compl_Union, compl_compl]
#align set.Inter_eq_compl_Union_compl Set.Inter_eq_compl_Union_compl

theorem inter_Union (s : Set β) (t : ι → Set β) : (s ∩ ⋃ i, t i) = ⋃ i, s ∩ t i :=
  inf_supᵢ_eq _ _
#align set.inter_Union Set.inter_Union

theorem Union_inter (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∩ s = ⋃ i, t i ∩ s :=
  supᵢ_inf_eq _ _
#align set.Union_inter Set.Union_inter

theorem Union_union_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋃ i, s i ∪ t i) = (⋃ i, s i) ∪ ⋃ i, t i :=
  supᵢ_sup_eq
#align set.Union_union_distrib Set.Union_union_distrib

theorem Inter_inter_distrib (s : ι → Set β) (t : ι → Set β) :
    (⋂ i, s i ∩ t i) = (⋂ i, s i) ∩ ⋂ i, t i :=
  infᵢ_inf_eq
#align set.Inter_inter_distrib Set.Inter_inter_distrib

theorem union_Union [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∪ ⋃ i, t i) = ⋃ i, s ∪ t i :=
  sup_supᵢ
#align set.union_Union Set.union_Union

theorem Union_union [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋃ i, t i) ∪ s = ⋃ i, t i ∪ s :=
  supᵢ_sup
#align set.Union_union Set.Union_union

theorem inter_Inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (s ∩ ⋂ i, t i) = ⋂ i, s ∩ t i :=
  inf_infᵢ
#align set.inter_Inter Set.inter_Inter

theorem Inter_inter [Nonempty ι] (s : Set β) (t : ι → Set β) : (⋂ i, t i) ∩ s = ⋂ i, t i ∩ s :=
  infᵢ_inf
#align set.Inter_inter Set.Inter_inter

-- classical
theorem union_Inter (s : Set β) (t : ι → Set β) : (s ∪ ⋂ i, t i) = ⋂ i, s ∪ t i :=
  sup_infᵢ_eq _ _
#align set.union_Inter Set.union_Inter

theorem Inter_union (s : ι → Set β) (t : Set β) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.Inter_union Set.Inter_union

theorem Union_diff (s : Set β) (t : ι → Set β) : (⋃ i, t i) \ s = ⋃ i, t i \ s :=
  Union_inter _ _
#align set.Union_diff Set.Union_diff

theorem diff_Union [Nonempty ι] (s : Set β) (t : ι → Set β) : (s \ ⋃ i, t i) = ⋂ i, s \ t i := by
  rw [diff_eq, compl_Union, inter_Inter] <;> rfl
#align set.diff_Union Set.diff_Union

theorem diff_Inter (s : Set β) (t : ι → Set β) : (s \ ⋂ i, t i) = ⋃ i, s \ t i := by
  rw [diff_eq, compl_Inter, inter_Union] <;> rfl
#align set.diff_Inter Set.diff_Inter

theorem directed_on_Union {r} {f : ι → Set α} (hd : Directed (· ⊆ ·) f)
    (h : ∀ x, DirectedOn r (f x)) : DirectedOn r (⋃ x, f x) := by
  simp only [DirectedOn, exists_prop, mem_Union, exists_imp] <;>
    exact fun a₁ b₁ fb₁ a₂ b₂ fb₂ =>
      let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂
      let ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂)
      ⟨x, ⟨z, xf⟩, xa₁, xa₂⟩
#align set.directed_on_Union Set.directed_on_Union

theorem Union_inter_subset {ι α} {s t : ι → Set α} : (⋃ i, s i ∩ t i) ⊆ (⋃ i, s i) ∩ ⋃ i, t i :=
  le_supᵢ_inf_supᵢ s t
#align set.Union_inter_subset Set.Union_inter_subset

theorem Union_inter_of_monotone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_monotone hs ht
#align set.Union_inter_of_monotone Set.Union_inter_of_monotone

theorem Union_inter_of_antitone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋃ i, s i ∩ t i) = (⋃ i, s i) ∩ ⋃ i, t i :=
  supᵢ_inf_of_antitone hs ht
#align set.Union_inter_of_antitone Set.Union_inter_of_antitone

theorem Inter_union_of_monotone {ι α} [Preorder ι] [IsDirected ι (swap (· ≤ ·))] {s t : ι → Set α}
    (hs : Monotone s) (ht : Monotone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_monotone hs ht
#align set.Inter_union_of_monotone Set.Inter_union_of_monotone

theorem Inter_union_of_antitone {ι α} [Preorder ι] [IsDirected ι (· ≤ ·)] {s t : ι → Set α}
    (hs : Antitone s) (ht : Antitone t) : (⋂ i, s i ∪ t i) = (⋂ i, s i) ∪ ⋂ i, t i :=
  infᵢ_sup_of_antitone hs ht
#align set.Inter_union_of_antitone Set.Inter_union_of_antitone

/-- An equality version of this lemma is `Union_Inter_of_monotone` in `data.set.finite`. -/
theorem Union_Inter_subset {s : ι → ι' → Set α} : (⋃ j, ⋂ i, s i j) ⊆ ⋂ i, ⋃ j, s i j :=
  supᵢ_infᵢ_le_infᵢ_supᵢ (flip s)
#align set.Union_Inter_subset Set.Union_Inter_subset

theorem Union_option {ι} (s : Option ι → Set α) : (⋃ o, s o) = s none ∪ ⋃ i, s (some i) :=
  supᵢ_option s
#align set.Union_option Set.Union_option

theorem Inter_option {ι} (s : Option ι → Set α) : (⋂ o, s o) = s none ∩ ⋂ i, s (some i) :=
  infᵢ_option s
#align set.Inter_option Set.Inter_option

section

variable (p : ι → Prop) [DecidablePred p]

theorem Union_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋃ i, if h : p i then f i h else g i h) = (⋃ (i) (h : p i), f i h) ∪ ⋃ (i) (h : ¬p i), g i h :=
  supᵢ_dite _ _ _
#align set.Union_dite Set.Union_dite

theorem Union_ite (f g : ι → Set α) :
    (⋃ i, if p i then f i else g i) = (⋃ (i) (h : p i), f i) ∪ ⋃ (i) (h : ¬p i), g i :=
  Union_dite _ _ _
#align set.Union_ite Set.Union_ite

theorem Inter_dite (f : ∀ i, p i → Set α) (g : ∀ i, ¬p i → Set α) :
    (⋂ i, if h : p i then f i h else g i h) = (⋂ (i) (h : p i), f i h) ∩ ⋂ (i) (h : ¬p i), g i h :=
  infᵢ_dite _ _ _
#align set.Inter_dite Set.Inter_dite

theorem Inter_ite (f g : ι → Set α) :
    (⋂ i, if p i then f i else g i) = (⋂ (i) (h : p i), f i) ∩ ⋂ (i) (h : ¬p i), g i :=
  Inter_dite _ _ _
#align set.Inter_ite Set.Inter_ite

end

theorem image_projection_prod {ι : Type _} {α : ι → Type _} {v : ∀ i : ι, Set (α i)}
    (hv : (pi univ v).Nonempty) (i : ι) :
    ((fun x : ∀ i : ι, α i => x i) '' ⋂ k, (fun x : ∀ j : ι, α j => x k) ⁻¹' v k) = v i := by
  classical 
    apply subset.antisymm
    · simp [Inter_subset]
    · intro y y_in
      simp only [mem_image, mem_Inter, mem_preimage]
      rcases hv with ⟨z, hz⟩
      refine' ⟨Function.update z i y, _, update_same i y z⟩
      rw [@forall_update_iff ι α _ z i y fun i t => t ∈ v i]
      exact ⟨y_in, fun j hj => by simpa using hz j⟩
#align set.image_projection_prod Set.image_projection_prod

/-! ### Unions and intersections indexed by `Prop` -/


theorem Inter_false {s : False → Set α} : inter s = univ :=
  infᵢ_false
#align set.Inter_false Set.Inter_false

theorem Union_false {s : False → Set α} : union s = ∅ :=
  supᵢ_false
#align set.Union_false Set.Union_false

@[simp]
theorem Inter_true {s : True → Set α} : inter s = s trivial :=
  infᵢ_true
#align set.Inter_true Set.Inter_true

@[simp]
theorem Union_true {s : True → Set α} : union s = s trivial :=
  supᵢ_true
#align set.Union_true Set.Union_true

@[simp]
theorem Inter_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋂ x, f x) = ⋂ (i) (h : p i), f ⟨i, h⟩ :=
  infᵢ_exists
#align set.Inter_exists Set.Inter_exists

@[simp]
theorem Union_exists {p : ι → Prop} {f : Exists p → Set α} :
    (⋃ x, f x) = ⋃ (i) (h : p i), f ⟨i, h⟩ :=
  supᵢ_exists
#align set.Union_exists Set.Union_exists

@[simp]
theorem Union_empty : (⋃ i : ι, ∅ : Set α) = ∅ :=
  supᵢ_bot
#align set.Union_empty Set.Union_empty

@[simp]
theorem Inter_univ : (⋂ i : ι, univ : Set α) = univ :=
  infᵢ_top
#align set.Inter_univ Set.Inter_univ

section

variable {s : ι → Set α}

@[simp]
theorem Union_eq_empty : (⋃ i, s i) = ∅ ↔ ∀ i, s i = ∅ :=
  supᵢ_eq_bot
#align set.Union_eq_empty Set.Union_eq_empty

@[simp]
theorem Inter_eq_univ : (⋂ i, s i) = univ ↔ ∀ i, s i = univ :=
  infᵢ_eq_top
#align set.Inter_eq_univ Set.Inter_eq_univ

@[simp]
theorem nonempty_Union : (⋃ i, s i).Nonempty ↔ ∃ i, (s i).Nonempty := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_Union Set.nonempty_Union

@[simp]
theorem nonempty_bUnion {t : Set α} {s : α → Set β} :
    (⋃ i ∈ t, s i).Nonempty ↔ ∃ i ∈ t, (s i).Nonempty := by simp [nonempty_iff_ne_empty]
#align set.nonempty_bUnion Set.nonempty_bUnion

theorem Union_nonempty_index (s : Set α) (t : s.Nonempty → Set β) :
    (⋃ h, t h) = ⋃ x ∈ s, t ⟨x, ‹_›⟩ :=
  supᵢ_exists
#align set.Union_nonempty_index Set.Union_nonempty_index

end

@[simp]
theorem Inter_Inter_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋂ (x) (h : x = b), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_left
#align set.Inter_Inter_eq_left Set.Inter_Inter_eq_left

@[simp]
theorem Inter_Inter_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋂ (x) (h : b = x), s x h) = s b rfl :=
  infᵢ_infᵢ_eq_right
#align set.Inter_Inter_eq_right Set.Inter_Inter_eq_right

@[simp]
theorem Union_Union_eq_left {b : β} {s : ∀ x : β, x = b → Set α} :
    (⋃ (x) (h : x = b), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_left
#align set.Union_Union_eq_left Set.Union_Union_eq_left

@[simp]
theorem Union_Union_eq_right {b : β} {s : ∀ x : β, b = x → Set α} :
    (⋃ (x) (h : b = x), s x h) = s b rfl :=
  supᵢ_supᵢ_eq_right
#align set.Union_Union_eq_right Set.Union_Union_eq_right

theorem Inter_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋂ h, s h) = (⋂ h : p, s (Or.inl h)) ∩ ⋂ h : q, s (Or.inr h) :=
  infᵢ_or
#align set.Inter_or Set.Inter_or

theorem Union_or {p q : Prop} (s : p ∨ q → Set α) :
    (⋃ h, s h) = (⋃ i, s (Or.inl i)) ∪ ⋃ j, s (Or.inr j) :=
  supᵢ_or
#align set.Union_or Set.Union_or

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem Union_and {p q : Prop} (s : p ∧ q → Set α) : (⋃ h, s h) = ⋃ (hp) (hq), s ⟨hp, hq⟩ :=
  supᵢ_and
#align set.Union_and Set.Union_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (hp hq) -/
theorem Inter_and {p q : Prop} (s : p ∧ q → Set α) : (⋂ h, s h) = ⋂ (hp) (hq), s ⟨hp, hq⟩ :=
  infᵢ_and
#align set.Inter_and Set.Inter_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem Union_comm (s : ι → ι' → Set α) : (⋃ (i) (i'), s i i') = ⋃ (i') (i), s i i' :=
  supᵢ_comm
#align set.Union_comm Set.Union_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i i') -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i' i) -/
theorem Inter_comm (s : ι → ι' → Set α) : (⋂ (i) (i'), s i i') = ⋂ (i') (i), s i i' :=
  infᵢ_comm
#align set.Inter_comm Set.Inter_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem Union₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋃ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋃ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  supᵢ₂_comm _
#align set.Union₂_comm Set.Union₂_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem Inter₂_comm (s : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → Set α) :
    (⋂ (i₁) (j₁) (i₂) (j₂), s i₁ j₁ i₂ j₂) = ⋂ (i₂) (j₂) (i₁) (j₁), s i₁ j₁ i₂ j₂ :=
  infᵢ₂_comm _
#align set.Inter₂_comm Set.Inter₂_comm

@[simp]
theorem bUnion_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋃ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [Union_and, @Union_comm _ ι']
#align set.bUnion_and Set.bUnion_and

@[simp]
theorem bUnion_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋃ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [Union_and, @Union_comm _ ι]
#align set.bUnion_and' Set.bUnion_and'

@[simp]
theorem bInter_and (p : ι → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p x ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p x ∧ q x y), s x y h) =
      ⋂ (x : ι) (hx : p x) (y : ι') (hy : q x y), s x y ⟨hx, hy⟩ :=
  by simp only [Inter_and, @Inter_comm _ ι']
#align set.bInter_and Set.bInter_and

@[simp]
theorem bInter_and' (p : ι' → Prop) (q : ι → ι' → Prop) (s : ∀ x y, p y ∧ q x y → Set α) :
    (⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x y h) =
      ⋂ (y : ι') (hy : p y) (x : ι) (hx : q x y), s x y ⟨hy, hx⟩ :=
  by simp only [Inter_and, @Inter_comm _ ι]
#align set.bInter_and' Set.bInter_and'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem Union_Union_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋃ (x) (h), s x h) = s b (Or.inl rfl) ∪ ⋃ (x) (h : p x), s x (Or.inr h) := by
  simp only [Union_or, Union_union_distrib, Union_Union_eq_left]
#align set.Union_Union_eq_or_left Set.Union_Union_eq_or_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x h) -/
@[simp]
theorem Inter_Inter_eq_or_left {b : β} {p : β → Prop} {s : ∀ x : β, x = b ∨ p x → Set α} :
    (⋂ (x) (h), s x h) = s b (Or.inl rfl) ∩ ⋂ (x) (h : p x), s x (Or.inr h) := by
  simp only [Inter_or, Inter_inter_distrib, Inter_Inter_eq_left]
#align set.Inter_Inter_eq_or_left Set.Inter_Inter_eq_or_left

/-! ### Bounded unions and intersections -/


/-- A specialization of `mem_Union₂`. -/
theorem mem_bUnion {s : Set α} {t : α → Set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
    y ∈ ⋃ x ∈ s, t x :=
  mem_Union₂_of_mem xs ytx
#align set.mem_bUnion Set.mem_bUnion

/-- A specialization of `mem_Inter₂`. -/
theorem mem_bInter {s : Set α} {t : α → Set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) : y ∈ ⋂ x ∈ s, t x :=
  mem_Inter₂_of_mem h
#align set.mem_bInter Set.mem_bInter

/-- A specialization of `subset_Union₂`. -/
theorem subset_bUnion_of_mem {s : Set α} {u : α → Set β} {x : α} (xs : x ∈ s) :
    u x ⊆ ⋃ x ∈ s, u x :=
  subset_Union₂ x xs
#align set.subset_bUnion_of_mem Set.subset_bUnion_of_mem

/-- A specialization of `Inter₂_subset`. -/
theorem bInter_subset_of_mem {s : Set α} {t : α → Set β} {x : α} (xs : x ∈ s) :
    (⋂ x ∈ s, t x) ⊆ t x :=
  Inter₂_subset x xs
#align set.bInter_subset_of_mem Set.bInter_subset_of_mem

theorem bUnion_subset_bUnion_left {s s' : Set α} {t : α → Set β} (h : s ⊆ s') :
    (⋃ x ∈ s, t x) ⊆ ⋃ x ∈ s', t x :=
  Union₂_subset fun x hx => subset_bUnion_of_mem <| h hx
#align set.bUnion_subset_bUnion_left Set.bUnion_subset_bUnion_left

theorem bInter_subset_bInter_left {s s' : Set α} {t : α → Set β} (h : s' ⊆ s) :
    (⋂ x ∈ s, t x) ⊆ ⋂ x ∈ s', t x :=
  subset_Inter₂ fun x hx => bInter_subset_of_mem <| h hx
#align set.bInter_subset_bInter_left Set.bInter_subset_bInter_left

theorem bUnion_mono {s s' : Set α} {t t' : α → Set β} (hs : s' ⊆ s) (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋃ x ∈ s', t x) ⊆ ⋃ x ∈ s, t' x :=
  (bUnion_subset_bUnion_left hs).trans <| Union₂_mono h
#align set.bUnion_mono Set.bUnion_mono

theorem bInter_mono {s s' : Set α} {t t' : α → Set β} (hs : s ⊆ s') (h : ∀ x ∈ s, t x ⊆ t' x) :
    (⋂ x ∈ s', t x) ⊆ ⋂ x ∈ s, t' x :=
  (bInter_subset_bInter_left hs).trans <| Inter₂_mono h
#align set.bInter_mono Set.bInter_mono

theorem Union_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋃ i, s i) = ⋃ i, t i :=
  supᵢ_congr h
#align set.Union_congr Set.Union_congr

theorem Inter_congr {s t : ι → Set α} (h : ∀ i, s i = t i) : (⋂ i, s i) = ⋂ i, t i :=
  infᵢ_congr h
#align set.Inter_congr Set.Inter_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋃ (i) (j), s i j) = ⋃ (i) (j), t i j :=
  Union_congr fun i => Union_congr <| h i
#align set.Union₂_congr Set.Union₂_congr

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_congr {s t : ∀ i, κ i → Set α} (h : ∀ i j, s i j = t i j) :
    (⋂ (i) (j), s i j) = ⋂ (i) (j), t i j :=
  Inter_congr fun i => Inter_congr <| h i
#align set.Inter₂_congr Set.Inter₂_congr

theorem bUnion_eq_Union (s : Set α) (t : ∀ x ∈ s, Set β) : (⋃ x ∈ s, t x ‹_›) = ⋃ x : s, t x x.2 :=
  supᵢ_subtype'
#align set.bUnion_eq_Union Set.bUnion_eq_Union

theorem bInter_eq_Inter (s : Set α) (t : ∀ x ∈ s, Set β) : (⋂ x ∈ s, t x ‹_›) = ⋂ x : s, t x x.2 :=
  infᵢ_subtype'
#align set.bInter_eq_Inter Set.bInter_eq_Inter

theorem Union_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋃ x : { x // p x }, s x) = ⋃ (x) (hx : p x), s ⟨x, hx⟩ :=
  supᵢ_subtype
#align set.Union_subtype Set.Union_subtype

theorem Inter_subtype (p : α → Prop) (s : { x // p x } → Set β) :
    (⋂ x : { x // p x }, s x) = ⋂ (x) (hx : p x), s ⟨x, hx⟩ :=
  infᵢ_subtype
#align set.Inter_subtype Set.Inter_subtype

theorem bInter_empty (u : α → Set β) : (⋂ x ∈ (∅ : Set α), u x) = univ :=
  infᵢ_emptyset
#align set.bInter_empty Set.bInter_empty

theorem bInter_univ (u : α → Set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
  infᵢ_univ
#align set.bInter_univ Set.bInter_univ

@[simp]
theorem bUnion_self (s : Set α) : (⋃ x ∈ s, s) = s :=
  Subset.antisymm (Union₂_subset fun x hx => Subset.refl s) fun x hx => mem_bUnion hx hx
#align set.bUnion_self Set.bUnion_self

@[simp]
theorem Union_nonempty_self (s : Set α) : (⋃ h : s.Nonempty, s) = s := by
  rw [Union_nonempty_index, bUnion_self]
#align set.Union_nonempty_self Set.Union_nonempty_self

-- TODO(Jeremy): here is an artifact of the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.
theorem bInter_singleton (a : α) (s : α → Set β) : (⋂ x ∈ ({a} : Set α), s x) = s a :=
  infᵢ_singleton
#align set.bInter_singleton Set.bInter_singleton

theorem bInter_union (s t : Set α) (u : α → Set β) :
    (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ ⋂ x ∈ t, u x :=
  infᵢ_union
#align set.bInter_union Set.bInter_union

theorem bInter_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋂ x ∈ insert a s, t x) = t a ∩ ⋂ x ∈ s, t x := by simp
#align set.bInter_insert Set.bInter_insert

-- TODO(Jeremy): another example of where an annotation is needed
theorem bInter_pair (a b : α) (s : α → Set β) : (⋂ x ∈ ({a, b} : Set α), s x) = s a ∩ s b := by
  rw [bInter_insert, bInter_singleton]
#align set.bInter_pair Set.bInter_pair

theorem bInter_inter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, f i ∩ t) = (⋂ i ∈ s, f i) ∩ t := by
  haveI : Nonempty s := hs.to_subtype
  simp [bInter_eq_Inter, ← Inter_inter]
#align set.bInter_inter Set.bInter_inter

theorem inter_bInter {ι α : Type _} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    (⋂ i ∈ s, t ∩ f i) = t ∩ ⋂ i ∈ s, f i := by
  rw [inter_comm, ← bInter_inter hs]
  simp [inter_comm]
#align set.inter_bInter Set.inter_bInter

theorem bUnion_empty (s : α → Set β) : (⋃ x ∈ (∅ : Set α), s x) = ∅ :=
  supᵢ_emptyset
#align set.bUnion_empty Set.bUnion_empty

theorem bUnion_univ (s : α → Set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
  supᵢ_univ
#align set.bUnion_univ Set.bUnion_univ

theorem bUnion_singleton (a : α) (s : α → Set β) : (⋃ x ∈ ({a} : Set α), s x) = s a :=
  supᵢ_singleton
#align set.bUnion_singleton Set.bUnion_singleton

@[simp]
theorem bUnion_of_singleton (s : Set α) : (⋃ x ∈ s, {x}) = s :=
  ext <| by simp
#align set.bUnion_of_singleton Set.bUnion_of_singleton

theorem bUnion_union (s t : Set α) (u : α → Set β) :
    (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ ⋃ x ∈ t, u x :=
  supᵢ_union
#align set.bUnion_union Set.bUnion_union

@[simp]
theorem Union_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋃ i, f i) = ⋃ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  Union_subtype _ _
#align set.Union_coe_set Set.Union_coe_set

@[simp]
theorem Inter_coe_set {α β : Type _} (s : Set α) (f : s → Set β) :
    (⋂ i, f i) = ⋂ i ∈ s, f ⟨i, ‹i ∈ s›⟩ :=
  Inter_subtype _ _
#align set.Inter_coe_set Set.Inter_coe_set

theorem bUnion_insert (a : α) (s : Set α) (t : α → Set β) :
    (⋃ x ∈ insert a s, t x) = t a ∪ ⋃ x ∈ s, t x := by simp
#align set.bUnion_insert Set.bUnion_insert

theorem bUnion_pair (a b : α) (s : α → Set β) : (⋃ x ∈ ({a, b} : Set α), s x) = s a ∪ s b := by simp
#align set.bUnion_pair Set.bUnion_pair

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem inter_Union₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∩ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ∩ t i j := by simp only [inter_Union]
#align set.inter_Union₂ Set.inter_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_inter (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋃ (i) (j), s i j) ∩ t = ⋃ (i) (j), s i j ∩ t := by simp_rw [Union_inter]
#align set.Union₂_inter Set.Union₂_inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_Inter₂ (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_Inter]
#align set.union_Inter₂ Set.union_Inter₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Inter₂_union (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [Inter_union]
#align set.Inter₂_union Set.Inter₂_union

theorem mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∈ t) (ht : t ∈ S) :
    x ∈ ⋃₀S :=
  ⟨t, ht, hx⟩
#align set.mem_sUnion_of_mem Set.mem_sUnion_of_mem

-- is this theorem really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : Set α} {S : Set (Set α)} (hx : x ∉ ⋃₀S)
    (ht : t ∈ S) : x ∉ t := fun h => hx ⟨t, ht, h⟩
#align set.not_mem_of_not_mem_sUnion Set.not_mem_of_not_mem_sUnion

theorem sInter_subset_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : ⋂₀ S ⊆ t :=
  infₛ_le tS
#align set.sInter_subset_of_mem Set.sInter_subset_of_mem

theorem subset_sUnion_of_mem {S : Set (Set α)} {t : Set α} (tS : t ∈ S) : t ⊆ ⋃₀S :=
  le_supₛ tS
#align set.subset_sUnion_of_mem Set.subset_sUnion_of_mem

theorem subset_sUnion_of_subset {s : Set α} (t : Set (Set α)) (u : Set α) (h₁ : s ⊆ u)
    (h₂ : u ∈ t) : s ⊆ ⋃₀t :=
  Subset.trans h₁ (subset_sUnion_of_mem h₂)
#align set.subset_sUnion_of_subset Set.subset_sUnion_of_subset

theorem sUnion_subset {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t' ⊆ t) : ⋃₀S ⊆ t :=
  supₛ_le h
#align set.sUnion_subset Set.sUnion_subset

@[simp]
theorem sUnion_subset_iff {s : Set (Set α)} {t : Set α} : ⋃₀s ⊆ t ↔ ∀ t' ∈ s, t' ⊆ t :=
  @supₛ_le_iff (Set α) _ _ _
#align set.sUnion_subset_iff Set.sUnion_subset_iff

theorem subset_sInter {S : Set (Set α)} {t : Set α} (h : ∀ t' ∈ S, t ⊆ t') : t ⊆ ⋂₀ S :=
  le_infₛ h
#align set.subset_sInter Set.subset_sInter

@[simp]
theorem subset_sInter_iff {S : Set (Set α)} {t : Set α} : t ⊆ ⋂₀ S ↔ ∀ t' ∈ S, t ⊆ t' :=
  @le_infₛ_iff (Set α) _ _ _
#align set.subset_sInter_iff Set.subset_sInter_iff

theorem sUnion_subset_sUnion {S T : Set (Set α)} (h : S ⊆ T) : ⋃₀S ⊆ ⋃₀T :=
  sUnion_subset fun s hs => subset_sUnion_of_mem (h hs)
#align set.sUnion_subset_sUnion Set.sUnion_subset_sUnion

theorem sInter_subset_sInter {S T : Set (Set α)} (h : S ⊆ T) : ⋂₀ T ⊆ ⋂₀ S :=
  subset_sInter fun s hs => sInter_subset_of_mem (h hs)
#align set.sInter_subset_sInter Set.sInter_subset_sInter

@[simp]
theorem sUnion_empty : ⋃₀∅ = (∅ : Set α) :=
  supₛ_empty
#align set.sUnion_empty Set.sUnion_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (univ : Set α) :=
  infₛ_empty
#align set.sInter_empty Set.sInter_empty

@[simp]
theorem sUnion_singleton (s : Set α) : ⋃₀{s} = s :=
  supₛ_singleton
#align set.sUnion_singleton Set.sUnion_singleton

@[simp]
theorem sInter_singleton (s : Set α) : ⋂₀ {s} = s :=
  infₛ_singleton
#align set.sInter_singleton Set.sInter_singleton

@[simp]
theorem sUnion_eq_empty {S : Set (Set α)} : ⋃₀S = ∅ ↔ ∀ s ∈ S, s = ∅ :=
  supₛ_eq_bot
#align set.sUnion_eq_empty Set.sUnion_eq_empty

@[simp]
theorem sInter_eq_univ {S : Set (Set α)} : ⋂₀ S = univ ↔ ∀ s ∈ S, s = univ :=
  infₛ_eq_top
#align set.sInter_eq_univ Set.sInter_eq_univ

@[simp]
theorem nonempty_sUnion {S : Set (Set α)} : (⋃₀S).Nonempty ↔ ∃ s ∈ S, Set.Nonempty s := by
  simp [nonempty_iff_ne_empty]
#align set.nonempty_sUnion Set.nonempty_sUnion

theorem Nonempty.of_sUnion {s : Set (Set α)} (h : (⋃₀s).Nonempty) : s.Nonempty :=
  let ⟨s, hs, _⟩ := nonempty_sUnion.1 h
  ⟨s, hs⟩
#align set.nonempty.of_sUnion Set.Nonempty.of_sUnion

theorem Nonempty.of_sUnion_eq_univ [Nonempty α] {s : Set (Set α)} (h : ⋃₀s = univ) : s.Nonempty :=
  nonempty.of_sUnion <| h.symm ▸ univ_nonempty
#align set.nonempty.of_sUnion_eq_univ Set.Nonempty.of_sUnion_eq_univ

theorem sUnion_union (S T : Set (Set α)) : ⋃₀(S ∪ T) = ⋃₀S ∪ ⋃₀T :=
  supₛ_union
#align set.sUnion_union Set.sUnion_union

theorem sInter_union (S T : Set (Set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T :=
  infₛ_union
#align set.sInter_union Set.sInter_union

@[simp]
theorem sUnion_insert (s : Set α) (T : Set (Set α)) : ⋃₀insert s T = s ∪ ⋃₀T :=
  supₛ_insert
#align set.sUnion_insert Set.sUnion_insert

@[simp]
theorem sInter_insert (s : Set α) (T : Set (Set α)) : ⋂₀ insert s T = s ∩ ⋂₀ T :=
  infₛ_insert
#align set.sInter_insert Set.sInter_insert

@[simp]
theorem sUnion_diff_singleton_empty (s : Set (Set α)) : ⋃₀(s \ {∅}) = ⋃₀s :=
  supₛ_diff_singleton_bot s
#align set.sUnion_diff_singleton_empty Set.sUnion_diff_singleton_empty

@[simp]
theorem sInter_diff_singleton_univ (s : Set (Set α)) : ⋂₀ (s \ {univ}) = ⋂₀ s :=
  infₛ_diff_singleton_top s
#align set.sInter_diff_singleton_univ Set.sInter_diff_singleton_univ

theorem sUnion_pair (s t : Set α) : ⋃₀{s, t} = s ∪ t :=
  supₛ_pair
#align set.sUnion_pair Set.sUnion_pair

theorem sInter_pair (s t : Set α) : ⋂₀ {s, t} = s ∩ t :=
  infₛ_pair
#align set.sInter_pair Set.sInter_pair

@[simp]
theorem sUnion_image (f : α → Set β) (s : Set α) : ⋃₀(f '' s) = ⋃ x ∈ s, f x :=
  supₛ_image
#align set.sUnion_image Set.sUnion_image

@[simp]
theorem sInter_image (f : α → Set β) (s : Set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x :=
  infₛ_image
#align set.sInter_image Set.sInter_image

@[simp]
theorem sUnion_range (f : ι → Set β) : ⋃₀range f = ⋃ x, f x :=
  rfl
#align set.sUnion_range Set.sUnion_range

@[simp]
theorem sInter_range (f : ι → Set β) : ⋂₀ range f = ⋂ x, f x :=
  rfl
#align set.sInter_range Set.sInter_range

theorem Union_eq_univ_iff {f : ι → Set α} : (⋃ i, f i) = univ ↔ ∀ x, ∃ i, x ∈ f i := by
  simp only [eq_univ_iff_forall, mem_Union]
#align set.Union_eq_univ_iff Set.Union_eq_univ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Union₂_eq_univ_iff {s : ∀ i, κ i → Set α} :
    (⋃ (i) (j), s i j) = univ ↔ ∀ a, ∃ i j, a ∈ s i j := by simp only [Union_eq_univ_iff, mem_Union]
#align set.Union₂_eq_univ_iff Set.Union₂_eq_univ_iff

theorem sUnion_eq_univ_iff {c : Set (Set α)} : ⋃₀c = univ ↔ ∀ a, ∃ b ∈ c, a ∈ b := by
  simp only [eq_univ_iff_forall, mem_sUnion]
#align set.sUnion_eq_univ_iff Set.sUnion_eq_univ_iff

-- classical
theorem Inter_eq_empty_iff {f : ι → Set α} : (⋂ i, f i) = ∅ ↔ ∀ x, ∃ i, x ∉ f i := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.Inter_eq_empty_iff Set.Inter_eq_empty_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
theorem Inter₂_eq_empty_iff {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j) = ∅ ↔ ∀ a, ∃ i j, a ∉ s i j := by
  simp only [eq_empty_iff_forall_not_mem, mem_Inter, not_forall]
#align set.Inter₂_eq_empty_iff Set.Inter₂_eq_empty_iff

-- classical
theorem sInter_eq_empty_iff {c : Set (Set α)} : ⋂₀ c = ∅ ↔ ∀ a, ∃ b ∈ c, a ∉ b := by
  simp [Set.eq_empty_iff_forall_not_mem]
#align set.sInter_eq_empty_iff Set.sInter_eq_empty_iff

-- classical
@[simp]
theorem nonempty_Inter {f : ι → Set α} : (⋂ i, f i).Nonempty ↔ ∃ x, ∀ i, x ∈ f i := by
  simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]
#align set.nonempty_Inter Set.nonempty_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
-- classical
@[simp]
theorem nonempty_Inter₂ {s : ∀ i, κ i → Set α} :
    (⋂ (i) (j), s i j).Nonempty ↔ ∃ a, ∀ i j, a ∈ s i j := by
  simp [nonempty_iff_ne_empty, Inter_eq_empty_iff]
#align set.nonempty_Inter₂ Set.nonempty_Inter₂

-- classical
@[simp]
theorem nonempty_sInter {c : Set (Set α)} : (⋂₀ c).Nonempty ↔ ∃ a, ∀ b ∈ c, a ∈ b := by
  simp [nonempty_iff_ne_empty, sInter_eq_empty_iff]
#align set.nonempty_sInter Set.nonempty_sInter

-- classical
theorem compl_sUnion (S : Set (Set α)) : (⋃₀S)ᶜ = ⋂₀ (compl '' S) :=
  ext fun x => by simp
#align set.compl_sUnion Set.compl_sUnion

-- classical
theorem sUnion_eq_compl_sInter_compl (S : Set (Set α)) : ⋃₀S = (⋂₀ (compl '' S))ᶜ := by
  rw [← compl_compl (⋃₀S), compl_sUnion]
#align set.sUnion_eq_compl_sInter_compl Set.sUnion_eq_compl_sInter_compl

-- classical
theorem compl_sInter (S : Set (Set α)) : (⋂₀ S)ᶜ = ⋃₀(compl '' S) := by
  rw [sUnion_eq_compl_sInter_compl, compl_compl_image]
#align set.compl_sInter Set.compl_sInter

-- classical
theorem sInter_eq_compl_sUnion_compl (S : Set (Set α)) : ⋂₀ S = (⋃₀(compl '' S))ᶜ := by
  rw [← compl_compl (⋂₀ S), compl_sInter]
#align set.sInter_eq_compl_sUnion_compl Set.sInter_eq_compl_sUnion_compl

theorem inter_empty_of_inter_sUnion_empty {s t : Set α} {S : Set (Set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀S = ∅) : s ∩ t = ∅ :=
  eq_empty_of_subset_empty <| by
    rw [← h] <;> exact inter_subset_inter_right _ (subset_sUnion_of_mem hs)
#align set.inter_empty_of_inter_sUnion_empty Set.inter_empty_of_inter_sUnion_empty

theorem range_sigma_eq_Union_range {γ : α → Type _} (f : Sigma γ → β) :
    range f = ⋃ a, range fun b => f ⟨a, b⟩ :=
  Set.ext <| by simp
#align set.range_sigma_eq_Union_range Set.range_sigma_eq_Union_range

theorem Union_eq_range_sigma (s : α → Set β) : (⋃ i, s i) = range fun a : Σi, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_sigma Set.Union_eq_range_sigma

theorem Union_eq_range_psigma (s : ι → Set β) : (⋃ i, s i) = range fun a : Σ'i, s i => a.2 := by
  simp [Set.ext_iff]
#align set.Union_eq_range_psigma Set.Union_eq_range_psigma

theorem Union_image_preimage_sigma_mk_eq_self {ι : Type _} {σ : ι → Type _} (s : Set (Sigma σ)) :
    (⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s)) = s := by
  ext x
  simp only [mem_Union, mem_image, mem_preimage]
  constructor
  · rintro ⟨i, a, h, rfl⟩
    exact h
  · intro h
    cases' x with i a
    exact ⟨i, a, h, rfl⟩
#align set.Union_image_preimage_sigma_mk_eq_self Set.Union_image_preimage_sigma_mk_eq_self

theorem Sigma.univ (X : α → Type _) : (Set.univ : Set (Σa, X a)) = ⋃ a, range (Sigma.mk a) :=
  Set.ext fun x =>
    iff_of_true trivial ⟨range (Sigma.mk x.1), Set.mem_range_self _, x.2, Sigma.eta x⟩
#align set.sigma.univ Set.Sigma.univ

theorem sUnion_mono {s t : Set (Set α)} (h : s ⊆ t) : ⋃₀s ⊆ ⋃₀t :=
  sUnion_subset fun t' ht' => subset_sUnion_of_mem <| h ht'
#align set.sUnion_mono Set.sUnion_mono

theorem Union_subset_Union_const {s : Set α} (h : ι → ι₂) : (⋃ i : ι, s) ⊆ ⋃ j : ι₂, s :=
  @supᵢ_const_mono (Set α) ι ι₂ _ s h
#align set.Union_subset_Union_const Set.Union_subset_Union_const

@[simp]
theorem Union_singleton_eq_range {α β : Type _} (f : α → β) : (⋃ x : α, {f x}) = range f := by
  ext x
  simp [@eq_comm _ x]
#align set.Union_singleton_eq_range Set.Union_singleton_eq_range

theorem Union_of_singleton (α : Type _) : (⋃ x, {x} : Set α) = univ := by simp
#align set.Union_of_singleton Set.Union_of_singleton

theorem Union_of_singleton_coe (s : Set α) : (⋃ i : s, {i} : Set α) = s := by simp
#align set.Union_of_singleton_coe Set.Union_of_singleton_coe

theorem sUnion_eq_bUnion {s : Set (Set α)} : ⋃₀s = ⋃ (i : Set α) (h : i ∈ s), i := by
  rw [← sUnion_image, image_id']
#align set.sUnion_eq_bUnion Set.sUnion_eq_bUnion

theorem sInter_eq_bInter {s : Set (Set α)} : ⋂₀ s = ⋂ (i : Set α) (h : i ∈ s), i := by
  rw [← sInter_image, image_id']
#align set.sInter_eq_bInter Set.sInter_eq_bInter

theorem sUnion_eq_Union {s : Set (Set α)} : ⋃₀s = ⋃ i : s, i := by
  simp only [← sUnion_range, Subtype.range_coe]
#align set.sUnion_eq_Union Set.sUnion_eq_Union

theorem sInter_eq_Inter {s : Set (Set α)} : ⋂₀ s = ⋂ i : s, i := by
  simp only [← sInter_range, Subtype.range_coe]
#align set.sInter_eq_Inter Set.sInter_eq_Inter

@[simp]
theorem Union_of_empty [IsEmpty ι] (s : ι → Set α) : (⋃ i, s i) = ∅ :=
  supᵢ_of_empty _
#align set.Union_of_empty Set.Union_of_empty

@[simp]
theorem Inter_of_empty [IsEmpty ι] (s : ι → Set α) : (⋂ i, s i) = univ :=
  infᵢ_of_empty _
#align set.Inter_of_empty Set.Inter_of_empty

theorem union_eq_Union {s₁ s₂ : Set α} : s₁ ∪ s₂ = ⋃ b : Bool, cond b s₁ s₂ :=
  sup_eq_supᵢ s₁ s₂
#align set.union_eq_Union Set.union_eq_Union

theorem inter_eq_Inter {s₁ s₂ : Set α} : s₁ ∩ s₂ = ⋂ b : Bool, cond b s₁ s₂ :=
  inf_eq_infᵢ s₁ s₂
#align set.inter_eq_Inter Set.inter_eq_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInter_union_sInter {S T : Set (Set α)} :
    ⋂₀ S ∪ ⋂₀ T = ⋂ p ∈ S ×ˢ T, (p : Set α × Set α).1 ∪ p.2 :=
  infₛ_sup_infₛ
#align set.sInter_union_sInter Set.sInter_union_sInter

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sUnion_inter_sUnion {s t : Set (Set α)} :
    ⋃₀s ∩ ⋃₀t = ⋃ p ∈ s ×ˢ t, (p : Set α × Set α).1 ∩ p.2 :=
  supₛ_inf_supₛ
#align set.sUnion_inter_sUnion Set.sUnion_inter_sUnion

theorem bUnion_Union (s : ι → Set α) (t : α → Set β) :
    (⋃ x ∈ ⋃ i, s i, t x) = ⋃ (i) (x ∈ s i), t x := by simp [@Union_comm _ ι]
#align set.bUnion_Union Set.bUnion_Union

theorem bInter_Union (s : ι → Set α) (t : α → Set β) :
    (⋂ x ∈ ⋃ i, s i, t x) = ⋂ (i) (x ∈ s i), t x := by simp [@Inter_comm _ ι]
#align set.bInter_Union Set.bInter_Union

theorem sUnion_Union (s : ι → Set (Set α)) : (⋃₀⋃ i, s i) = ⋃ i, ⋃₀s i := by
  simp only [sUnion_eq_bUnion, bUnion_Union]
#align set.sUnion_Union Set.sUnion_Union

theorem sInter_Union (s : ι → Set (Set α)) : (⋂₀ ⋃ i, s i) = ⋂ i, ⋂₀ s i := by
  simp only [sInter_eq_bInter, bInter_Union]
#align set.sInter_Union Set.sInter_Union

theorem Union_range_eq_sUnion {α β : Type _} (C : Set (Set α)) {f : ∀ s : C, β → s}
    (hf : ∀ s : C, Surjective (f s)) : (⋃ y : β, range fun s : C => (f s y).val) = ⋃₀C := by
  ext x; constructor
  · rintro ⟨s, ⟨y, rfl⟩, ⟨s, hs⟩, rfl⟩
    refine' ⟨_, hs, _⟩
    exact (f ⟨s, hs⟩ y).2
  · rintro ⟨s, hs, hx⟩
    cases' hf ⟨s, hs⟩ ⟨x, hx⟩ with y hy
    refine' ⟨_, ⟨y, rfl⟩, ⟨s, hs⟩, _⟩
    exact congr_arg Subtype.val hy
#align set.Union_range_eq_sUnion Set.Union_range_eq_sUnion

theorem Union_range_eq_Union (C : ι → Set α) {f : ∀ x : ι, β → C x}
    (hf : ∀ x : ι, Surjective (f x)) : (⋃ y : β, range fun x : ι => (f x y).val) = ⋃ x, C x := by
  ext x; rw [mem_Union, mem_Union]; constructor
  · rintro ⟨y, i, rfl⟩
    exact ⟨i, (f i y).2⟩
  · rintro ⟨i, hx⟩
    cases' hf i ⟨x, hx⟩ with y hy
    exact ⟨y, i, congr_arg Subtype.val hy⟩
#align set.Union_range_eq_Union Set.Union_range_eq_Union

theorem union_distrib_Inter_left (s : ι → Set α) (t : Set α) : (t ∪ ⋂ i, s i) = ⋂ i, t ∪ s i :=
  sup_infᵢ_eq _ _
#align set.union_distrib_Inter_left Set.union_distrib_Inter_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_Inter₂_left (s : Set α) (t : ∀ i, κ i → Set α) :
    (s ∪ ⋂ (i) (j), t i j) = ⋂ (i) (j), s ∪ t i j := by simp_rw [union_distrib_Inter_left]
#align set.union_distrib_Inter₂_left Set.union_distrib_Inter₂_left

theorem union_distrib_Inter_right (s : ι → Set α) (t : Set α) : (⋂ i, s i) ∪ t = ⋂ i, s i ∪ t :=
  infᵢ_sup_eq _ _
#align set.union_distrib_Inter_right Set.union_distrib_Inter_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem union_distrib_Inter₂_right (s : ∀ i, κ i → Set α) (t : Set α) :
    (⋂ (i) (j), s i j) ∪ t = ⋂ (i) (j), s i j ∪ t := by simp_rw [union_distrib_Inter_right]
#align set.union_distrib_Inter₂_right Set.union_distrib_Inter₂_right

section Function

/-! ### `maps_to` -/


theorem maps_to_sUnion {S : Set (Set α)} {t : Set β} {f : α → β} (H : ∀ s ∈ S, MapsTo f s t) :
    MapsTo f (⋃₀S) t := fun x ⟨s, hs, hx⟩ => H s hs hx
#align set.maps_to_sUnion Set.maps_to_sUnion

theorem maps_to_Union {s : ι → Set α} {t : Set β} {f : α → β} (H : ∀ i, MapsTo f (s i) t) :
    MapsTo f (⋃ i, s i) t :=
  maps_to_sUnion <| forall_range_iff.2 H
#align set.maps_to_Union Set.maps_to_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem maps_to_Union₂ {s : ∀ i, κ i → Set α} {t : Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) t) : MapsTo f (⋃ (i) (j), s i j) t :=
  maps_to_Union fun i => maps_to_Union (H i)
#align set.maps_to_Union₂ Set.maps_to_Union₂

theorem maps_to_Union_Union {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋃ i, s i) (⋃ i, t i) :=
  maps_to_Union fun i => (H i).mono (Subset.refl _) (subset_Union t i)
#align set.maps_to_Union_Union Set.maps_to_Union_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem maps_to_Union₂_Union₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  maps_to_Union_Union fun i => maps_to_Union_Union (H i)
#align set.maps_to_Union₂_Union₂ Set.maps_to_Union₂_Union₂

theorem maps_to_sInter {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, MapsTo f s t) :
    MapsTo f s (⋂₀ T) := fun x hx t ht => H t ht hx
#align set.maps_to_sInter Set.maps_to_sInter

theorem maps_to_Inter {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, MapsTo f s (t i)) :
    MapsTo f s (⋂ i, t i) := fun x hx => mem_Inter.2 fun i => H i hx
#align set.maps_to_Inter Set.maps_to_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem maps_to_Inter₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f s (t i j)) : MapsTo f s (⋂ (i) (j), t i j) :=
  maps_to_Inter fun i => maps_to_Inter (H i)
#align set.maps_to_Inter₂ Set.maps_to_Inter₂

theorem maps_to_Inter_Inter {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, MapsTo f (s i) (t i)) : MapsTo f (⋂ i, s i) (⋂ i, t i) :=
  maps_to_Inter fun i => (H i).mono (Inter_subset s i) (Subset.refl _)
#align set.maps_to_Inter_Inter Set.maps_to_Inter_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem maps_to_Inter₂_Inter₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, MapsTo f (s i j) (t i j)) : MapsTo f (⋂ (i) (j), s i j) (⋂ (i) (j), t i j) :=
  maps_to_Inter_Inter fun i => maps_to_Inter_Inter (H i)
#align set.maps_to_Inter₂_Inter₂ Set.maps_to_Inter₂_Inter₂

theorem image_Inter_subset (s : ι → Set α) (f : α → β) : (f '' ⋂ i, s i) ⊆ ⋂ i, f '' s i :=
  (maps_to_Inter_Inter fun i => mapsTo_image f (s i)).image_subset
#align set.image_Inter_subset Set.image_Inter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_Inter₂_subset (s : ∀ i, κ i → Set α) (f : α → β) :
    (f '' ⋂ (i) (j), s i j) ⊆ ⋂ (i) (j), f '' s i j :=
  (maps_to_Inter₂_Inter₂ fun i hi => mapsTo_image f (s i hi)).image_subset
#align set.image_Inter₂_subset Set.image_Inter₂_subset

theorem image_sInter_subset (S : Set (Set α)) (f : α → β) : f '' ⋂₀ S ⊆ ⋂ s ∈ S, f '' s := by
  rw [sInter_eq_bInter]
  apply image_Inter₂_subset
#align set.image_sInter_subset Set.image_sInter_subset

/-! ### `restrict_preimage` -/


section

open Function

variable (s : Set β) {f : α → β} {U : ι → Set β} (hU : union U = univ)

include hU

theorem injective_iff_injective_of_Union_eq_univ :
    Injective f ↔ ∀ i, Injective ((U i).restrictPreimage f) := by
  refine' ⟨fun H i => (U i).restrict_preimage_injective H, fun H x y e => _⟩
  obtain ⟨i, hi⟩ :=
    set.mem_Union.mp
      (show f x ∈ Set.union U by 
        rw [hU]
        triv)
  injection @H i ⟨x, hi⟩ ⟨y, show f y ∈ U i from e ▸ hi⟩ (Subtype.ext e)
#align set.injective_iff_injective_of_Union_eq_univ Set.injective_iff_injective_of_Union_eq_univ

theorem surjective_iff_surjective_of_Union_eq_univ :
    Surjective f ↔ ∀ i, Surjective ((U i).restrictPreimage f) := by
  refine' ⟨fun H i => (U i).restrict_preimage_surjective H, fun H x => _⟩
  obtain ⟨i, hi⟩ :=
    set.mem_Union.mp
      (show x ∈ Set.union U by 
        rw [hU]
        triv)
  exact ⟨_, congr_arg Subtype.val (H i ⟨x, hi⟩).some_spec⟩
#align set.surjective_iff_surjective_of_Union_eq_univ Set.surjective_iff_surjective_of_Union_eq_univ

theorem bijective_iff_bijective_of_Union_eq_univ :
    Bijective f ↔ ∀ i, Bijective ((U i).restrictPreimage f) := by
  simp_rw [bijective, forall_and, injective_iff_injective_of_Union_eq_univ hU,
    surjective_iff_surjective_of_Union_eq_univ hU]
#align set.bijective_iff_bijective_of_Union_eq_univ Set.bijective_iff_bijective_of_Union_eq_univ

end

/-! ### `inj_on` -/


theorem InjOn.image_Inter_eq [Nonempty ι] {s : ι → Set α} {f : α → β} (h : InjOn f (⋃ i, s i)) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by 
  inhabit ι
  refine' subset.antisymm (image_Inter_subset s f) fun y hy => _
  simp only [mem_Inter, mem_image_iff_bex] at hy
  choose x hx hy using hy
  refine' ⟨x default, mem_Inter.2 fun i => _, hy _⟩
  suffices x default = x i by 
    rw [this]
    apply hx
  replace hx : ∀ i, x i ∈ ⋃ j, s j := fun i => (subset_Union _ _) (hx i)
  apply h (hx _) (hx _)
  simp only [hy]
#align set.inj_on.image_Inter_eq Set.InjOn.image_Inter_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem InjOn.image_bInter_eq {p : ι → Prop} {s : ∀ (i) (hi : p i), Set α} (hp : ∃ i, p i)
    {f : α → β} (h : InjOn f (⋃ (i) (hi), s i hi)) :
    (f '' ⋂ (i) (hi), s i hi) = ⋂ (i) (hi), f '' s i hi := by
  simp only [Inter, infᵢ_subtype']
  haveI : Nonempty { i // p i } := nonempty_subtype.2 hp
  apply inj_on.image_Inter_eq
  simpa only [Union, supᵢ_subtype'] using h
#align set.inj_on.image_bInter_eq Set.InjOn.image_bInter_eq

theorem image_Inter {f : α → β} (hf : Bijective f) (s : ι → Set α) :
    (f '' ⋂ i, s i) = ⋂ i, f '' s i := by
  cases isEmpty_or_nonempty ι
  · simp_rw [Inter_of_empty, image_univ_of_surjective hf.surjective]
  · exact (hf.injective.inj_on _).image_Inter_eq
#align set.image_Inter Set.image_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_Inter₂ {f : α → β} (hf : Bijective f) (s : ∀ i, κ i → Set α) :
    (f '' ⋂ (i) (j), s i j) = ⋂ (i) (j), f '' s i j := by simp_rw [image_Inter hf]
#align set.image_Inter₂ Set.image_Inter₂

theorem inj_on_Union_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {f : α → β}
    (hf : ∀ i, InjOn f (s i)) : InjOn f (⋃ i, s i) := by
  intro x hx y hy hxy
  rcases mem_Union.1 hx with ⟨i, hx⟩
  rcases mem_Union.1 hy with ⟨j, hy⟩
  rcases hs i j with ⟨k, hi, hj⟩
  exact hf k (hi hx) (hj hy) hxy
#align set.inj_on_Union_of_directed Set.inj_on_Union_of_directed

/-! ### `surj_on` -/


theorem surj_on_sUnion {s : Set α} {T : Set (Set β)} {f : α → β} (H : ∀ t ∈ T, SurjOn f s t) :
    SurjOn f s (⋃₀T) := fun x ⟨t, ht, hx⟩ => H t ht hx
#align set.surj_on_sUnion Set.surj_on_sUnion

theorem surj_on_Union {s : Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, SurjOn f s (t i)) :
    SurjOn f s (⋃ i, t i) :=
  surj_on_sUnion <| forall_range_iff.2 H
#align set.surj_on_Union Set.surj_on_Union

theorem surj_on_Union_Union {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) : SurjOn f (⋃ i, s i) (⋃ i, t i) :=
  surj_on_Union fun i => (H i).mono (subset_Union _ _) (Subset.refl _)
#align set.surj_on_Union_Union Set.surj_on_Union_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surj_on_Union₂ {s : Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f s (t i j)) : SurjOn f s (⋃ (i) (j), t i j) :=
  surj_on_Union fun i => surj_on_Union (H i)
#align set.surj_on_Union₂ Set.surj_on_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem surj_on_Union₂_Union₂ {s : ∀ i, κ i → Set α} {t : ∀ i, κ i → Set β} {f : α → β}
    (H : ∀ i j, SurjOn f (s i j) (t i j)) : SurjOn f (⋃ (i) (j), s i j) (⋃ (i) (j), t i j) :=
  surj_on_Union_Union fun i => surj_on_Union_Union (H i)
#align set.surj_on_Union₂_Union₂ Set.surj_on_Union₂_Union₂

theorem surj_on_Inter [hi : Nonempty ι] {s : ι → Set α} {t : Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) t) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) t := by
  intro y hy
  rw [Hinj.image_Inter_eq, mem_Inter]
  exact fun i => H i hy
#align set.surj_on_Inter Set.surj_on_Inter

theorem surj_on_Inter_Inter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, SurjOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : SurjOn f (⋂ i, s i) (⋂ i, t i) :=
  surj_on_Inter (fun i => (H i).mono (Subset.refl _) (Inter_subset _ _)) Hinj
#align set.surj_on_Inter_Inter Set.surj_on_Inter_Inter

/-! ### `bij_on` -/


theorem bij_on_Union {s : ι → Set α} {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i))
    (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  ⟨maps_to_Union_Union fun i => (H i).MapsTo, Hinj, surj_on_Union_Union fun i => (H i).SurjOn⟩
#align set.bij_on_Union Set.bij_on_Union

theorem bij_on_Inter [hi : Nonempty ι] {s : ι → Set α} {t : ι → Set β} {f : α → β}
    (H : ∀ i, BijOn f (s i) (t i)) (Hinj : InjOn f (⋃ i, s i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  ⟨maps_to_Inter_Inter fun i => (H i).MapsTo, hi.elim fun i => (H i).InjOn.mono (Inter_subset _ _),
    surj_on_Inter_Inter (fun i => (H i).SurjOn) Hinj⟩
#align set.bij_on_Inter Set.bij_on_Inter

theorem bij_on_Union_of_directed {s : ι → Set α} (hs : Directed (· ⊆ ·) s) {t : ι → Set β}
    {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋃ i, s i) (⋃ i, t i) :=
  bij_on_Union H <| inj_on_Union_of_directed hs fun i => (H i).InjOn
#align set.bij_on_Union_of_directed Set.bij_on_Union_of_directed

theorem bij_on_Inter_of_directed [Nonempty ι] {s : ι → Set α} (hs : Directed (· ⊆ ·) s)
    {t : ι → Set β} {f : α → β} (H : ∀ i, BijOn f (s i) (t i)) : BijOn f (⋂ i, s i) (⋂ i, t i) :=
  bij_on_Inter H <| inj_on_Union_of_directed hs fun i => (H i).InjOn
#align set.bij_on_Inter_of_directed Set.bij_on_Inter_of_directed

end Function

/-! ### `image`, `preimage` -/


section Image

theorem image_Union {f : α → β} {s : ι → Set α} : (f '' ⋃ i, s i) = ⋃ i, f '' s i := by
  ext1 x
  simp [image, ← exists_and_right, @exists_swap α]
#align set.image_Union Set.image_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image_Union₂ (f : α → β) (s : ∀ i, κ i → Set α) :
    (f '' ⋃ (i) (j), s i j) = ⋃ (i) (j), f '' s i j := by simp_rw [image_Union]
#align set.image_Union₂ Set.image_Union₂

theorem univ_subtype {p : α → Prop} : (univ : Set (Subtype p)) = ⋃ (x) (h : p x), {⟨x, h⟩} :=
  Set.ext fun ⟨x, h⟩ => by simp [h]
#align set.univ_subtype Set.univ_subtype

theorem range_eq_Union {ι} (f : ι → α) : range f = ⋃ i, {f i} :=
  Set.ext fun a => by simp [@eq_comm α a]
#align set.range_eq_Union Set.range_eq_Union

theorem image_eq_Union (f : α → β) (s : Set α) : f '' s = ⋃ i ∈ s, {f i} :=
  Set.ext fun b => by simp [@eq_comm β b]
#align set.image_eq_Union Set.image_eq_Union

theorem bUnion_range {f : ι → α} {g : α → Set β} : (⋃ x ∈ range f, g x) = ⋃ y, g (f y) :=
  supᵢ_range
#align set.bUnion_range Set.bUnion_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem Union_Union_eq' {f : ι → α} {g : α → Set β} :
    (⋃ (x) (y) (h : f y = x), g x) = ⋃ y, g (f y) := by simpa using bUnion_range
#align set.Union_Union_eq' Set.Union_Union_eq'

theorem bInter_range {f : ι → α} {g : α → Set β} : (⋂ x ∈ range f, g x) = ⋂ y, g (f y) :=
  infᵢ_range
#align set.bInter_range Set.bInter_range

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (x y) -/
@[simp]
theorem Inter_Inter_eq' {f : ι → α} {g : α → Set β} :
    (⋂ (x) (y) (h : f y = x), g x) = ⋂ y, g (f y) := by simpa using bInter_range
#align set.Inter_Inter_eq' Set.Inter_Inter_eq'

variable {s : Set γ} {f : γ → α} {g : α → Set β}

theorem bUnion_image : (⋃ x ∈ f '' s, g x) = ⋃ y ∈ s, g (f y) :=
  supᵢ_image
#align set.bUnion_image Set.bUnion_image

theorem bInter_image : (⋂ x ∈ f '' s, g x) = ⋂ y ∈ s, g (f y) :=
  infᵢ_image
#align set.bInter_image Set.bInter_image

end Image

section Preimage

theorem monotone_preimage {f : α → β} : Monotone (preimage f) := fun a b h => preimage_mono h
#align set.monotone_preimage Set.monotone_preimage

@[simp]
theorem preimage_Union {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i :=
  Set.ext <| by simp [preimage]
#align set.preimage_Union Set.preimage_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_Union₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_Union]
#align set.preimage_Union₂ Set.preimage_Union₂

@[simp]
theorem preimage_sUnion {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋃₀s = ⋃ t ∈ s, f ⁻¹' t := by
  rw [sUnion_eq_bUnion, preimage_Union₂]
#align set.preimage_sUnion Set.preimage_sUnion

theorem preimage_Inter {f : α → β} {s : ι → Set β} : (f ⁻¹' ⋂ i, s i) = ⋂ i, f ⁻¹' s i := by
  ext <;> simp
#align set.preimage_Inter Set.preimage_Inter

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem preimage_Inter₂ {f : α → β} {s : ∀ i, κ i → Set β} :
    (f ⁻¹' ⋂ (i) (j), s i j) = ⋂ (i) (j), f ⁻¹' s i j := by simp_rw [preimage_Inter]
#align set.preimage_Inter₂ Set.preimage_Inter₂

@[simp]
theorem preimage_sInter {f : α → β} {s : Set (Set β)} : f ⁻¹' ⋂₀ s = ⋂ t ∈ s, f ⁻¹' t := by
  rw [sInter_eq_bInter, preimage_Inter₂]
#align set.preimage_sInter Set.preimage_sInter

@[simp]
theorem bUnion_preimage_singleton (f : α → β) (s : Set β) : (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s := by
  rw [← preimage_Union₂, bUnion_of_singleton]
#align set.bUnion_preimage_singleton Set.bUnion_preimage_singleton

theorem bUnion_range_preimage_singleton (f : α → β) : (⋃ y ∈ range f, f ⁻¹' {y}) = univ := by
  rw [bUnion_preimage_singleton, preimage_range]
#align set.bUnion_range_preimage_singleton Set.bUnion_range_preimage_singleton

end Preimage

section Prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_Union {s : Set α} {t : ι → Set β} : (s ×ˢ ⋃ i, t i) = ⋃ i, s ×ˢ t i := by
  ext
  simp
#align set.prod_Union Set.prod_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_Union₂ {s : Set α} {t : ∀ i, κ i → Set β} :
    (s ×ˢ ⋃ (i) (j), t i j) = ⋃ (i) (j), s ×ˢ t i j := by simp_rw [prod_Union]
#align set.prod_Union₂ Set.prod_Union₂

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_sUnion {s : Set α} {C : Set (Set β)} : s ×ˢ ⋃₀C = ⋃₀((fun t => s ×ˢ t) '' C) := by
  simp_rw [sUnion_eq_bUnion, bUnion_image, prod_Union₂]
#align set.prod_sUnion Set.prod_sUnion

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Union_prod_const {s : ι → Set α} {t : Set β} : (⋃ i, s i) ×ˢ t = ⋃ i, s i ×ˢ t := by
  ext
  simp
#align set.Union_prod_const Set.Union_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Union₂_prod_const {s : ∀ i, κ i → Set α} {t : Set β} :
    (⋃ (i) (j), s i j) ×ˢ t = ⋃ (i) (j), s i j ×ˢ t := by simp_rw [Union_prod_const]
#align set.Union₂_prod_const Set.Union₂_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sUnion_prod_const {C : Set (Set α)} {t : Set β} :
    ⋃₀C ×ˢ t = ⋃₀((fun s : Set α => s ×ˢ t) '' C) := by
  simp only [sUnion_eq_bUnion, Union₂_prod_const, bUnion_image]
#align set.sUnion_prod_const Set.sUnion_prod_const

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Union_prod {ι ι' α β} (s : ι → Set α) (t : ι' → Set β) :
    (⋃ x : ι × ι', s x.1 ×ˢ t x.2) = (⋃ i : ι, s i) ×ˢ ⋃ i : ι', t i := by
  ext
  simp
#align set.Union_prod Set.Union_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Union_prod_of_monotone [SemilatticeSup α] {s : α → Set β} {t : α → Set γ} (hs : Monotone s)
    (ht : Monotone t) : (⋃ x, s x ×ˢ t x) = (⋃ x, s x) ×ˢ ⋃ x, t x := by
  ext ⟨z, w⟩; simp only [mem_prod, mem_Union, exists_imp, and_imp, iff_def]; constructor
  · intro x hz hw
    exact ⟨⟨x, hz⟩, x, hw⟩
  · intro x hz x' hw
    exact ⟨x ⊔ x', hs le_sup_left hz, ht le_sup_right hw⟩
#align set.Union_prod_of_monotone Set.Union_prod_of_monotone

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInter_prod_sInter_subset (S : Set (Set α)) (T : Set (Set β)) :
    ⋂₀ S ×ˢ ⋂₀ T ⊆ ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 :=
  subset_Inter₂ fun x hx y hy => ⟨hy.1 x.1 hx.1, hy.2 x.2 hx.2⟩
#align set.sInter_prod_sInter_subset Set.sInter_prod_sInter_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInter_prod_sInter {S : Set (Set α)} {T : Set (Set β)} (hS : S.Nonempty) (hT : T.Nonempty) :
    ⋂₀ S ×ˢ ⋂₀ T = ⋂ r ∈ S ×ˢ T, r.1 ×ˢ r.2 := by
  obtain ⟨s₁, h₁⟩ := hS
  obtain ⟨s₂, h₂⟩ := hT
  refine' Set.Subset.antisymm (sInter_prod_sInter_subset S T) fun x hx => _
  rw [mem_Inter₂] at hx
  exact ⟨fun s₀ h₀ => (hx (s₀, s₂) ⟨h₀, h₂⟩).1, fun s₀ h₀ => (hx (s₁, s₀) ⟨h₁, h₀⟩).2⟩
#align set.sInter_prod_sInter Set.sInter_prod_sInter

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem sInter_prod {S : Set (Set α)} (hS : S.Nonempty) (t : Set β) : ⋂₀ S ×ˢ t = ⋂ s ∈ S, s ×ˢ t :=
  by 
  rw [← sInter_singleton t, sInter_prod_sInter hS (singleton_nonempty t), sInter_singleton]
  simp_rw [prod_singleton, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right]
#align set.sInter_prod Set.sInter_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_sInter {T : Set (Set β)} (hT : T.Nonempty) (s : Set α) : s ×ˢ ⋂₀ T = ⋂ t ∈ T, s ×ˢ t :=
  by 
  rw [← sInter_singleton s, sInter_prod_sInter (singleton_nonempty s) hT, sInter_singleton]
  simp_rw [singleton_prod, mem_image, Inter_exists, bInter_and', Inter_Inter_eq_right]
#align set.prod_sInter Set.prod_sInter

end Prod

section Image2

variable (f : α → β → γ) {s : Set α} {t : Set β}

theorem Union_image_left : (⋃ a ∈ s, f a '' t) = image2 f s t := by
  ext y
  constructor <;> simp only [mem_Union] <;> rintro ⟨a, ha, x, hx, ax⟩ <;> exact ⟨a, x, ha, hx, ax⟩
#align set.Union_image_left Set.Union_image_left

theorem Union_image_right : (⋃ b ∈ t, (fun a => f a b) '' s) = image2 f s t := by
  ext y
  constructor <;> simp only [mem_Union] <;> rintro ⟨a, b, c, d, e⟩
  exact ⟨c, a, d, b, e⟩
  exact ⟨b, d, a, c, e⟩
#align set.Union_image_right Set.Union_image_right

theorem image2_Union_left (s : ι → Set α) (t : Set β) :
    image2 f (⋃ i, s i) t = ⋃ i, image2 f (s i) t := by
  simp only [← image_prod, Union_prod_const, image_Union]
#align set.image2_Union_left Set.image2_Union_left

theorem image2_Union_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋃ i, t i) = ⋃ i, image2 f s (t i) := by
  simp only [← image_prod, prod_Union, image_Union]
#align set.image2_Union_right Set.image2_Union_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_Union₂_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋃ (i) (j), s i j) t = ⋃ (i) (j), image2 f (s i j) t := by simp_rw [image2_Union_left]
#align set.image2_Union₂_left Set.image2_Union₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_Union₂_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋃ (i) (j), t i j) = ⋃ (i) (j), image2 f s (t i j) := by simp_rw [image2_Union_right]
#align set.image2_Union₂_right Set.image2_Union₂_right

theorem image2_Inter_subset_left (s : ι → Set α) (t : Set β) :
    image2 f (⋂ i, s i) t ⊆ ⋂ i, image2 f (s i) t := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem (hx _) hy
#align set.image2_Inter_subset_left Set.image2_Inter_subset_left

theorem image2_Inter_subset_right (s : Set α) (t : ι → Set β) :
    image2 f s (⋂ i, t i) ⊆ ⋂ i, image2 f s (t i) := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i => mem_image2_of_mem hx (hy _)
#align set.image2_Inter_subset_right Set.image2_Inter_subset_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_Inter₂_subset_left (s : ∀ i, κ i → Set α) (t : Set β) :
    image2 f (⋂ (i) (j), s i j) t ⊆ ⋂ (i) (j), image2 f (s i j) t := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem (hx _ _) hy
#align set.image2_Inter₂_subset_left Set.image2_Inter₂_subset_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem image2_Inter₂_subset_right (s : Set α) (t : ∀ i, κ i → Set β) :
    image2 f s (⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), image2 f s (t i j) := by
  simp_rw [image2_subset_iff, mem_Inter]
  exact fun x hx y hy i j => mem_image2_of_mem hx (hy _ _)
#align set.image2_Inter₂_subset_right Set.image2_Inter₂_subset_right

/-- The `set.image2` version of `set.image_eq_Union` -/
theorem image2_eq_Union (s : Set α) (t : Set β) : image2 f s t = ⋃ (i ∈ s) (j ∈ t), {f i j} := by
  simp_rw [← image_eq_Union, Union_image_left]
#align set.image2_eq_Union Set.image2_eq_Union

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bUnion_left : s ×ˢ t = ⋃ a ∈ s, (fun b => (a, b)) '' t := by
  rw [Union_image_left, image2_mk_eq_prod]
#align set.prod_eq_bUnion_left Set.prod_eq_bUnion_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_bUnion_right : s ×ˢ t = ⋃ b ∈ t, (fun a => (a, b)) '' s := by
  rw [Union_image_right, image2_mk_eq_prod]
#align set.prod_eq_bUnion_right Set.prod_eq_bUnion_right

end Image2

section Seq

/-- Given a set `s` of functions `α → β` and `t : set α`, `seq s t` is the union of `f '' t` over
all `f ∈ s`. -/
def seq (s : Set (α → β)) (t : Set α) : Set β :=
  { b | ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b }
#align set.seq Set.seq

theorem seq_def {s : Set (α → β)} {t : Set α} : seq s t = ⋃ f ∈ s, f '' t :=
  Set.ext <| by simp [seq]
#align set.seq_def Set.seq_def

@[simp]
theorem mem_seq_iff {s : Set (α → β)} {t : Set α} {b : β} :
    b ∈ seq s t ↔ ∃ f ∈ s, ∃ a ∈ t, (f : α → β) a = b :=
  Iff.rfl
#align set.mem_seq_iff Set.mem_seq_iff

theorem seq_subset {s : Set (α → β)} {t : Set α} {u : Set β} :
    seq s t ⊆ u ↔ ∀ f ∈ s, ∀ a ∈ t, (f : α → β) a ∈ u :=
  Iff.intro (fun h f hf a ha => h ⟨f, hf, a, ha, rfl⟩) fun h b ⟨f, hf, a, ha, Eq⟩ =>
    Eq ▸ h f hf a ha
#align set.seq_subset Set.seq_subset

theorem seq_mono {s₀ s₁ : Set (α → β)} {t₀ t₁ : Set α} (hs : s₀ ⊆ s₁) (ht : t₀ ⊆ t₁) :
    seq s₀ t₀ ⊆ seq s₁ t₁ := fun b ⟨f, hf, a, ha, Eq⟩ => ⟨f, hs hf, a, ht ha, Eq⟩
#align set.seq_mono Set.seq_mono

theorem singleton_seq {f : α → β} {t : Set α} : Set.seq {f} t = f '' t :=
  Set.ext <| by simp
#align set.singleton_seq Set.singleton_seq

theorem seq_singleton {s : Set (α → β)} {a : α} : Set.seq s {a} = (fun f : α → β => f a) '' s :=
  Set.ext <| by simp
#align set.seq_singleton Set.seq_singleton

theorem seq_seq {s : Set (β → γ)} {t : Set (α → β)} {u : Set α} :
    seq s (seq t u) = seq (seq ((· ∘ ·) '' s) t) u := by
  refine' Set.ext fun c => Iff.intro _ _
  · rintro ⟨f, hfs, b, ⟨g, hg, a, hau, rfl⟩, rfl⟩
    exact ⟨f ∘ g, ⟨(· ∘ ·) f, mem_image_of_mem _ hfs, g, hg, rfl⟩, a, hau, rfl⟩
  · rintro ⟨fg, ⟨fc, ⟨f, hfs, rfl⟩, g, hgt, rfl⟩, a, ha, rfl⟩
    exact ⟨f, hfs, g a, ⟨g, hgt, a, ha, rfl⟩, rfl⟩
#align set.seq_seq Set.seq_seq

theorem image_seq {f : β → γ} {s : Set (α → β)} {t : Set α} :
    f '' seq s t = seq ((· ∘ ·) f '' s) t := by
  rw [← singleton_seq, ← singleton_seq, seq_seq, image_singleton]
#align set.image_seq Set.image_seq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_seq {s : Set α} {t : Set β} : s ×ˢ t = (Prod.mk '' s).seq t := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨Prod.mk a, ⟨a, ha, rfl⟩, b, hb, rfl⟩
  · rintro ⟨f, ⟨x, hx, rfl⟩, y, hy, eq⟩
    rw [← Eq]
    exact ⟨hx, hy⟩
#align set.prod_eq_seq Set.prod_eq_seq

theorem prod_image_seq_comm (s : Set α) (t : Set β) :
    (Prod.mk '' s).seq t = seq ((fun b a => (a, b)) '' t) s := by
  rw [← prod_eq_seq, ← image_swap_prod, prod_eq_seq, image_seq, ← image_comp, Prod.swap]
#align set.prod_image_seq_comm Set.prod_image_seq_comm

theorem image2_eq_seq (f : α → β → γ) (s : Set α) (t : Set β) : image2 f s t = seq (f '' s) t := by
  ext
  simp
#align set.image2_eq_seq Set.image2_eq_seq

end Seq

section Pi

variable {π : α → Type _}

theorem pi_def (i : Set α) (s : ∀ a, Set (π a)) : pi i s = ⋂ a ∈ i, eval a ⁻¹' s a := by
  ext
  simp
#align set.pi_def Set.pi_def

theorem univ_pi_eq_Inter (t : ∀ i, Set (π i)) : pi univ t = ⋂ i, eval i ⁻¹' t i := by
  simp only [pi_def, Inter_true, mem_univ]
#align set.univ_pi_eq_Inter Set.univ_pi_eq_Inter

theorem pi_diff_pi_subset (i : Set α) (s t : ∀ a, Set (π a)) :
    pi i s \ pi i t ⊆ ⋃ a ∈ i, eval a ⁻¹' (s a \ t a) := by
  refine' diff_subset_comm.2 fun x hx a ha => _
  simp only [mem_diff, mem_pi, mem_Union, not_exists, mem_preimage, not_and, not_not, eval_apply] at
    hx
  exact hx.2 _ ha (hx.1 _ ha)
#align set.pi_diff_pi_subset Set.pi_diff_pi_subset

theorem Union_univ_pi (t : ∀ i, ι → Set (π i)) :
    (⋃ x : α → ι, pi univ fun i => t i (x i)) = pi univ fun i => ⋃ j : ι, t i j := by
  ext
  simp [Classical.skolem]
#align set.Union_univ_pi Set.Union_univ_pi

end Pi

end Set

namespace Function

namespace Surjective

theorem Union_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋃ x, g (f x)) = ⋃ y, g y :=
  hf.supr_comp g
#align function.surjective.Union_comp Function.Surjective.Union_comp

theorem Inter_comp {f : ι → ι₂} (hf : Surjective f) (g : ι₂ → Set α) : (⋂ x, g (f x)) = ⋂ y, g y :=
  hf.infi_comp g
#align function.surjective.Inter_comp Function.Surjective.Inter_comp

end Surjective

end Function

/-!
### Disjoint sets

We define some lemmas in the `disjoint` namespace to be able to use projection notation.
-/


section Disjoint

variable {s t u : Set α} {f : α → β}

namespace Set

@[simp]
theorem disjoint_Union_left {ι : Sort _} {s : ι → Set α} :
    Disjoint (⋃ i, s i) t ↔ ∀ i, Disjoint (s i) t :=
  supᵢ_disjoint_iff
#align set.disjoint_Union_left Set.disjoint_Union_left

@[simp]
theorem disjoint_Union_right {ι : Sort _} {s : ι → Set α} :
    Disjoint t (⋃ i, s i) ↔ ∀ i, Disjoint t (s i) :=
  disjoint_supᵢ_iff
#align set.disjoint_Union_right Set.disjoint_Union_right

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem disjoint_Union₂_left {s : ∀ i, κ i → Set α} {t : Set α} :
    Disjoint (⋃ (i) (j), s i j) t ↔ ∀ i j, Disjoint (s i j) t :=
  supᵢ₂_disjoint_iff
#align set.disjoint_Union₂_left Set.disjoint_Union₂_left

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem disjoint_Union₂_right {s : Set α} {t : ∀ i, κ i → Set α} :
    Disjoint s (⋃ (i) (j), t i j) ↔ ∀ i j, Disjoint s (t i j) :=
  disjoint_supᵢ₂_iff
#align set.disjoint_Union₂_right Set.disjoint_Union₂_right

@[simp]
theorem disjoint_sUnion_left {S : Set (Set α)} {t : Set α} :
    Disjoint (⋃₀S) t ↔ ∀ s ∈ S, Disjoint s t :=
  supₛ_disjoint_iff
#align set.disjoint_sUnion_left Set.disjoint_sUnion_left

@[simp]
theorem disjoint_sUnion_right {s : Set α} {S : Set (Set α)} :
    Disjoint s (⋃₀S) ↔ ∀ t ∈ S, Disjoint s t :=
  disjoint_supₛ_iff
#align set.disjoint_sUnion_right Set.disjoint_sUnion_right

end Set

end Disjoint

/-! ### Intervals -/


namespace Set

variable [CompleteLattice α]

theorem Ici_supr (f : ι → α) : Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  ext fun _ => by simp only [mem_Ici, supᵢ_le_iff, mem_Inter]
#align set.Ici_supr Set.Ici_supr

theorem Iic_infi (f : ι → α) : Iic (⨅ i, f i) = ⋂ i, Iic (f i) :=
  ext fun _ => by simp only [mem_Iic, le_infᵢ_iff, mem_Inter]
#align set.Iic_infi Set.Iic_infi

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Ici_supr₂ (f : ∀ i, κ i → α) : Ici (⨆ (i) (j), f i j) = ⋂ (i) (j), Ici (f i j) := by
  simp_rw [Ici_supr]
#align set.Ici_supr₂ Set.Ici_supr₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Iic_infi₂ (f : ∀ i, κ i → α) : Iic (⨅ (i) (j), f i j) = ⋂ (i) (j), Iic (f i j) := by
  simp_rw [Iic_infi]
#align set.Iic_infi₂ Set.Iic_infi₂

theorem Ici_Sup (s : Set α) : Ici (supₛ s) = ⋂ a ∈ s, Ici a := by rw [supₛ_eq_supᵢ, Ici_supr₂]
#align set.Ici_Sup Set.Ici_Sup

theorem Iic_Inf (s : Set α) : Iic (infₛ s) = ⋂ a ∈ s, Iic a := by rw [infₛ_eq_infᵢ, Iic_infi₂]
#align set.Iic_Inf Set.Iic_Inf

end Set

namespace Set

variable (t : α → Set β)

theorem bUnion_diff_bUnion_subset (s₁ s₂ : Set α) :
    ((⋃ x ∈ s₁, t x) \ ⋃ x ∈ s₂, t x) ⊆ ⋃ x ∈ s₁ \ s₂, t x := by
  simp only [diff_subset_iff, ← bUnion_union]
  apply bUnion_subset_bUnion_left
  rw [union_diff_self]
  apply subset_union_right
#align set.bUnion_diff_bUnion_subset Set.bUnion_diff_bUnion_subset

/-- If `t` is an indexed family of sets, then there is a natural map from `Σ i, t i` to `⋃ i, t i`
sending `⟨i, x⟩` to `x`. -/
def sigmaToUnion (x : Σi, t i) : ⋃ i, t i :=
  ⟨x.2, mem_Union.2 ⟨x.1, x.2.2⟩⟩
#align set.sigma_to_Union Set.sigmaToUnion

theorem sigma_to_Union_surjective : Surjective (sigmaToUnion t)
  | ⟨b, hb⟩ =>
    have : ∃ a, b ∈ t a := by simpa using hb
    let ⟨a, hb⟩ := this
    ⟨⟨a, b, hb⟩, rfl⟩
#align set.sigma_to_Union_surjective Set.sigma_to_Union_surjective

theorem sigma_to_Union_injective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Injective (sigmaToUnion t)
  | ⟨a₁, b₁, h₁⟩, ⟨a₂, b₂, h₂⟩, Eq =>
    have b_eq : b₁ = b₂ := congr_arg Subtype.val Eq
    have a_eq : a₁ = a₂ :=
      by_contradiction fun ne =>
        have : b₁ ∈ t a₁ ∩ t a₂ := ⟨h₁, b_eq.symm ▸ h₂⟩
        (h _ _ Ne).le_bot this
    Sigma.eq a_eq <| Subtype.eq <| by subst b_eq <;> subst a_eq
#align set.sigma_to_Union_injective Set.sigma_to_Union_injective

theorem sigma_to_Union_bijective (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    Bijective (sigmaToUnion t) :=
  ⟨sigma_to_Union_injective t h, sigma_to_Union_surjective t⟩
#align set.sigma_to_Union_bijective Set.sigma_to_Union_bijective

/-- Equivalence between a disjoint union and a dependent sum. -/
noncomputable def unionEqSigmaOfDisjoint {t : α → Set β} (h : ∀ i j, i ≠ j → Disjoint (t i) (t j)) :
    (⋃ i, t i) ≃ Σi, t i :=
  (Equiv.ofBijective _ <| sigma_to_Union_bijective t h).symm
#align set.Union_eq_sigma_of_disjoint Set.unionEqSigmaOfDisjoint

theorem Union_ge_eq_Union_nat_add (u : ℕ → Set α) (n : ℕ) : (⋃ i ≥ n, u i) = ⋃ i, u (i + n) :=
  supᵢ_ge_eq_supᵢ_nat_add u n
#align set.Union_ge_eq_Union_nat_add Set.Union_ge_eq_Union_nat_add

theorem Inter_ge_eq_Inter_nat_add (u : ℕ → Set α) (n : ℕ) : (⋂ i ≥ n, u i) = ⋂ i, u (i + n) :=
  infᵢ_ge_eq_infᵢ_nat_add u n
#align set.Inter_ge_eq_Inter_nat_add Set.Inter_ge_eq_Inter_nat_add

theorem Monotone.Union_nat_add {f : ℕ → Set α} (hf : Monotone f) (k : ℕ) :
    (⋃ n, f (n + k)) = ⋃ n, f n :=
  hf.supr_nat_add k
#align monotone.Union_nat_add Monotone.Union_nat_add

theorem Antitone.Inter_nat_add {f : ℕ → Set α} (hf : Antitone f) (k : ℕ) :
    (⋂ n, f (n + k)) = ⋂ n, f n :=
  hf.infi_nat_add k
#align antitone.Inter_nat_add Antitone.Inter_nat_add

@[simp]
theorem Union_Inter_ge_nat_add (f : ℕ → Set α) (k : ℕ) :
    (⋃ n, ⋂ i ≥ n, f (i + k)) = ⋃ n, ⋂ i ≥ n, f i :=
  supᵢ_infᵢ_ge_nat_add f k
#align set.Union_Inter_ge_nat_add Set.Union_Inter_ge_nat_add

theorem union_Union_nat_succ (u : ℕ → Set α) : (u 0 ∪ ⋃ i, u (i + 1)) = ⋃ i, u i :=
  sup_supᵢ_nat_succ u
#align set.union_Union_nat_succ Set.union_Union_nat_succ

theorem inter_Inter_nat_succ (u : ℕ → Set α) : (u 0 ∩ ⋂ i, u (i + 1)) = ⋂ i, u i :=
  inf_infᵢ_nat_succ u
#align set.inter_Inter_nat_succ Set.inter_Inter_nat_succ

end Set

open Set

variable [CompleteLattice β]

theorem supr_Union (s : ι → Set α) (f : α → β) : (⨆ a ∈ ⋃ i, s i, f a) = ⨆ (i) (a ∈ s i), f a := by
  rw [supᵢ_comm]
  simp_rw [mem_Union, supᵢ_exists]
#align supr_Union supr_Union

theorem infi_Union (s : ι → Set α) (f : α → β) : (⨅ a ∈ ⋃ i, s i, f a) = ⨅ (i) (a ∈ s i), f a :=
  @supr_Union α βᵒᵈ _ _ s f
#align infi_Union infi_Union

theorem Sup_sUnion (s : Set (Set β)) : supₛ (⋃₀s) = ⨆ t ∈ s, supₛ t := by
  simp only [sUnion_eq_bUnion, supₛ_eq_supᵢ, supr_Union]
#align Sup_sUnion Sup_sUnion

theorem Inf_sUnion (s : Set (Set β)) : infₛ (⋃₀s) = ⨅ t ∈ s, infₛ t :=
  @Sup_sUnion βᵒᵈ _ _
#align Inf_sUnion Inf_sUnion

