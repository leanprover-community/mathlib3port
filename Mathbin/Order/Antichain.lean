/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.antichain
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pairwise

/-!
# Antichains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.adj` for `G : simple_graph α`, this corresponds to independent sets of `G`.

## Definitions

* `is_antichain r s`: Any two elements of `s : set α` are unrelated by `r : α → α → Prop`.
* `is_strong_antichain r s`: Any two elements of `s : set α` are not related by `r : α → α → Prop`
  to a common element.
* `is_antichain.mk r s`: Turns `s` into an antichain by keeping only the "maximal" elements.
-/


open Function Set

section General

variable {α β : Type _} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : Set α} {a : α}

#print Symmetric.compl /-
protected theorem Symmetric.compl (h : Symmetric r) : Symmetric (rᶜ) := fun x y hr hr' =>
  hr <| h hr'
#align symmetric.compl Symmetric.compl
-/

#print IsAntichain /-
/-- An antichain is a set such that no two distinct elements are related. -/
def IsAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise (rᶜ)
#align is_antichain IsAntichain
-/

namespace IsAntichain

#print IsAntichain.subset /-
protected theorem subset (hs : IsAntichain r s) (h : t ⊆ s) : IsAntichain r t :=
  hs.mono h
#align is_antichain.subset IsAntichain.subset
-/

#print IsAntichain.mono /-
theorem mono (hs : IsAntichain r₁ s) (h : r₂ ≤ r₁) : IsAntichain r₂ s :=
  hs.mono' <| compl_le_compl h
#align is_antichain.mono IsAntichain.mono
-/

#print IsAntichain.mono_on /-
theorem mono_on (hs : IsAntichain r₁ s) (h : s.Pairwise fun ⦃a b⦄ => r₂ a b → r₁ a b) :
    IsAntichain r₂ s :=
  hs.imp_on <| h.imp fun a b h h₁ h₂ => h₁ <| h h₂
#align is_antichain.mono_on IsAntichain.mono_on
-/

#print IsAntichain.eq /-
protected theorem eq (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) :
    a = b :=
  hs.Eq ha hb <| not_not_intro h
#align is_antichain.eq IsAntichain.eq
-/

#print IsAntichain.eq' /-
protected theorem eq' (hs : IsAntichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r b a) :
    a = b :=
  (hs.Eq hb ha h).symm
#align is_antichain.eq' IsAntichain.eq'
-/

#print IsAntichain.isAntisymm /-
protected theorem isAntisymm (h : IsAntichain r univ) : IsAntisymm α r :=
  ⟨fun a b ha _ => h.Eq trivial trivial ha⟩
#align is_antichain.is_antisymm IsAntichain.isAntisymm
-/

#print IsAntichain.subsingleton /-
protected theorem subsingleton [IsTrichotomous α r] (h : IsAntichain r s) : s.Subsingleton :=
  by
  rintro a ha b hb
  obtain hab | hab | hab := trichotomous_of r a b
  · exact h.eq ha hb hab
  · exact hab
  · exact h.eq' ha hb hab
#align is_antichain.subsingleton IsAntichain.subsingleton
-/

#print IsAntichain.flip /-
protected theorem flip (hs : IsAntichain r s) : IsAntichain (flip r) s := fun a ha b hb h =>
  hs hb ha h.symm
#align is_antichain.flip IsAntichain.flip
-/

#print IsAntichain.swap /-
theorem swap (hs : IsAntichain r s) : IsAntichain (swap r) s :=
  hs.flip
#align is_antichain.swap IsAntichain.swap
-/

/- warning: is_antichain.image -> IsAntichain.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsAntichain.{u1} α r s) -> (forall (f : α -> β), (forall {{a : α}} {{b : α}}, (r' (f a) (f b)) -> (r a b)) -> (IsAntichain.{u2} β r' (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsAntichain.{u2} α r s) -> (forall (f : α -> β), (forall {{a : α}} {{b : α}}, (r' (f a) (f b)) -> (r a b)) -> (IsAntichain.{u1} β r' (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align is_antichain.image IsAntichain.imageₓ'. -/
theorem image (hs : IsAntichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
    IsAntichain r' (f '' s) :=
  by
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr)
#align is_antichain.image IsAntichain.image

/- warning: is_antichain.preimage -> IsAntichain.preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsAntichain.{u1} α r s) -> (forall {f : β -> α}, (Function.Injective.{succ u2, succ u1} β α f) -> (forall {{a : β}} {{b : β}}, (r' a b) -> (r (f a) (f b))) -> (IsAntichain.{u2} β r' (Set.preimage.{u2, u1} β α f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsAntichain.{u2} α r s) -> (forall {f : β -> α}, (Function.Injective.{succ u1, succ u2} β α f) -> (forall {{a : β}} {{b : β}}, (r' a b) -> (r (f a) (f b))) -> (IsAntichain.{u1} β r' (Set.preimage.{u1, u2} β α f s)))
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage IsAntichain.preimageₓ'. -/
theorem preimage (hs : IsAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) : IsAntichain r' (f ⁻¹' s) := fun b hb c hc hbc hr =>
  hs hb hc (hf.Ne hbc) <| h hr
#align is_antichain.preimage IsAntichain.preimage

#print isAntichain_insert /-
theorem isAntichain_insert :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b ∧ ¬r b a :=
  Set.pairwise_insert
#align is_antichain_insert isAntichain_insert
-/

#print IsAntichain.insert /-
protected theorem insert (hs : IsAntichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r b a)
    (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  isAntichain_insert.2 ⟨hs, fun b hb hab => ⟨hr hb hab, hl hb hab⟩⟩
#align is_antichain.insert IsAntichain.insert
-/

#print isAntichain_insert_of_symmetric /-
theorem isAntichain_insert_of_symmetric (hr : Symmetric r) :
    IsAntichain r (insert a s) ↔ IsAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b :=
  pairwise_insert_of_symmetric hr.compl
#align is_antichain_insert_of_symmetric isAntichain_insert_of_symmetric
-/

#print IsAntichain.insert_of_symmetric /-
theorem insert_of_symmetric (hs : IsAntichain r s) (hr : Symmetric r)
    (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬r a b) : IsAntichain r (insert a s) :=
  (isAntichain_insert_of_symmetric hr).2 ⟨hs, h⟩
#align is_antichain.insert_of_symmetric IsAntichain.insert_of_symmetric
-/

/- warning: is_antichain.image_rel_embedding -> IsAntichain.image_relEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsAntichain.{u1} α r s) -> (forall (φ : RelEmbedding.{u1, u2} α β r r'), IsAntichain.{u2} β r' (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r r') (fun (_x : RelEmbedding.{u1, u2} α β r r') => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r r') φ) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsAntichain.{u2} α r s) -> (forall (φ : RelEmbedding.{u2, u1} α β r r'), IsAntichain.{u1} β r' (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r r' φ)) s))
Case conversion may be inaccurate. Consider using '#align is_antichain.image_rel_embedding IsAntichain.image_relEmbeddingₓ'. -/
theorem image_relEmbedding (hs : IsAntichain r s) (φ : r ↪r r') : IsAntichain r' (φ '' s) :=
  by
  intro b hb b' hb' h₁ h₂
  rw [Set.mem_image] at hb hb'
  obtain ⟨⟨a, has, rfl⟩, ⟨a', has', rfl⟩⟩ := hb, hb'
  exact hs has has' (fun haa' => h₁ (haa'.subst (by rfl))) (φ.map_rel_iff.mp h₂)
#align is_antichain.image_rel_embedding IsAntichain.image_relEmbedding

/- warning: is_antichain.preimage_rel_embedding -> IsAntichain.preimage_relEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {t : Set.{u2} β}, (IsAntichain.{u2} β r' t) -> (forall (φ : RelEmbedding.{u1, u2} α β r r'), IsAntichain.{u1} α r (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r r') (fun (_x : RelEmbedding.{u1, u2} α β r r') => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r r') φ) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {t : Set.{u2} β}, (IsAntichain.{u2} β r' t) -> (forall (φ : RelEmbedding.{u1, u2} α β r r'), IsAntichain.{u1} α r (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r r' φ)) t))
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage_rel_embedding IsAntichain.preimage_relEmbeddingₓ'. -/
theorem preimage_relEmbedding {t : Set β} (ht : IsAntichain r' t) (φ : r ↪r r') :
    IsAntichain r (φ ⁻¹' t) := fun a ha a' ha' hne hle =>
  ht ha ha' (fun h => hne (φ.Injective h)) (φ.map_rel_iff.mpr hle)
#align is_antichain.preimage_rel_embedding IsAntichain.preimage_relEmbedding

/- warning: is_antichain.image_rel_iso -> IsAntichain.image_relIso is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsAntichain.{u1} α r s) -> (forall (φ : RelIso.{u1, u2} α β r r'), IsAntichain.{u2} β r' (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r r') (fun (_x : RelIso.{u1, u2} α β r r') => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r r') φ) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsAntichain.{u2} α r s) -> (forall (φ : RelIso.{u2, u1} α β r r'), IsAntichain.{u1} β r' (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r r' (RelIso.toRelEmbedding.{u2, u1} α β r r' φ))) s))
Case conversion may be inaccurate. Consider using '#align is_antichain.image_rel_iso IsAntichain.image_relIsoₓ'. -/
theorem image_relIso (hs : IsAntichain r s) (φ : r ≃r r') : IsAntichain r' (φ '' s) :=
  hs.image_rel_embedding φ
#align is_antichain.image_rel_iso IsAntichain.image_relIso

/- warning: is_antichain.preimage_rel_iso -> IsAntichain.preimage_relIso is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {t : Set.{u2} β}, (IsAntichain.{u2} β r' t) -> (forall (φ : RelIso.{u1, u2} α β r r'), IsAntichain.{u1} α r (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r r') (fun (_x : RelIso.{u1, u2} α β r r') => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r r') φ) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {t : Set.{u2} β}, (IsAntichain.{u2} β r' t) -> (forall (φ : RelIso.{u1, u2} α β r r'), IsAntichain.{u1} α r (Set.preimage.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r r' (RelIso.toRelEmbedding.{u1, u2} α β r r' φ))) t))
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage_rel_iso IsAntichain.preimage_relIsoₓ'. -/
theorem preimage_relIso {t : Set β} (hs : IsAntichain r' t) (φ : r ≃r r') :
    IsAntichain r (φ ⁻¹' t) :=
  hs.preimage_rel_embedding φ
#align is_antichain.preimage_rel_iso IsAntichain.preimage_relIso

/- warning: is_antichain.image_rel_embedding_iff -> IsAntichain.image_relEmbedding_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α} {φ : RelEmbedding.{u1, u2} α β r r'}, Iff (IsAntichain.{u2} β r' (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r r') (fun (_x : RelEmbedding.{u1, u2} α β r r') => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r r') φ) s)) (IsAntichain.{u1} α r s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α} {φ : RelEmbedding.{u2, u1} α β r r'}, Iff (IsAntichain.{u1} β r' (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r r' φ)) s)) (IsAntichain.{u2} α r s)
Case conversion may be inaccurate. Consider using '#align is_antichain.image_rel_embedding_iff IsAntichain.image_relEmbedding_iffₓ'. -/
theorem image_relEmbedding_iff {φ : r ↪r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  ⟨fun h => (φ.Injective.preimage_image s).subst (h.preimage_rel_embedding φ), fun h =>
    h.image_rel_embedding φ⟩
#align is_antichain.image_rel_embedding_iff IsAntichain.image_relEmbedding_iff

/- warning: is_antichain.image_rel_iso_iff -> IsAntichain.image_relIso_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α} {φ : RelIso.{u1, u2} α β r r'}, Iff (IsAntichain.{u2} β r' (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r r') (fun (_x : RelIso.{u1, u2} α β r r') => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r r') φ) s)) (IsAntichain.{u1} α r s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α} {φ : RelIso.{u2, u1} α β r r'}, Iff (IsAntichain.{u1} β r' (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r r' (RelIso.toRelEmbedding.{u2, u1} α β r r' φ))) s)) (IsAntichain.{u2} α r s)
Case conversion may be inaccurate. Consider using '#align is_antichain.image_rel_iso_iff IsAntichain.image_relIso_iffₓ'. -/
theorem image_relIso_iff {φ : r ≃r r'} : IsAntichain r' (φ '' s) ↔ IsAntichain r s :=
  @image_relEmbedding_iff _ _ _ _ _ (φ : r ↪r r')
#align is_antichain.image_rel_iso_iff IsAntichain.image_relIso_iff

/- warning: is_antichain.image_embedding -> IsAntichain.image_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β], (IsAntichain.{u1} α (LE.le.{u1} α _inst_1) s) -> (forall (φ : OrderEmbedding.{u1, u2} α β _inst_1 _inst_2), IsAntichain.{u2} β (LE.le.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β], (IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.1593 : α) (x._@.Mathlib.Order.Antichain._hyg.1595 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.1593 x._@.Mathlib.Order.Antichain._hyg.1595) s) -> (forall (φ : OrderEmbedding.{u2, u1} α β _inst_1 _inst_2), IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.1615 : β) (x._@.Mathlib.Order.Antichain._hyg.1617 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.1615 x._@.Mathlib.Order.Antichain._hyg.1617) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) φ)) s))
Case conversion may be inaccurate. Consider using '#align is_antichain.image_embedding IsAntichain.image_embeddingₓ'. -/
theorem image_embedding [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
#align is_antichain.image_embedding IsAntichain.image_embedding

/- warning: is_antichain.preimage_embedding -> IsAntichain.preimage_embedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] {t : Set.{u2} β}, (IsAntichain.{u2} β (LE.le.{u2} β _inst_2) t) -> (forall (φ : OrderEmbedding.{u1, u2} α β _inst_1 _inst_2), IsAntichain.{u1} α (LE.le.{u1} α _inst_1) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] {t : Set.{u1} β}, (IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.1678 : β) (x._@.Mathlib.Order.Antichain._hyg.1680 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.1678 x._@.Mathlib.Order.Antichain._hyg.1680) t) -> (forall (φ : OrderEmbedding.{u2, u1} α β _inst_1 _inst_2), IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.1700 : α) (x._@.Mathlib.Order.Antichain._hyg.1702 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.1700 x._@.Mathlib.Order.Antichain._hyg.1702) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) φ)) t))
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage_embedding IsAntichain.preimage_embeddingₓ'. -/
theorem preimage_embedding [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ↪o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
#align is_antichain.preimage_embedding IsAntichain.preimage_embedding

/- warning: is_antichain.image_embedding_iff -> IsAntichain.image_embedding_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] {φ : OrderEmbedding.{u1, u2} α β _inst_1 _inst_2}, Iff (IsAntichain.{u2} β (LE.le.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelEmbedding.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) s)) (IsAntichain.{u1} α (LE.le.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] {φ : OrderEmbedding.{u2, u1} α β _inst_1 _inst_2}, Iff (IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.1769 : β) (x._@.Mathlib.Order.Antichain._hyg.1771 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.1769 x._@.Mathlib.Order.Antichain._hyg.1771) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.744 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.746 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.744 x._@.Mathlib.Order.Hom.Basic._hyg.746) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.759 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.761 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.759 x._@.Mathlib.Order.Hom.Basic._hyg.761) φ)) s)) (IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.1792 : α) (x._@.Mathlib.Order.Antichain._hyg.1794 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.1792 x._@.Mathlib.Order.Antichain._hyg.1794) s)
Case conversion may be inaccurate. Consider using '#align is_antichain.image_embedding_iff IsAntichain.image_embedding_iffₓ'. -/
theorem image_embedding_iff [LE α] [LE β] {φ : α ↪o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_rel_embedding_iff
#align is_antichain.image_embedding_iff IsAntichain.image_embedding_iff

/- warning: is_antichain.image_iso -> IsAntichain.image_iso is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β], (IsAntichain.{u1} α (LE.le.{u1} α _inst_1) s) -> (forall (φ : OrderIso.{u1, u2} α β _inst_1 _inst_2), IsAntichain.{u2} β (LE.le.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β], (IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.1845 : α) (x._@.Mathlib.Order.Antichain._hyg.1847 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.1845 x._@.Mathlib.Order.Antichain._hyg.1847) s) -> (forall (φ : OrderIso.{u2, u1} α β _inst_1 _inst_2), IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.1867 : β) (x._@.Mathlib.Order.Antichain._hyg.1869 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.1867 x._@.Mathlib.Order.Antichain._hyg.1869) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) φ))) s))
Case conversion may be inaccurate. Consider using '#align is_antichain.image_iso IsAntichain.image_isoₓ'. -/
theorem image_iso [LE α] [LE β] (hs : IsAntichain (· ≤ ·) s) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ '' s) :=
  image_relEmbedding hs _
#align is_antichain.image_iso IsAntichain.image_iso

/- warning: is_antichain.image_iso_iff -> IsAntichain.image_iso_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] {φ : OrderIso.{u1, u2} α β _inst_1 _inst_2}, Iff (IsAntichain.{u2} β (LE.le.{u2} β _inst_2) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) s)) (IsAntichain.{u1} α (LE.le.{u1} α _inst_1) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] {φ : OrderIso.{u2, u1} α β _inst_1 _inst_2}, Iff (IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.1936 : β) (x._@.Mathlib.Order.Antichain._hyg.1938 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.1936 x._@.Mathlib.Order.Antichain._hyg.1938) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) φ))) s)) (IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.1959 : α) (x._@.Mathlib.Order.Antichain._hyg.1961 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.1959 x._@.Mathlib.Order.Antichain._hyg.1961) s)
Case conversion may be inaccurate. Consider using '#align is_antichain.image_iso_iff IsAntichain.image_iso_iffₓ'. -/
theorem image_iso_iff [LE α] [LE β] {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ '' s) ↔ IsAntichain (· ≤ ·) s :=
  image_rel_embedding_iff
#align is_antichain.image_iso_iff IsAntichain.image_iso_iff

/- warning: is_antichain.preimage_iso -> IsAntichain.preimage_iso is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] {t : Set.{u2} β}, (IsAntichain.{u2} β (LE.le.{u2} β _inst_2) t) -> (forall (φ : OrderIso.{u1, u2} α β _inst_1 _inst_2), IsAntichain.{u1} α (LE.le.{u1} α _inst_1) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] {t : Set.{u1} β}, (IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.2014 : β) (x._@.Mathlib.Order.Antichain._hyg.2016 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.2014 x._@.Mathlib.Order.Antichain._hyg.2016) t) -> (forall (φ : OrderIso.{u2, u1} α β _inst_1 _inst_2), IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.2036 : α) (x._@.Mathlib.Order.Antichain._hyg.2038 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.2036 x._@.Mathlib.Order.Antichain._hyg.2038) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) φ))) t))
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage_iso IsAntichain.preimage_isoₓ'. -/
theorem preimage_iso [LE α] [LE β] {t : Set β} (ht : IsAntichain (· ≤ ·) t) (φ : α ≃o β) :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) :=
  preimage_relEmbedding ht _
#align is_antichain.preimage_iso IsAntichain.preimage_iso

/- warning: is_antichain.preimage_iso_iff -> IsAntichain.preimage_iso_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : LE.{u1} α] [_inst_2 : LE.{u2} β] {t : Set.{u2} β} {φ : OrderIso.{u1, u2} α β _inst_1 _inst_2}, Iff (IsAntichain.{u1} α (LE.le.{u1} α _inst_1) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderIso.{u1, u2} α β _inst_1 _inst_2) (fun (_x : RelIso.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β (LE.le.{u1} α _inst_1) (LE.le.{u2} β _inst_2)) φ) t)) (IsAntichain.{u2} β (LE.le.{u2} β _inst_2) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : LE.{u2} α] [_inst_2 : LE.{u1} β] {t : Set.{u1} β} {φ : OrderIso.{u2, u1} α β _inst_1 _inst_2}, Iff (IsAntichain.{u2} α (fun (x._@.Mathlib.Order.Antichain._hyg.2107 : α) (x._@.Mathlib.Order.Antichain._hyg.2109 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Antichain._hyg.2107 x._@.Mathlib.Order.Antichain._hyg.2109) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) (RelIso.toRelEmbedding.{u2, u1} α β (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1411 : α) (x._@.Mathlib.Order.Hom.Basic._hyg.1413 : α) => LE.le.{u2} α _inst_1 x._@.Mathlib.Order.Hom.Basic._hyg.1411 x._@.Mathlib.Order.Hom.Basic._hyg.1413) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1426 : β) (x._@.Mathlib.Order.Hom.Basic._hyg.1428 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Hom.Basic._hyg.1426 x._@.Mathlib.Order.Hom.Basic._hyg.1428) φ))) t)) (IsAntichain.{u1} β (fun (x._@.Mathlib.Order.Antichain._hyg.2130 : β) (x._@.Mathlib.Order.Antichain._hyg.2132 : β) => LE.le.{u1} β _inst_2 x._@.Mathlib.Order.Antichain._hyg.2130 x._@.Mathlib.Order.Antichain._hyg.2132) t)
Case conversion may be inaccurate. Consider using '#align is_antichain.preimage_iso_iff IsAntichain.preimage_iso_iffₓ'. -/
theorem preimage_iso_iff [LE α] [LE β] {t : Set β} {φ : α ≃o β} :
    IsAntichain (· ≤ ·) (φ ⁻¹' t) ↔ IsAntichain (· ≤ ·) t :=
  ⟨fun h => (φ.image_preimage t).subst (h.image_iso φ), fun h => h.preimage_iso _⟩
#align is_antichain.preimage_iso_iff IsAntichain.preimage_iso_iff

#print IsAntichain.to_dual /-
theorem to_dual [LE α] (hs : IsAntichain (· ≤ ·) s) : @IsAntichain αᵒᵈ (· ≤ ·) s :=
  fun a ha b hb hab => hs hb ha hab.symm
#align is_antichain.to_dual IsAntichain.to_dual
-/

#print IsAntichain.to_dual_iff /-
theorem to_dual_iff [LE α] : IsAntichain (· ≤ ·) s ↔ @IsAntichain αᵒᵈ (· ≤ ·) s :=
  ⟨to_dual, to_dual⟩
#align is_antichain.to_dual_iff IsAntichain.to_dual_iff
-/

#print IsAntichain.image_compl /-
theorem image_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl '' s) :=
  (hs.image_embedding (OrderIso.compl α).toOrderEmbedding).flip
#align is_antichain.image_compl IsAntichain.image_compl
-/

#print IsAntichain.preimage_compl /-
theorem preimage_compl [BooleanAlgebra α] (hs : IsAntichain (· ≤ ·) s) :
    IsAntichain (· ≤ ·) (compl ⁻¹' s) := fun a ha a' ha' hne hle =>
  hs ha' ha (fun h => hne (compl_inj_iff.mp h.symm)) (compl_le_compl hle)
#align is_antichain.preimage_compl IsAntichain.preimage_compl
-/

end IsAntichain

#print isAntichain_singleton /-
theorem isAntichain_singleton (a : α) (r : α → α → Prop) : IsAntichain r {a} :=
  pairwise_singleton _ _
#align is_antichain_singleton isAntichain_singleton
-/

#print Set.Subsingleton.isAntichain /-
theorem Set.Subsingleton.isAntichain (hs : s.Subsingleton) (r : α → α → Prop) : IsAntichain r s :=
  hs.Pairwise _
#align set.subsingleton.is_antichain Set.Subsingleton.isAntichain
-/

section Preorder

variable [Preorder α]

#print isAntichain_and_least_iff /-
theorem isAntichain_and_least_iff : IsAntichain (· ≤ ·) s ∧ IsLeast s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun b hb => h.1.eq' hb h.2.1 (h.2.2 hb)⟩,
    by
    rintro rfl
    exact ⟨isAntichain_singleton _ _, isLeast_singleton⟩⟩
#align is_antichain_and_least_iff isAntichain_and_least_iff
-/

#print isAntichain_and_greatest_iff /-
theorem isAntichain_and_greatest_iff : IsAntichain (· ≤ ·) s ∧ IsGreatest s a ↔ s = {a} :=
  ⟨fun h => eq_singleton_iff_unique_mem.2 ⟨h.2.1, fun b hb => h.1.Eq hb h.2.1 (h.2.2 hb)⟩,
    by
    rintro rfl
    exact ⟨isAntichain_singleton _ _, isGreatest_singleton⟩⟩
#align is_antichain_and_greatest_iff isAntichain_and_greatest_iff
-/

#print IsAntichain.least_iff /-
theorem IsAntichain.least_iff (hs : IsAntichain (· ≤ ·) s) : IsLeast s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_least_iff
#align is_antichain.least_iff IsAntichain.least_iff
-/

#print IsAntichain.greatest_iff /-
theorem IsAntichain.greatest_iff (hs : IsAntichain (· ≤ ·) s) : IsGreatest s a ↔ s = {a} :=
  (and_iff_right hs).symm.trans isAntichain_and_greatest_iff
#align is_antichain.greatest_iff IsAntichain.greatest_iff
-/

#print IsLeast.antichain_iff /-
theorem IsLeast.antichain_iff (hs : IsLeast s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_least_iff
#align is_least.antichain_iff IsLeast.antichain_iff
-/

#print IsGreatest.antichain_iff /-
theorem IsGreatest.antichain_iff (hs : IsGreatest s a) : IsAntichain (· ≤ ·) s ↔ s = {a} :=
  (and_iff_left hs).symm.trans isAntichain_and_greatest_iff
#align is_greatest.antichain_iff IsGreatest.antichain_iff
-/

/- warning: is_antichain.bot_mem_iff -> IsAntichain.bot_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)], (IsAntichain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) s) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)) s) (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Bot.bot.{u1} α (OrderBot.toHasBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderBot.{u1} α (Preorder.toLE.{u1} α _inst_1)], (IsAntichain.{u1} α (fun (x._@.Mathlib.Order.Antichain._hyg.3354 : α) (x._@.Mathlib.Order.Antichain._hyg.3356 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Antichain._hyg.3354 x._@.Mathlib.Order.Antichain._hyg.3356) s) -> (Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)) s) (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Bot.bot.{u1} α (OrderBot.toBot.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_antichain.bot_mem_iff IsAntichain.bot_mem_iffₓ'. -/
theorem IsAntichain.bot_mem_iff [OrderBot α] (hs : IsAntichain (· ≤ ·) s) : ⊥ ∈ s ↔ s = {⊥} :=
  isLeast_bot_iff.symm.trans hs.least_iff
#align is_antichain.bot_mem_iff IsAntichain.bot_mem_iff

/- warning: is_antichain.top_mem_iff -> IsAntichain.top_mem_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)], (IsAntichain.{u1} α (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) s) -> (Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)) s) (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (Top.top.{u1} α (OrderTop.toHasTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] [_inst_2 : OrderTop.{u1} α (Preorder.toLE.{u1} α _inst_1)], (IsAntichain.{u1} α (fun (x._@.Mathlib.Order.Antichain._hyg.3433 : α) (x._@.Mathlib.Order.Antichain._hyg.3435 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) x._@.Mathlib.Order.Antichain._hyg.3433 x._@.Mathlib.Order.Antichain._hyg.3435) s) -> (Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)) s) (Eq.{succ u1} (Set.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) (Top.top.{u1} α (OrderTop.toTop.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_2)))))
Case conversion may be inaccurate. Consider using '#align is_antichain.top_mem_iff IsAntichain.top_mem_iffₓ'. -/
theorem IsAntichain.top_mem_iff [OrderTop α] (hs : IsAntichain (· ≤ ·) s) : ⊤ ∈ s ↔ s = {⊤} :=
  isGreatest_top_iff.symm.trans hs.greatest_iff
#align is_antichain.top_mem_iff IsAntichain.top_mem_iff

end Preorder

/-! ### Strong antichains -/


#print IsStrongAntichain /-
/-- A strong (upward) antichain is a set such that no two distinct elements are related to a common
element. -/
def IsStrongAntichain (r : α → α → Prop) (s : Set α) : Prop :=
  s.Pairwise fun a b => ∀ c, ¬r a c ∨ ¬r b c
#align is_strong_antichain IsStrongAntichain
-/

namespace IsStrongAntichain

#print IsStrongAntichain.subset /-
protected theorem subset (hs : IsStrongAntichain r s) (h : t ⊆ s) : IsStrongAntichain r t :=
  hs.mono h
#align is_strong_antichain.subset IsStrongAntichain.subset
-/

#print IsStrongAntichain.mono /-
theorem mono (hs : IsStrongAntichain r₁ s) (h : r₂ ≤ r₁) : IsStrongAntichain r₂ s :=
  hs.mono' fun a b hab c => (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)
#align is_strong_antichain.mono IsStrongAntichain.mono
-/

#print IsStrongAntichain.eq /-
theorem eq (hs : IsStrongAntichain r s) {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hac : r a c)
    (hbc : r b c) : a = b :=
  hs.Eq ha hb fun h => False.elim <| (h c).elim (not_not_intro hac) (not_not_intro hbc)
#align is_strong_antichain.eq IsStrongAntichain.eq
-/

#print IsStrongAntichain.isAntichain /-
protected theorem isAntichain [IsRefl α r] (h : IsStrongAntichain r s) : IsAntichain r s :=
  h.imp fun a b hab => (hab b).resolve_right (not_not_intro <| refl _)
#align is_strong_antichain.is_antichain IsStrongAntichain.isAntichain
-/

#print IsStrongAntichain.subsingleton /-
protected theorem subsingleton [IsDirected α r] (h : IsStrongAntichain r s) : s.Subsingleton :=
  fun a ha b hb =>
  let ⟨c, hac, hbc⟩ := directed_of r a b
  h.Eq ha hb hac hbc
#align is_strong_antichain.subsingleton IsStrongAntichain.subsingleton
-/

#print IsStrongAntichain.flip /-
protected theorem flip [IsSymm α r] (hs : IsStrongAntichain r s) : IsStrongAntichain (flip r) s :=
  fun a ha b hb h c => (hs ha hb h c).imp (mt <| symm_of r) (mt <| symm_of r)
#align is_strong_antichain.flip IsStrongAntichain.flip
-/

#print IsStrongAntichain.swap /-
theorem swap [IsSymm α r] (hs : IsStrongAntichain r s) : IsStrongAntichain (swap r) s :=
  hs.flip
#align is_strong_antichain.swap IsStrongAntichain.swap
-/

/- warning: is_strong_antichain.image -> IsStrongAntichain.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsStrongAntichain.{u1} α r s) -> (forall {f : α -> β}, (Function.Surjective.{succ u1, succ u2} α β f) -> (forall (a : α) (b : α), (r' (f a) (f b)) -> (r a b)) -> (IsStrongAntichain.{u2} β r' (Set.image.{u1, u2} α β f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsStrongAntichain.{u2} α r s) -> (forall {f : α -> β}, (Function.Surjective.{succ u2, succ u1} α β f) -> (forall (a : α) (b : α), (r' (f a) (f b)) -> (r a b)) -> (IsStrongAntichain.{u1} β r' (Set.image.{u2, u1} α β f s)))
Case conversion may be inaccurate. Consider using '#align is_strong_antichain.image IsStrongAntichain.imageₓ'. -/
theorem image (hs : IsStrongAntichain r s) {f : α → β} (hf : Surjective f)
    (h : ∀ a b, r' (f a) (f b) → r a b) : IsStrongAntichain r' (f '' s) :=
  by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c
  obtain ⟨c, rfl⟩ := hf c
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt <| h _ _) (mt <| h _ _)
#align is_strong_antichain.image IsStrongAntichain.image

/- warning: is_strong_antichain.preimage -> IsStrongAntichain.preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u1} α}, (IsStrongAntichain.{u1} α r s) -> (forall {f : β -> α}, (Function.Injective.{succ u2, succ u1} β α f) -> (forall (a : β) (b : β), (r' a b) -> (r (f a) (f b))) -> (IsStrongAntichain.{u2} β r' (Set.preimage.{u2, u1} β α f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {r' : β -> β -> Prop} {s : Set.{u2} α}, (IsStrongAntichain.{u2} α r s) -> (forall {f : β -> α}, (Function.Injective.{succ u1, succ u2} β α f) -> (forall (a : β) (b : β), (r' a b) -> (r (f a) (f b))) -> (IsStrongAntichain.{u1} β r' (Set.preimage.{u1, u2} β α f s)))
Case conversion may be inaccurate. Consider using '#align is_strong_antichain.preimage IsStrongAntichain.preimageₓ'. -/
theorem preimage (hs : IsStrongAntichain r s) {f : β → α} (hf : Injective f)
    (h : ∀ a b, r' a b → r (f a) (f b)) : IsStrongAntichain r' (f ⁻¹' s) := fun a ha b hb hab c =>
  (hs ha hb (hf.Ne hab) _).imp (mt <| h _ _) (mt <| h _ _)
#align is_strong_antichain.preimage IsStrongAntichain.preimage

#print isStrongAntichain_insert /-
theorem isStrongAntichain_insert :
    IsStrongAntichain r (insert a s) ↔
      IsStrongAntichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c :=
  Set.pairwise_insert_of_symmetric fun a b h c => (h c).symm
#align is_strong_antichain_insert isStrongAntichain_insert
-/

#print IsStrongAntichain.insert /-
protected theorem insert (hs : IsStrongAntichain r s)
    (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬r a c ∨ ¬r b c) : IsStrongAntichain r (insert a s) :=
  isStrongAntichain_insert.2 ⟨hs, h⟩
#align is_strong_antichain.insert IsStrongAntichain.insert
-/

end IsStrongAntichain

#print Set.Subsingleton.isStrongAntichain /-
theorem Set.Subsingleton.isStrongAntichain (hs : s.Subsingleton) (r : α → α → Prop) :
    IsStrongAntichain r s :=
  hs.Pairwise _
#align set.subsingleton.is_strong_antichain Set.Subsingleton.isStrongAntichain
-/

end General

/-! ### Weak antichains -/


section Pi

variable {ι : Type _} {α : ι → Type _} [∀ i, Preorder (α i)] {s t : Set (∀ i, α i)}
  {a b c : ∀ i, α i}

-- mathport name: «expr ≺ »
local infixl:50 " ≺ " => StrongLT

#print IsWeakAntichain /-
/-- A weak antichain in `Π i, α i` is a set such that no two distinct elements are strongly less
than each other. -/
def IsWeakAntichain (s : Set (∀ i, α i)) : Prop :=
  IsAntichain (· ≺ ·) s
#align is_weak_antichain IsWeakAntichain
-/

namespace IsWeakAntichain

/- warning: is_weak_antichain.subset -> IsWeakAntichain.subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)} {t : Set.{max u1 u2} (forall (i : ι), α i)}, (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) t s) -> (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) t)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)} {t : Set.{max u2 u1} (forall (i : ι), α i)}, (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet.{max u2 u1} (forall (i : ι), α i)) t s) -> (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) t)
Case conversion may be inaccurate. Consider using '#align is_weak_antichain.subset IsWeakAntichain.subsetₓ'. -/
protected theorem subset (hs : IsWeakAntichain s) : t ⊆ s → IsWeakAntichain t :=
  hs.Subset
#align is_weak_antichain.subset IsWeakAntichain.subset

/- warning: is_weak_antichain.eq -> IsWeakAntichain.eq is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)} {a : forall (i : ι), α i} {b : forall (i : ι), α i}, (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) a s) -> (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) b s) -> (StrongLT.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_1 i)) a b) -> (Eq.{max (succ u1) (succ u2)} (forall (i : ι), α i) a b)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)} {a : forall (i : ι), α i} {b : forall (i : ι), α i}, (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) a s) -> (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) b s) -> (StrongLT.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u1} (α i) (_inst_1 i)) a b) -> (Eq.{max (succ u2) (succ u1)} (forall (i : ι), α i) a b)
Case conversion may be inaccurate. Consider using '#align is_weak_antichain.eq IsWeakAntichain.eqₓ'. -/
protected theorem eq (hs : IsWeakAntichain s) : a ∈ s → b ∈ s → a ≺ b → a = b :=
  hs.Eq
#align is_weak_antichain.eq IsWeakAntichain.eq

/- warning: is_weak_antichain.insert -> IsWeakAntichain.insert is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)} {a : forall (i : ι), α i}, (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (forall {{b : forall (i : ι), α i}}, (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u1) (succ u2)} (forall (i : ι), α i) a b) -> (Not (StrongLT.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_1 i)) b a))) -> (forall {{b : forall (i : ι), α i}}, (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u1) (succ u2)} (forall (i : ι), α i) a b) -> (Not (StrongLT.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_1 i)) a b))) -> (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (Insert.insert.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInsert.{max u1 u2} (forall (i : ι), α i)) a s))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)} {a : forall (i : ι), α i}, (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) -> (forall {{b : forall (i : ι), α i}}, (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u2) (succ u1)} (forall (i : ι), α i) a b) -> (Not (StrongLT.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u1} (α i) (_inst_1 i)) b a))) -> (forall {{b : forall (i : ι), α i}}, (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u2) (succ u1)} (forall (i : ι), α i) a b) -> (Not (StrongLT.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u1} (α i) (_inst_1 i)) a b))) -> (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (Insert.insert.{max u2 u1, max u1 u2} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInsertSet.{max u2 u1} (forall (i : ι), α i)) a s))
Case conversion may be inaccurate. Consider using '#align is_weak_antichain.insert IsWeakAntichain.insertₓ'. -/
protected theorem insert (hs : IsWeakAntichain s) :
    (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬b ≺ a) →
      (∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b) → IsWeakAntichain (insert a s) :=
  hs.insert
#align is_weak_antichain.insert IsWeakAntichain.insert

end IsWeakAntichain

/- warning: is_weak_antichain_insert -> isWeakAntichain_insert is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)} {a : forall (i : ι), α i}, Iff (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (Insert.insert.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInsert.{max u1 u2} (forall (i : ι), α i)) a s)) (And (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) (forall {{b : forall (i : ι), α i}}, (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u1) (succ u2)} (forall (i : ι), α i) a b) -> (And (Not (StrongLT.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_1 i)) a b)) (Not (StrongLT.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u2} (α i) (_inst_1 i)) b a)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)} {a : forall (i : ι), α i}, Iff (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) (Insert.insert.{max u2 u1, max u1 u2} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInsertSet.{max u2 u1} (forall (i : ι), α i)) a s)) (And (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s) (forall {{b : forall (i : ι), α i}}, (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) b s) -> (Ne.{max (succ u2) (succ u1)} (forall (i : ι), α i) a b) -> (And (Not (StrongLT.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u1} (α i) (_inst_1 i)) a b)) (Not (StrongLT.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLT.{u1} (α i) (_inst_1 i)) b a)))))
Case conversion may be inaccurate. Consider using '#align is_weak_antichain_insert isWeakAntichain_insertₓ'. -/
theorem isWeakAntichain_insert :
    IsWeakAntichain (insert a s) ↔ IsWeakAntichain s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬a ≺ b ∧ ¬b ≺ a :=
  isAntichain_insert
#align is_weak_antichain_insert isWeakAntichain_insert

/- warning: is_antichain.is_weak_antichain -> IsAntichain.isWeakAntichain is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)}, (IsAntichain.{max u1 u2} (forall (i : ι), α i) (LE.le.{max u1 u2} (forall (i : ι), α i) (Pi.hasLe.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLE.{u2} (α i) (_inst_1 i)))) s) -> (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)}, (IsAntichain.{max u2 u1} (forall (i : ι), α i) (fun (x._@.Mathlib.Order.Antichain._hyg.5796 : forall (i : ι), α i) (x._@.Mathlib.Order.Antichain._hyg.5798 : forall (i : ι), α i) => LE.le.{max u2 u1} (forall (i : ι), α i) (Pi.hasLe.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => Preorder.toLE.{u1} (α i) (_inst_1 i))) x._@.Mathlib.Order.Antichain._hyg.5796 x._@.Mathlib.Order.Antichain._hyg.5798) s) -> (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s)
Case conversion may be inaccurate. Consider using '#align is_antichain.is_weak_antichain IsAntichain.isWeakAntichainₓ'. -/
protected theorem IsAntichain.isWeakAntichain (hs : IsAntichain (· ≤ ·) s) : IsWeakAntichain s :=
  hs.mono fun a b => le_of_strongLT
#align is_antichain.is_weak_antichain IsAntichain.isWeakAntichain

/- warning: set.subsingleton.is_weak_antichain -> Set.Subsingleton.isWeakAntichain is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : forall (i : ι), Preorder.{u2} (α i)] {s : Set.{max u1 u2} (forall (i : ι), α i)}, (Set.Subsingleton.{max u1 u2} (forall (i : ι), α i) s) -> (IsWeakAntichain.{u1, u2} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : forall (i : ι), Preorder.{u1} (α i)] {s : Set.{max u2 u1} (forall (i : ι), α i)}, (Set.Subsingleton.{max u2 u1} (forall (i : ι), α i) s) -> (IsWeakAntichain.{u2, u1} ι (fun (i : ι) => α i) (fun (i : ι) => _inst_1 i) s)
Case conversion may be inaccurate. Consider using '#align set.subsingleton.is_weak_antichain Set.Subsingleton.isWeakAntichainₓ'. -/
theorem Set.Subsingleton.isWeakAntichain (hs : s.Subsingleton) : IsWeakAntichain s :=
  hs.IsAntichain _
#align set.subsingleton.is_weak_antichain Set.Subsingleton.isWeakAntichain

end Pi

