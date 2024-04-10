/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Algebra.Group.Embedding
import Data.Fin.Basic
import Data.Finset.Basic
import Algebra.Order.Group.Int

#align_import data.finset.image from "leanprover-community/mathlib"@"65a1391a0106c9204fe45bc73a039f056558cb83"

/-! # Image and map operations on finite sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Thie file provides the finite analog of `set.image`, along with some other similar functions.

Note there are two ways to take the image over a finset; via `finset.image` which applies the
function then removes duplicates (requiring `decidable_eq`), or via `finset.map` which exploits
injectivity of the function to avoid needing to deduplicate. Choosing between these is similar to
choosing between `insert` and `finset.cons`, or between `finset.union` and `finset.disj_union`.

## Main definitions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.subtype`: `s.subtype p` is the the finset of `subtype p` whose elements belong to `s`.
* `finset.fin`:`s.fin n` is the finset of all elements of `s` less than `n`.

-/


variable {α β γ : Type _}

open Multiset

open Function

namespace Finset

/-! ### map -/


section Map

open Function

#print Finset.map /-
/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : Finset α) : Finset β :=
  ⟨s.1.map f, s.2.map f.2⟩
#align finset.map Finset.map
-/

#print Finset.map_val /-
@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl
#align finset.map_val Finset.map_val
-/

#print Finset.map_empty /-
@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl
#align finset.map_empty Finset.map_empty
-/

variable {f : α ↪ β} {s : Finset α}

#print Finset.mem_map /-
@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  mem_map.trans <| by simp only [exists_prop] <;> rfl
#align finset.mem_map Finset.mem_map
-/

#print Finset.mem_map_equiv /-
@[simp]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s := by
  rw [mem_map]; exact ⟨by rintro ⟨a, H, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩
#align finset.mem_map_equiv Finset.mem_map_equiv
-/

#print Finset.mem_map' /-
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2
#align finset.mem_map' Finset.mem_map'
-/

#print Finset.mem_map_of_mem /-
theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2
#align finset.mem_map_of_mem Finset.mem_map_of_mem
-/

#print Finset.forall_mem_map /-
theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀ y ∈ s.map f, p y H) ↔ ∀ x ∈ s, p (f x) (mem_map_of_mem _ H) :=
  ⟨fun h y hy => h (f y) (mem_map_of_mem _ hy), fun h x hx => by
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx; exact h _ hy⟩
#align finset.forall_mem_map Finset.forall_mem_map
-/

#print Finset.apply_coe_mem_map /-
theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.Prop
#align finset.apply_coe_mem_map Finset.apply_coe_mem_map
-/

#print Finset.coe_map /-
@[simp, norm_cast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext fun x => mem_map.trans Set.mem_image_iff_bex.symm
#align finset.coe_map Finset.coe_map
-/

#print Finset.coe_map_subset_range /-
theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.range f :=
  calc
    ↑(s.map f) = f '' s := coe_map f s
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
#align finset.coe_map_subset_range Finset.coe_map_subset_range
-/

#print Finset.map_perm /-
/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem map_perm {σ : Equiv.Perm α} (hs : {a | σ a ≠ a} ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs
#align finset.map_perm Finset.map_perm
-/

#print Finset.map_toFinset /-
theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, exists_prop, Multiset.mem_toFinset]
#align finset.map_to_finset Finset.map_toFinset
-/

#print Finset.map_refl /-
@[simp]
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using exists_eq_right
#align finset.map_refl Finset.map_refl
-/

#print Finset.map_cast_heq /-
@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) : HEq (s.map (Equiv.cast h).toEmbedding) s :=
  by subst h; simp
#align finset.map_cast_heq Finset.map_cast_heq
-/

#print Finset.map_map /-
theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by simp only [map_val, Multiset.map_map] <;> rfl
#align finset.map_map Finset.map_map
-/

#print Finset.map_comm /-
theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, embedding.trans, Function.comp, h_comm]
#align finset.map_comm Finset.map_comm
-/

#print Function.Semiconj.finset_map /-
theorem Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun s =>
  map_comm h
#align function.semiconj.finset_map Function.Semiconj.finset_map
-/

#print Function.Commute.finset_map /-
theorem Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.finset_map
#align function.commute.finset_map Function.Commute.finset_map
-/

#print Finset.map_subset_map /-
@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h x xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs, fun h => by
    simp [subset_def, map_subset_map h]⟩
#align finset.map_subset_map Finset.map_subset_map
-/

#print Finset.mapEmbedding /-
/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLEIff (map f) fun _ _ => map_subset_map
#align finset.map_embedding Finset.mapEmbedding
-/

#print Finset.map_inj /-
@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).Injective.eq_iff
#align finset.map_inj Finset.map_inj
-/

#print Finset.map_injective /-
theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).Injective
#align finset.map_injective Finset.map_injective
-/

#print Finset.mapEmbedding_apply /-
@[simp]
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl
#align finset.map_embedding_apply Finset.mapEmbedding_apply
-/

#print Finset.filter_map /-
theorem filter_map {p : β → Prop} [DecidablePred p] :
    (s.map f).filterₓ p = (s.filterₓ (p ∘ f)).map f :=
  eq_of_veq (map_filter _ _ _)
#align finset.filter_map Finset.filter_map
-/

#print Finset.map_filter' /-
theorem map_filter' (p : α → Prop) [DecidablePred p] (f : α ↪ β) (s : Finset α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (s.filterₓ p).map f = (s.map f).filterₓ fun b => ∃ a, p a ∧ f a = b := by
  simp [(· ∘ ·), filter_map, f.injective.eq_iff]
#align finset.map_filter' Finset.map_filter'
-/

#print Finset.filter_attach' /-
theorem filter_attach' [DecidableEq α] (s : Finset α) (p : s → Prop) [DecidablePred p] :
    s.attach.filterₓ p =
      (s.filterₓ fun x => ∃ h, p ⟨x, h⟩).attach.map
        ⟨Subtype.map id <| filter_subset _ _, Subtype.map_injective _ injective_id⟩ :=
  eq_of_veq <| Multiset.filter_attach' _ _
#align finset.filter_attach' Finset.filter_attach'
-/

#print Finset.filter_attach /-
@[simp]
theorem filter_attach (p : α → Prop) [DecidablePred p] (s : Finset α) :
    (s.attach.filterₓ fun x => p ↑x) =
      (s.filterₓ p).attach.map ((Embedding.refl _).subtypeMap mem_of_mem_filter) :=
  eq_of_veq <| Multiset.filter_attach _ _
#align finset.filter_attach Finset.filter_attach
-/

#print Finset.map_filter /-
theorem map_filter {f : α ≃ β} {p : α → Prop} [DecidablePred p] :
    (s.filterₓ p).map f.toEmbedding = (s.map f.toEmbedding).filterₓ (p ∘ f.symm) := by
  simp only [filter_map, Function.comp, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
#align finset.map_filter Finset.map_filter
-/

#print Finset.disjoint_map /-
@[simp]
theorem disjoint_map {s t : Finset α} (f : α ↪ β) : Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  by
  simp only [disjoint_iff_ne, mem_map, exists_prop, exists_imp, and_imp]
  refine' ⟨fun h a ha b hb hab => h _ _ ha rfl _ _ hb rfl <| congr_arg _ hab, _⟩
  rintro h _ a ha rfl _ b hb rfl
  exact f.injective.ne (h _ ha _ hb)
#align finset.disjoint_map Finset.disjoint_map
-/

#print Finset.map_disjUnion /-
theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _
#align finset.map_disj_union Finset.map_disjUnion
-/

#print Finset.map_disjUnion' /-
/-- A version of `finset.map_disj_union` for writing in the other direction. -/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _
#align finset.map_disj_union' Finset.map_disjUnion'
-/

#print Finset.map_union /-
theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_union, Set.image_union]
#align finset.map_union Finset.map_union
-/

#print Finset.map_inter /-
theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_inter, Set.image_inter f.injective]
#align finset.map_inter Finset.map_inter
-/

#print Finset.map_singleton /-
@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by simp only [coe_map, coe_singleton, Set.image_singleton]
#align finset.map_singleton Finset.map_singleton
-/

#print Finset.map_insert /-
@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]
#align finset.map_insert Finset.map_insert
-/

#print Finset.map_cons /-
@[simp]
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
  eq_of_veq <| Multiset.map_cons f a s.val
#align finset.map_cons Finset.map_cons
-/

#print Finset.map_eq_empty /-
@[simp]
theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun a m => ne_empty_of_mem (mem_map_of_mem _ m) h, fun e =>
    e.symm ▸ rfl⟩
#align finset.map_eq_empty Finset.map_eq_empty
-/

#print Finset.map_nonempty /-
@[simp]
theorem map_nonempty : (s.map f).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne.def, map_eq_empty]
#align finset.map_nonempty Finset.map_nonempty
-/

alias ⟨_, Nonempty.map⟩ := map_nonempty
#align finset.nonempty.map Finset.Nonempty.map

#print Finset.attach_map_val /-
theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by rw [map_val, attach_val] <;> exact attach_map_val _
#align finset.attach_map_val Finset.attach_map_val
-/

#print Finset.disjoint_range_addLeftEmbedding /-
theorem disjoint_range_addLeftEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) (range b)) :=
  by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding_apply, mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_left_embedding Finset.disjoint_range_addLeftEmbedding
-/

#print Finset.disjoint_range_addRightEmbedding /-
theorem disjoint_range_addRightEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) (range b)) :=
  by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding_apply, mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_right_embedding Finset.disjoint_range_addRightEmbedding
-/

#print Finset.map_disjiUnion /-
theorem map_disjiUnion {f : α ↪ β} {s : Finset α} {t : β → Finset γ} {h} :
    (s.map f).disjUnionₓ t h =
      s.disjUnionₓ (fun a => t (f a)) fun a ha b hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.Injective.Ne hab) :=
  eq_of_veq <| Multiset.bind_map _ _ _
#align finset.map_disj_Union Finset.map_disjiUnion
-/

#print Finset.disjiUnion_map /-
theorem disjiUnion_map {s : Finset α} {t : α → Finset β} {f : β ↪ γ} {h} :
    (s.disjUnionₓ t h).map f =
      s.disjUnionₓ (fun a => (t a).map f) fun a ha b hb hab =>
        disjoint_left.mpr fun x hxa hxb =>
          by
          obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa
          obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb
          obtain rfl := f.injective hfab
          exact disjoint_left.mp (h ha hb hab) hfa hfb :=
  eq_of_veq <| Multiset.map_bind _ _ _
#align finset.disj_Union_map Finset.disjiUnion_map
-/

end Map

#print Finset.range_add_one' /-
theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => Nat.succ.inj⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.succ_eq_add_one, Nat.zero_lt_succ n]
#align finset.range_add_one' Finset.range_add_one'
-/

/-! ### image -/


section Image

variable [DecidableEq β]

#print Finset.image /-
/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset
#align finset.image Finset.image
-/

#print Finset.image_val /-
@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl
#align finset.image_val Finset.image_val
-/

#print Finset.image_empty /-
@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).image f = ∅ :=
  rfl
#align finset.image_empty Finset.image_empty
-/

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

#print Finset.mem_image /-
@[simp]
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map, exists_prop]
#align finset.mem_image Finset.mem_image
-/

#print Finset.mem_image_of_mem /-
theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩
#align finset.mem_image_of_mem Finset.mem_image_of_mem
-/

#print Finset.forall_image /-
theorem forall_image {p : β → Prop} : (∀ b ∈ s.image f, p b) ↔ ∀ a ∈ s, p (f a) := by
  simp only [mem_image, forall_exists_index, forall_apply_eq_imp_iff₂]
#align finset.forall_image Finset.forall_image
-/

#print Finset.mem_image_const /-
@[simp]
theorem mem_image_const : c ∈ s.image (const α b) ↔ s.Nonempty ∧ b = c := by rw [mem_image];
  simp only [exists_prop, const_apply, exists_and_right]; rfl
#align finset.mem_image_const Finset.mem_image_const
-/

#print Finset.mem_image_const_self /-
theorem mem_image_const_self : b ∈ s.image (const α b) ↔ s.Nonempty :=
  mem_image_const.trans <| and_iff_left rfl
#align finset.mem_image_const_self Finset.mem_image_const_self
-/

#print Finset.canLift /-
instance canLift (c) (p) [CanLift β α c p] :
    CanLift (Finset β) (Finset α) (image c) fun s => ∀ x ∈ s, p x
    where prf := by
    rintro ⟨⟨l⟩, hd : l.nodup⟩ hl
    lift l to List α using hl
    exact ⟨⟨l, hd.of_map _⟩, ext fun a => by simp⟩
#align finset.can_lift Finset.canLift
-/

#print Finset.image_congr /-
theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s := by ext;
  simp_rw [mem_image]; exact exists₂_congr fun x hx => by rw [h hx]
#align finset.image_congr Finset.image_congr
-/

#print Function.Injective.mem_finset_image /-
theorem Function.Injective.mem_finset_image (hf : Injective f) : f a ∈ s.image f ↔ a ∈ s :=
  by
  refine' ⟨fun h => _, Finset.mem_image_of_mem f⟩
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  exact hf HEq ▸ hy
#align function.injective.mem_finset_image Function.Injective.mem_finset_image
-/

#print Finset.filter_mem_image_eq_image /-
theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) :
    (t.filterₓ fun y => y ∈ s.image f) = s.image f :=
  by
  ext; rw [mem_filter, mem_image]
  simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp]
  rintro x xel rfl; exact h _ xel
#align finset.filter_mem_image_eq_image Finset.filter_mem_image_eq_image
-/

#print Finset.fiber_nonempty_iff_mem_image /-
theorem fiber_nonempty_iff_mem_image (f : α → β) (s : Finset α) (y : β) :
    (s.filterₓ fun x => f x = y).Nonempty ↔ y ∈ s.image f := by simp [Finset.Nonempty]
#align finset.fiber_nonempty_iff_mem_image Finset.fiber_nonempty_iff_mem_image
-/

#print Finset.coe_image /-
@[simp, norm_cast]
theorem coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
  Set.ext fun _ => mem_image.trans Set.mem_image_iff_bex.symm
#align finset.coe_image Finset.coe_image
-/

#print Finset.Nonempty.image /-
protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.image f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, mem_image_of_mem f ha⟩
#align finset.nonempty.image Finset.Nonempty.image
-/

#print Finset.image_nonempty /-
@[simp]
theorem Finset.image_nonempty (f : α → β) : (s.image f).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx, _⟩ := mem_image.mp hy
    ⟨x, hx⟩,
    fun h => h.image f⟩
#align finset.nonempty.image_iff Finset.image_nonempty
-/

#print Finset.image_toFinset /-
theorem image_toFinset [DecidableEq α] {s : Multiset α} : s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, exists_prop, Multiset.mem_map]
#align finset.image_to_finset Finset.image_toFinset
-/

#print Finset.image_val_of_injOn /-
theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_onₓ H).dedup
#align finset.image_val_of_inj_on Finset.image_val_of_injOn
-/

#print Finset.image_id /-
@[simp]
theorem image_id [DecidableEq α] : s.image id = s :=
  ext fun _ => by simp only [mem_image, exists_prop, id, exists_eq_right]
#align finset.image_id Finset.image_id
-/

#print Finset.image_id' /-
@[simp]
theorem image_id' [DecidableEq α] : (s.image fun x => x) = s :=
  image_id
#align finset.image_id' Finset.image_id'
-/

#print Finset.image_image /-
theorem image_image [DecidableEq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
  eq_of_veq <| by simp only [image_val, dedup_map_dedup_eq, Multiset.map_map]
#align finset.image_image Finset.image_image
-/

#print Finset.image_comm /-
theorem image_comm {β'} [DecidableEq β'] [DecidableEq γ] {f : β → γ} {g : α → β} {f' : α → β'}
    {g' : β' → γ} (h_comm : ∀ a, f (g a) = g' (f' a)) :
    (s.image g).image f = (s.image f').image g' := by simp_rw [image_image, comp, h_comm]
#align finset.image_comm Finset.image_comm
-/

#print Function.Semiconj.finset_image /-
theorem Function.Semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s =>
  image_comm h
#align function.semiconj.finset_image Function.Semiconj.finset_image
-/

#print Function.Commute.finset_image /-
theorem Function.Commute.finset_image [DecidableEq α] {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  h.finset_image
#align function.commute.finset_image Function.Commute.finset_image
-/

#print Finset.image_subset_image /-
theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]
#align finset.image_subset_image Finset.image_subset_image
-/

#print Finset.image_subset_iff /-
theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
  calc
    s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff
#align finset.image_subset_iff Finset.image_subset_iff
-/

#print Finset.image_mono /-
theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image
#align finset.image_mono Finset.image_mono
-/

#print Finset.image_subset_image_iff /-
theorem image_subset_image_iff {t : Finset α} (hf : Injective f) : s.image f ⊆ t.image f ↔ s ⊆ t :=
  by simp_rw [← coe_subset]; push_cast; exact Set.image_subset_image_iff hf
#align finset.image_subset_image_iff Finset.image_subset_image_iff
-/

#print Finset.coe_image_subset_range /-
theorem coe_image_subset_range : ↑(s.image f) ⊆ Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
#align finset.coe_image_subset_range Finset.coe_image_subset_range
-/

#print Finset.filter_image /-
theorem filter_image {p : β → Prop} [DecidablePred p] :
    (s.image f).filterₓ p = (s.filterₓ (p ∘ f)).image f :=
  ext fun b => by
    simp only [mem_filter, mem_image, exists_prop] <;>
      exact
        ⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩ <;> exact ⟨x, ⟨h1, h2⟩, rfl⟩, by
          rintro ⟨x, ⟨h1, h2⟩, rfl⟩ <;> exact ⟨⟨x, h1, rfl⟩, h2⟩⟩
#align finset.image_filter Finset.filter_image
-/

#print Finset.image_union /-
theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  ext fun _ => by simp only [mem_image, mem_union, exists_prop, or_and_right, exists_or]
#align finset.image_union Finset.image_union
-/

#print Finset.image_inter_subset /-
theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
  subset_inter (image_subset_image <| inter_subset_left _ _) <|
    image_subset_image <| inter_subset_right _ _
#align finset.image_inter_subset Finset.image_inter_subset
-/

#print Finset.image_inter_of_injOn /-
theorem image_inter_of_injOn [DecidableEq α] {f : α → β} (s t : Finset α)
    (hf : Set.InjOn f (s ∪ t)) : (s ∩ t).image f = s.image f ∩ t.image f :=
  coe_injective <| by push_cast;
    exact Set.image_inter_on fun a ha b hb => hf (Or.inr ha) <| Or.inl hb
#align finset.image_inter_of_inj_on Finset.image_inter_of_injOn
-/

#print Finset.image_inter /-
theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
  image_inter_of_injOn _ _ <| hf.InjOn _
#align finset.image_inter Finset.image_inter
-/

#print Finset.image_singleton /-
@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext fun x => by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm
#align finset.image_singleton Finset.image_singleton
-/

#print Finset.image_insert /-
@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by
  simp only [insert_eq, image_singleton, image_union]
#align finset.image_insert Finset.image_insert
-/

#print Finset.erase_image_subset_image_erase /-
theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.image f).eraseₓ (f a) ⊆ (s.eraseₓ a).image f :=
  by
  simp only [subset_iff, and_imp, exists_prop, mem_image, exists_imp, mem_erase]
  rintro b hb x hx rfl
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩
#align finset.erase_image_subset_image_erase Finset.erase_image_subset_image_erase
-/

#print Finset.image_erase /-
@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.eraseₓ a).image f = (s.image f).eraseₓ (f a) :=
  by
  refine' (erase_image_subset_image_erase _ _ _).antisymm' fun b => _
  simp only [mem_image, exists_prop, mem_erase]
  rintro ⟨a', ⟨haa', ha'⟩, rfl⟩
  exact ⟨hf.ne haa', a', ha', rfl⟩
#align finset.image_erase Finset.image_erase
-/

#print Finset.image_eq_empty /-
@[simp]
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun a m => ne_empty_of_mem (mem_image_of_mem _ m) h, fun e =>
    e.symm ▸ rfl⟩
#align finset.image_eq_empty Finset.image_eq_empty
-/

#print Finset.image_sdiff /-
theorem image_sdiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s \ t).image f = s.image f \ t.image f :=
  coe_injective <| by push_cast; exact Set.image_diff hf _ _
#align finset.image_sdiff Finset.image_sdiff
-/

#print Finset.image_symmDiff /-
theorem image_symmDiff [DecidableEq α] {f : α → β} (s t : Finset α) (hf : Injective f) :
    (s ∆ t).image f = s.image f ∆ t.image f :=
  coe_injective <| by push_cast; exact Set.image_symmDiff hf _ _
#align finset.image_symm_diff Finset.image_symmDiff
-/

#print Disjoint.of_image_finset /-
@[simp]
theorem Disjoint.of_image_finset {s t : Finset α} {f : α → β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun a ha b hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
#align disjoint.of_image_finset Disjoint.of_image_finset
-/

#print Finset.mem_range_iff_mem_finset_range_of_mod_eq' /-
theorem mem_range_iff_mem_finset_range_of_mod_eq' [DecidableEq α] {f : ℕ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i :=
  by
  constructor
  · rintro ⟨i, hi⟩
    simp only [mem_image, exists_prop, mem_range]
    exact ⟨i % n, Nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩
  · rintro h
    simp only [mem_image, exists_prop, Set.mem_range, mem_range] at *
    rcases h with ⟨i, hi, ha⟩
    exact ⟨i, ha⟩
#align finset.mem_range_iff_mem_finset_range_of_mod_eq' Finset.mem_range_iff_mem_finset_range_of_mod_eq'
-/

#print Finset.mem_range_iff_mem_finset_range_of_mod_eq /-
theorem mem_range_iff_mem_finset_range_of_mod_eq [DecidableEq α] {f : ℤ → α} {a : α} {n : ℕ}
    (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
    a ∈ Set.range f ↔ a ∈ (Finset.range n).image fun i => f i :=
  suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a by simpa [h]
  have hn' : 0 < (n : ℤ) := Int.ofNat_lt.mpr hn
  Iff.intro
    (fun ⟨i, hi⟩ =>
      have : 0 ≤ i % ↑n := Int.emod_nonneg _ (ne_of_gt hn')
      ⟨Int.toNat (i % n), by
        rw [← Int.ofNat_lt, Int.toNat_of_nonneg this] <;> exact ⟨Int.emod_lt_of_pos i hn', hi⟩⟩)
    fun ⟨i, hi, ha⟩ =>
    ⟨i, by rw [Int.emod_eq_of_lt (Int.ofNat_zero_le _) (Int.ofNat_lt_ofNat_of_lt hi), ha]⟩
#align finset.mem_range_iff_mem_finset_range_of_mod_eq Finset.mem_range_iff_mem_finset_range_of_mod_eq
-/

#print Finset.range_add /-
theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) := by
  rw [← val_inj, union_val]; exact Multiset.range_add_eq_union a b
#align finset.range_add Finset.range_add
-/

#print Finset.attach_image_val /-
@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image Subtype.val = s :=
  eq_of_veq <| by rw [image_val, attach_val, Multiset.attach_map_val, dedup_eq_self]
#align finset.attach_image_val Finset.attach_image_val
-/

/- warning: finset.attach_image_coe clashes with finset.attach_image_val -> Finset.attach_image_val
Case conversion may be inaccurate. Consider using '#align finset.attach_image_coe Finset.attach_image_valₓ'. -/
#print Finset.attach_image_val /-
@[simp]
theorem attach_image_val [DecidableEq α] {s : Finset α} : s.attach.image coe = s :=
  Finset.attach_image_val
#align finset.attach_image_coe Finset.attach_image_val
-/

#print Finset.attach_insert /-
@[simp]
theorem attach_insert [DecidableEq α] {a : α} {s : Finset α} :
    attach (insert a s) =
      insert (⟨a, mem_insert_self a s⟩ : { x // x ∈ insert a s })
        ((attach s).image fun x => ⟨x.1, mem_insert_of_mem x.2⟩) :=
  ext fun ⟨x, hx⟩ =>
    ⟨Or.cases_on (mem_insert.1 hx)
        (fun h : x = a => fun _ => mem_insert.2 <| Or.inl <| Subtype.eq h) fun h : x ∈ s => fun _ =>
        mem_insert_of_mem <| mem_image.2 <| ⟨⟨x, h⟩, mem_attach _ _, Subtype.eq rfl⟩,
      fun _ => Finset.mem_attach _ _⟩
#align finset.attach_insert Finset.attach_insert
-/

#print Finset.map_eq_image /-
theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm
#align finset.map_eq_image Finset.map_eq_image
-/

#print Finset.disjoint_image /-
@[simp]
theorem disjoint_image {s t : Finset α} {f : α → β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t := by
  convert disjoint_map ⟨_, hf⟩ <;> simp [map_eq_image]
#align finset.disjoint_image Finset.disjoint_image
-/

#print Finset.image_const /-
theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun a => b) = singleton b :=
  ext fun b' => by
    simp only [mem_image, exists_prop, exists_and_right, h.bex, true_and_iff, mem_singleton,
      eq_comm]
#align finset.image_const Finset.image_const
-/

#print Finset.map_erase /-
@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.eraseₓ a).map f = (s.map f).eraseₓ (f a) := by simp_rw [map_eq_image];
  exact s.image_erase f.2 a
#align finset.map_erase Finset.map_erase
-/

#print Finset.image_biUnion /-
theorem image_biUnion [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.image f).biUnion t = s.biUnion fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by simp only [image_insert, bUnion_insert, ih]
#align finset.image_bUnion Finset.image_biUnion
-/

#print Finset.biUnion_image /-
theorem biUnion_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.biUnion t).image f = s.biUnion fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by simp only [bUnion_insert, image_union, ih]
#align finset.bUnion_image Finset.biUnion_image
-/

#print Finset.image_biUnion_filter_eq /-
theorem image_biUnion_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.image g).biUnion fun a => s.filterₓ fun c => g c = a) = s :=
  biUnion_filter_eq_of_maps_to fun x => mem_image_of_mem g
#align finset.image_bUnion_filter_eq Finset.image_biUnion_filter_eq
-/

#print Finset.biUnion_singleton /-
theorem biUnion_singleton {f : α → β} : (s.biUnion fun a => {f a}) = s.image f :=
  ext fun x => by simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]
#align finset.bUnion_singleton Finset.biUnion_singleton
-/

end Image

/-! ### Subtype -/


section Subtype

#print Finset.subtype /-
/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [DecidablePred p] (s : Finset α) : Finset (Subtype p) :=
  (s.filterₓ p).attach.map
    ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩, fun x y H => Subtype.eq <| Subtype.mk.inj H⟩
#align finset.subtype Finset.subtype
-/

#print Finset.mem_subtype /-
@[simp]
theorem mem_subtype {p : α → Prop} [DecidablePred p] {s : Finset α} :
    ∀ {a : Subtype p}, a ∈ s.Subtype p ↔ (a : α) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.subtype, ha]
#align finset.mem_subtype Finset.mem_subtype
-/

#print Finset.subtype_eq_empty /-
theorem subtype_eq_empty {p : α → Prop} [DecidablePred p] {s : Finset α} :
    s.Subtype p = ∅ ↔ ∀ x, p x → x ∉ s := by simp [ext_iff, Subtype.forall, Subtype.coe_mk] <;> rfl
#align finset.subtype_eq_empty Finset.subtype_eq_empty
-/

#print Finset.subtype_mono /-
@[mono]
theorem subtype_mono {p : α → Prop} [DecidablePred p] : Monotone (Finset.subtype p) :=
  fun s t h x hx => mem_subtype.2 <| h <| mem_subtype.1 hx
#align finset.subtype_mono Finset.subtype_mono
-/

#print Finset.subtype_map /-
/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp]
theorem subtype_map (p : α → Prop) [DecidablePred p] {s : Finset α} :
    (s.Subtype p).map (Embedding.subtype _) = s.filterₓ p :=
  by
  ext x
  simp [and_comm' _ (_ = _), @and_left_comm _ (_ = _), and_comm' (p x) (x ∈ s)]
#align finset.subtype_map Finset.subtype_map
-/

#print Finset.subtype_map_of_mem /-
/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
theorem subtype_map_of_mem {p : α → Prop} [DecidablePred p] {s : Finset α} (h : ∀ x ∈ s, p x) :
    (s.Subtype p).map (Embedding.subtype _) = s := by rw [subtype_map, filter_true_of_mem h]
#align finset.subtype_map_of_mem Finset.subtype_map_of_mem
-/

#print Finset.property_of_mem_map_subtype /-
/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
theorem property_of_mem_map_subtype {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : a ∈ s.map (Embedding.subtype _)) : p a :=
  by
  rcases mem_map.1 h with ⟨x, hx, rfl⟩
  exact x.2
#align finset.property_of_mem_map_subtype Finset.property_of_mem_map_subtype
-/

#print Finset.not_mem_map_subtype_of_not_property /-
/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
theorem not_mem_map_subtype_of_not_property {p : α → Prop} (s : Finset { x // p x }) {a : α}
    (h : ¬p a) : a ∉ s.map (Embedding.subtype _) :=
  mt s.property_of_mem_map_subtype h
#align finset.not_mem_map_subtype_of_not_property Finset.not_mem_map_subtype_of_not_property
-/

#print Finset.map_subtype_subset /-
/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
theorem map_subtype_subset {t : Set α} (s : Finset t) : ↑(s.map (Embedding.subtype _)) ⊆ t :=
  by
  intro a ha
  rw [mem_coe] at ha
  convert property_of_mem_map_subtype s ha
#align finset.map_subtype_subset Finset.map_subtype_subset
-/

end Subtype

/-! ### Fin -/


#print Finset.fin /-
/-- Given a finset `s` of natural numbers and a bound `n`,
`s.fin n` is the finset of all elements of `s` less than `n`.
-/
protected def fin (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  (s.Subtype _).map Fin.equivSubtype.symm.toEmbedding
#align finset.fin Finset.fin
-/

#print Finset.mem_fin /-
@[simp]
theorem mem_fin {n} {s : Finset ℕ} : ∀ a : Fin n, a ∈ s.Fin n ↔ (a : ℕ) ∈ s
  | ⟨a, ha⟩ => by simp [Finset.fin]
#align finset.mem_fin Finset.mem_fin
-/

#print Finset.fin_mono /-
@[mono]
theorem fin_mono {n} : Monotone (Finset.fin n) := fun s t h x => by simpa using @h x
#align finset.fin_mono Finset.fin_mono
-/

#print Finset.fin_map /-
@[simp]
theorem fin_map {n} {s : Finset ℕ} : (s.Fin n).map Fin.valEmbedding = s.filterₓ (· < n) := by
  simp [Finset.fin, Finset.map_map]
#align finset.fin_map Finset.fin_map
-/

#print Finset.subset_image_iff /-
theorem subset_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α → β} :
    ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.image f = t :=
  by
  constructor; swap
  · rintro ⟨t, ht, rfl⟩; rw [coe_image]; exact Set.image_subset f ht
  intro h
  letI : CanLift β s (f ∘ coe) fun y => y ∈ f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
  lift t to Finset s using h
  refine' ⟨t.map (embedding.subtype _), map_subtype_subset _, _⟩
  ext y; simp
#align finset.subset_image_iff Finset.subset_image_iff
-/

#print Finset.range_sdiff_zero /-
theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ :=
  by
  induction' n with k hk
  · simp
  nth_rw 2 [range_succ]
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  simp
#align finset.range_sdiff_zero Finset.range_sdiff_zero
-/

end Finset

#print Multiset.toFinset_map /-
theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm
#align multiset.to_finset_map Multiset.toFinset_map
-/

namespace Equiv

#print Equiv.finsetCongr /-
/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finsetCongr (e : α ≃ β) : Finset α ≃ Finset β
    where
  toFun s := s.map e.toEmbedding
  invFun s := s.map e.symm.toEmbedding
  left_inv s := by simp [Finset.map_map]
  right_inv s := by simp [Finset.map_map]
#align equiv.finset_congr Equiv.finsetCongr
-/

#print Equiv.finsetCongr_apply /-
@[simp]
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl
#align equiv.finset_congr_apply Equiv.finsetCongr_apply
-/

#print Equiv.finsetCongr_refl /-
@[simp]
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ := by ext; simp
#align equiv.finset_congr_refl Equiv.finsetCongr_refl
-/

#print Equiv.finsetCongr_symm /-
@[simp]
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl
#align equiv.finset_congr_symm Equiv.finsetCongr_symm
-/

#print Equiv.finsetCongr_trans /-
@[simp]
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr := by ext;
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]
#align equiv.finset_congr_trans Equiv.finsetCongr_trans
-/

#print Equiv.finsetCongr_toEmbedding /-
theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl
#align equiv.finset_congr_to_embedding Equiv.finsetCongr_toEmbedding
-/

end Equiv

