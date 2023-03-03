/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro

! This file was ported from Lean 3 source module data.finset.image
! leanprover-community/mathlib commit e04043d6bf7264a3c84bc69711dc354958ca4516
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Embedding
import Mathbin.Data.Fin.Basic
import Mathbin.Data.Finset.Basic
import Mathbin.Data.Int.Order.Basic

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

/- warning: finset.map_val -> Finset.map_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Finset.val.{u2} β (Finset.map.{u1, u2} α β f s)) (Multiset.map.{u1, u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) (Finset.val.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Finset.val.{u1} β (Finset.map.{u2, u1} α β f s)) (Multiset.map.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) (Finset.val.{u2} α s))
Case conversion may be inaccurate. Consider using '#align finset.map_val Finset.map_valₓ'. -/
@[simp]
theorem map_val (f : α ↪ β) (s : Finset α) : (map f s).1 = s.1.map f :=
  rfl
#align finset.map_val Finset.map_val

/- warning: finset.map_empty -> Finset.map_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))
Case conversion may be inaccurate. Consider using '#align finset.map_empty Finset.map_emptyₓ'. -/
@[simp]
theorem map_empty (f : α ↪ β) : (∅ : Finset α).map f = ∅ :=
  rfl
#align finset.map_empty Finset.map_empty

variable {f : α ↪ β} {s : Finset α}

/- warning: finset.mem_map -> Finset.mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) f a) b)))
Case conversion may be inaccurate. Consider using '#align finset.mem_map Finset.mem_mapₓ'. -/
@[simp]
theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
  mem_map.trans <| by simp only [exists_prop] <;> rfl
#align finset.mem_map Finset.mem_map

/- warning: finset.mem_map_equiv -> Finset.mem_map_equiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {f : Equiv.{succ u1, succ u2} α β} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.map.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β f) s)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f) b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {f : Equiv.{succ u2, succ u1} α β} {b : β}, Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b (Finset.map.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β f) s)) (Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) b) (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β f) b) s)
Case conversion may be inaccurate. Consider using '#align finset.mem_map_equiv Finset.mem_map_equivₓ'. -/
@[simp]
theorem mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.toEmbedding ↔ f.symm b ∈ s :=
  by
  rw [mem_map]
  exact
    ⟨by
      rintro ⟨a, H, rfl⟩
      simpa, fun h => ⟨_, h, by simp⟩⟩
#align finset.mem_map_equiv Finset.mem_map_equiv

/- warning: finset.mem_map' -> Finset.mem_map' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) {a : α} {s : Finset.{u1} α}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) {a : α} {s : Finset.{u2} α}, Iff (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s)) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)
Case conversion may be inaccurate. Consider using '#align finset.mem_map' Finset.mem_map'ₓ'. -/
theorem mem_map' (f : α ↪ β) {a} {s : Finset α} : f a ∈ s.map f ↔ a ∈ s :=
  mem_map_of_injective f.2
#align finset.mem_map' Finset.mem_map'

/- warning: finset.mem_map_of_mem -> Finset.mem_map_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) {a : α} {s : Finset.{u1} α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) {a : α} {s : Finset.{u2} α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align finset.mem_map_of_mem Finset.mem_map_of_memₓ'. -/
theorem mem_map_of_mem (f : α ↪ β) {a} {s : Finset α} : a ∈ s → f a ∈ s.map f :=
  (mem_map' _).2
#align finset.mem_map_of_mem Finset.mem_map_of_mem

/- warning: finset.forall_mem_map -> Finset.forall_mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α} {p : forall (a : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (Finset.map.{u1, u2} α β f s)) -> Prop}, Iff (forall (y : β) (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.map.{u1, u2} α β f s)), p y H) (forall (x : α) (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s), p (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f x) (Finset.mem_map_of_mem.{u1, u2} α β f x s H))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} {s : Finset.{u2} α} {p : forall (a : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) a (Finset.map.{u2, u1} α β f s)) -> Prop}, Iff (forall (y : β) (H : Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.map.{u2, u1} α β f s)), p y H) (forall (x : α) (H : Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s), p (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f x) (Finset.mem_map_of_mem.{u1, u2} α β f x s H))
Case conversion may be inaccurate. Consider using '#align finset.forall_mem_map Finset.forall_mem_mapₓ'. -/
theorem forall_mem_map {f : α ↪ β} {s : Finset α} {p : ∀ a, a ∈ s.map f → Prop} :
    (∀ y ∈ s.map f, p y H) ↔ ∀ x ∈ s, p (f x) (mem_map_of_mem _ H) :=
  ⟨fun h y hy => h (f y) (mem_map_of_mem _ hy), fun h x hx =>
    by
    obtain ⟨y, hy, rfl⟩ := mem_map.1 hx
    exact h _ hy⟩
#align finset.forall_mem_map Finset.forall_mem_map

/- warning: finset.apply_coe_mem_map -> Finset.apply_coe_mem_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α) (x : coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s), Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (HasLiftT.mk.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (CoeTCₓ.coe.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeBase.{succ u1, succ u1} (coeSort.{succ u1, succ (succ u1)} (Finset.{u1} α) Type.{u1} (Finset.hasCoeToSort.{u1} α) s) α (coeSubtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s))))) x)) (Finset.map.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α) (x : Subtype.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s)), Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x)) (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f (Subtype.val.{succ u2} α (fun (x : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) x)) (Finset.map.{u2, u1} α β f s)
Case conversion may be inaccurate. Consider using '#align finset.apply_coe_mem_map Finset.apply_coe_mem_mapₓ'. -/
theorem apply_coe_mem_map (f : α ↪ β) (s : Finset α) (x : s) : f x ∈ s.map f :=
  mem_map_of_mem f x.Prop
#align finset.apply_coe_mem_map Finset.apply_coe_mem_map

/- warning: finset.coe_map -> Finset.coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α), Eq.{succ u2} (Set.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.map.{u1, u2} α β f s)) (Set.image.{u1, u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α), Eq.{succ u1} (Set.{u1} β) (Finset.toSet.{u1} β (Finset.map.{u2, u1} α β f s)) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) (Finset.toSet.{u2} α s))
Case conversion may be inaccurate. Consider using '#align finset.coe_map Finset.coe_mapₓ'. -/
@[simp, norm_cast]
theorem coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) = f '' s :=
  Set.ext fun x => mem_map.trans Set.mem_image_iff_bex.symm
#align finset.coe_map Finset.coe_map

/- warning: finset.coe_map_subset_range -> Finset.coe_map_subset_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.map.{u1, u2} α β f s)) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Finset.toSet.{u1} β (Finset.map.{u2, u1} α β f s)) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))
Case conversion may be inaccurate. Consider using '#align finset.coe_map_subset_range Finset.coe_map_subset_rangeₓ'. -/
theorem coe_map_subset_range (f : α ↪ β) (s : Finset α) : (s.map f : Set β) ⊆ Set.range f :=
  calc
    ↑(s.map f) = f '' s := coe_map f s
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
    
#align finset.coe_map_subset_range Finset.coe_map_subset_range

#print Finset.map_perm /-
/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
theorem map_perm {σ : Equiv.Perm α} (hs : { a | σ a ≠ a } ⊆ s) : s.map (σ : α ↪ α) = s :=
  coe_injective <| (coe_map _ _).trans <| Set.image_perm hs
#align finset.map_perm Finset.map_perm
-/

/- warning: finset.map_to_finset -> Finset.map_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {s : Multiset.{u1} α}, Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u1, u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] {s : Multiset.{u2} α}, Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Multiset.toFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) s))
Case conversion may be inaccurate. Consider using '#align finset.map_to_finset Finset.map_toFinsetₓ'. -/
theorem map_toFinset [DecidableEq α] [DecidableEq β] {s : Multiset α} :
    s.toFinset.map f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_map, Multiset.mem_map, exists_prop, Multiset.mem_toFinset]
#align finset.map_to_finset Finset.map_toFinset

#print Finset.map_refl /-
@[simp]
theorem map_refl : s.map (Embedding.refl _) = s :=
  ext fun _ => by simpa only [mem_map, exists_prop] using exists_eq_right
#align finset.map_refl Finset.map_refl
-/

#print Finset.map_cast_heq /-
@[simp]
theorem map_cast_heq {α β} (h : α = β) (s : Finset α) : HEq (s.map (Equiv.cast h).toEmbedding) s :=
  by
  subst h
  simp
#align finset.map_cast_heq Finset.map_cast_heq
-/

/- warning: finset.map_map -> Finset.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (f : Function.Embedding.{succ u1, succ u2} α β) (g : Function.Embedding.{succ u2, succ u3} β γ) (s : Finset.{u1} α), Eq.{succ u3} (Finset.{u3} γ) (Finset.map.{u2, u3} β γ g (Finset.map.{u1, u2} α β f s)) (Finset.map.{u1, u3} α γ (Function.Embedding.trans.{succ u1, succ u2, succ u3} α β γ f g) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (f : Function.Embedding.{succ u3, succ u2} α β) (g : Function.Embedding.{succ u2, succ u1} β γ) (s : Finset.{u3} α), Eq.{succ u1} (Finset.{u1} γ) (Finset.map.{u2, u1} β γ g (Finset.map.{u3, u2} α β f s)) (Finset.map.{u3, u1} α γ (Function.Embedding.trans.{succ u3, succ u2, succ u1} α β γ f g) s)
Case conversion may be inaccurate. Consider using '#align finset.map_map Finset.map_mapₓ'. -/
theorem map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map f).map g = s.map (f.trans g) :=
  eq_of_veq <| by simp only [map_val, Multiset.map_map] <;> rfl
#align finset.map_map Finset.map_map

/- warning: finset.map_comm -> Finset.map_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Finset.{u1} α} {β' : Type.{u4}} {f : Function.Embedding.{succ u2, succ u3} β γ} {g : Function.Embedding.{succ u1, succ u2} α β} {f' : Function.Embedding.{succ u1, succ u4} α β'} {g' : Function.Embedding.{succ u4, succ u3} β' γ}, (forall (a : α), Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) g a)) (coeFn.{max 1 (succ u4) (succ u3), max (succ u4) (succ u3)} (Function.Embedding.{succ u4, succ u3} β' γ) (fun (_x : Function.Embedding.{succ u4, succ u3} β' γ) => β' -> γ) (Function.Embedding.hasCoeToFun.{succ u4, succ u3} β' γ) g' (coeFn.{max 1 (succ u1) (succ u4), max (succ u1) (succ u4)} (Function.Embedding.{succ u1, succ u4} α β') (fun (_x : Function.Embedding.{succ u1, succ u4} α β') => α -> β') (Function.Embedding.hasCoeToFun.{succ u1, succ u4} α β') f' a))) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.map.{u2, u3} β γ f (Finset.map.{u1, u2} α β g s)) (Finset.map.{u4, u3} β' γ g' (Finset.map.{u1, u4} α β' f' s)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Finset.{u1} α} {β' : Type.{u4}} {f : Function.Embedding.{succ u3, succ u2} β γ} {g : Function.Embedding.{succ u1, succ u3} α β} {f' : Function.Embedding.{succ u1, succ u4} α β'} {g' : Function.Embedding.{succ u4, succ u2} β' γ}, (forall (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u3} α β)) g a)) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} β γ)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u3} α β)) g a)) (FunLike.coe.{max (succ u2) (succ u4), succ u4, succ u2} (Function.Embedding.{succ u4, succ u2} β' γ) β' (fun (_x : β') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β') => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u4), succ u4, succ u2} (Function.Embedding.{succ u4, succ u2} β' γ) β' γ (Function.instEmbeddingLikeEmbedding.{succ u4, succ u2} β' γ)) g' (FunLike.coe.{max (succ u1) (succ u4), succ u1, succ u4} (Function.Embedding.{succ u1, succ u4} α β') α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β') _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u4), succ u1, succ u4} (Function.Embedding.{succ u1, succ u4} α β') α β' (Function.instEmbeddingLikeEmbedding.{succ u1, succ u4} α β')) f' a))) -> (Eq.{succ u2} (Finset.{u2} γ) (Finset.map.{u3, u2} β γ f (Finset.map.{u1, u3} α β g s)) (Finset.map.{u4, u2} β' γ g' (Finset.map.{u1, u4} α β' f' s)))
Case conversion may be inaccurate. Consider using '#align finset.map_comm Finset.map_commₓ'. -/
theorem map_comm {β'} {f : β ↪ γ} {g : α ↪ β} {f' : α ↪ β'} {g' : β' ↪ γ}
    (h_comm : ∀ a, f (g a) = g' (f' a)) : (s.map g).map f = (s.map f').map g' := by
  simp_rw [map_map, embedding.trans, Function.comp, h_comm]
#align finset.map_comm Finset.map_comm

/- warning: function.semiconj.finset_map -> Function.Semiconj.finset_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {ga : Function.Embedding.{succ u1, succ u1} α α} {gb : Function.Embedding.{succ u2, succ u2} β β}, (Function.Semiconj.{u1, u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) (coeFn.{succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) (fun (_x : Function.Embedding.{succ u1, succ u1} α α) => α -> α) (Function.Embedding.hasCoeToFun.{succ u1, succ u1} α α) ga) (coeFn.{succ u2, succ u2} (Function.Embedding.{succ u2, succ u2} β β) (fun (_x : Function.Embedding.{succ u2, succ u2} β β) => β -> β) (Function.Embedding.hasCoeToFun.{succ u2, succ u2} β β) gb)) -> (Function.Semiconj.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.map.{u1, u2} α β f) (Finset.map.{u1, u1} α α ga) (Finset.map.{u2, u2} β β gb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} {ga : Function.Embedding.{succ u2, succ u2} α α} {gb : Function.Embedding.{succ u1, succ u1} β β}, (Function.Semiconj.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) (FunLike.coe.{succ u2, succ u2, succ u2} (Function.Embedding.{succ u2, succ u2} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u2, succ u2, succ u2} (Function.Embedding.{succ u2, succ u2} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u2, succ u2} α α)) ga) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} β β) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => β) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} β β) β β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} β β)) gb)) -> (Function.Semiconj.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.map.{u2, u1} α β f) (Finset.map.{u2, u2} α α ga) (Finset.map.{u1, u1} β β gb))
Case conversion may be inaccurate. Consider using '#align function.semiconj.finset_map Function.Semiconj.finset_mapₓ'. -/
theorem Function.Semiconj.finset_map {f : α ↪ β} {ga : α ↪ α} {gb : β ↪ β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (map f) (map ga) (map gb) := fun s =>
  map_comm h
#align function.semiconj.finset_map Function.Semiconj.finset_map

#print Function.Commute.finset_map /-
theorem Function.Commute.finset_map {f g : α ↪ α} (h : Function.Commute f g) :
    Function.Commute (map f) (map g) :=
  h.finset_map
#align function.commute.finset_map Function.Commute.finset_map
-/

/- warning: finset.map_subset_map -> Finset.map_subset_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α}, Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align finset.map_subset_map Finset.map_subset_mapₓ'. -/
@[simp]
theorem map_subset_map {s₁ s₂ : Finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
  ⟨fun h x xs => (mem_map' _).1 <| h <| (mem_map' f).2 xs, fun h => by
    simp [subset_def, map_subset_map h]⟩
#align finset.map_subset_map Finset.map_subset_map

#print Finset.mapEmbedding /-
/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def mapEmbedding (f : α ↪ β) : Finset α ↪o Finset β :=
  OrderEmbedding.ofMapLeIff (map f) fun _ _ => map_subset_map
#align finset.map_embedding Finset.mapEmbedding
-/

/- warning: finset.map_inj -> Finset.map_inj is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, Iff (Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (Eq.{succ u1} (Finset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α}, Iff (Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (Eq.{succ u2} (Finset.{u2} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align finset.map_inj Finset.map_injₓ'. -/
@[simp]
theorem map_inj {s₁ s₂ : Finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
  (mapEmbedding f).Injective.eq_iff
#align finset.map_inj Finset.map_inj

/- warning: finset.map_injective -> Finset.map_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β), Function.Injective.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.map.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β), Function.Injective.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.map.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align finset.map_injective Finset.map_injectiveₓ'. -/
theorem map_injective (f : α ↪ β) : Injective (map f) :=
  (mapEmbedding f).Injective
#align finset.map_injective Finset.map_injective

/- warning: finset.map_embedding_apply -> Finset.mapEmbedding_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α}, Eq.{succ u2} (Finset.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderEmbedding.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)))) (fun (_x : RelEmbedding.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u2} (Finset.{u2} β) (Preorder.toLE.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β))))) => (Finset.{u1} α) -> (Finset.{u2} β)) (RelEmbedding.hasCoeToFun.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u2} (Finset.{u2} β) (Preorder.toLE.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β))))) (Finset.mapEmbedding.{u1, u2} α β f) s) (Finset.map.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α}, Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u2} β) s) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u2} β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) (Finset.{u1} α) (Finset.{u2} β) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β))) (RelEmbedding.toEmbedding.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u2} β) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u2} β) => LE.le.{u2} (Finset.{u2} β) (Preorder.toLE.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.mapEmbedding.{u1, u2} α β f)) s) (Finset.map.{u1, u2} α β f s)
Case conversion may be inaccurate. Consider using '#align finset.map_embedding_apply Finset.mapEmbedding_applyₓ'. -/
@[simp]
theorem mapEmbedding_apply : mapEmbedding f s = map f s :=
  rfl
#align finset.map_embedding_apply Finset.mapEmbedding_apply

#print Finset.filter_map /-
theorem filter_map {p : β → Prop} [DecidablePred p] :
    (s.map f).filterₓ p = (s.filterₓ (p ∘ f)).map f :=
  eq_of_veq (map_filter _ _ _)
#align finset.filter_map Finset.filter_map
-/

/- warning: finset.map_filter -> Finset.map_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {f : Equiv.{succ u1, succ u2} α β} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u1} α p], Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β f) (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Finset.filter.{u2} β (Function.comp.{succ u2, succ u1, 1} β α Prop p (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f))) (fun (a : β) => _inst_1 (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β f) a)) (Finset.map.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {f : Equiv.{succ u2, succ u1} α β} {p : α -> Prop} [_inst_1 : DecidablePred.{succ u2} α p], Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β f) (Finset.filter.{u2} α p (fun (a : α) => _inst_1 a) s)) (Finset.filter.{u1} β (Function.comp.{succ u1, succ u2, 1} β α Prop p (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β f))) (fun (a : β) => instDecidablePredCompProp.{succ u1, succ u2} β α p (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (a : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) a) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β f)) (fun (a : α) => _inst_1 a) a) (Finset.map.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β f) s))
Case conversion may be inaccurate. Consider using '#align finset.map_filter Finset.map_filterₓ'. -/
theorem map_filter {f : α ≃ β} {p : α → Prop} [DecidablePred p] :
    (s.filterₓ p).map f.toEmbedding = (s.map f.toEmbedding).filterₓ (p ∘ f.symm) := by
  simp only [filter_map, Function.comp, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
#align finset.map_filter Finset.map_filter

/- warning: finset.disjoint_map -> Finset.disjoint_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u1} α} (f : Function.Embedding.{succ u1, succ u2} α β), Iff (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.map.{u1, u2} α β f s) (Finset.map.{u1, u2} α β f t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u2} α} (f : Function.Embedding.{succ u2, succ u1} α β), Iff (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.map.{u2, u1} α β f s) (Finset.map.{u2, u1} α β f t)) (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s t)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_map Finset.disjoint_mapₓ'. -/
@[simp]
theorem disjoint_map {s t : Finset α} (f : α ↪ β) : Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  by
  simp only [disjoint_iff_ne, mem_map, exists_prop, exists_imp, and_imp]
  refine' ⟨fun h a ha b hb hab => h _ _ ha rfl _ _ hb rfl <| congr_arg _ hab, _⟩
  rintro h _ a ha rfl _ b hb rfl
  exact f.injective.ne (h _ ha _ hb)
#align finset.disjoint_map Finset.disjoint_map

/- warning: finset.map_disj_union -> Finset.map_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α) (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂) (h' : optParam.{0} (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (Iff.mpr (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂) (Finset.disjoint_map.{u1, u2} α β s₁ s₂ f) h)), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Finset.disjUnion.{u1} α s₁ s₂ h)) (Finset.disjUnion.{u2} β (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂) h')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α) (h : Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂) (h' : optParam.{0} (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (Iff.mpr (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂) (Finset.disjoint_map.{u1, u2} α β s₁ s₂ f) h)), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Finset.disjUnion.{u2} α s₁ s₂ h)) (Finset.disjUnion.{u1} β (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂) h')
Case conversion may be inaccurate. Consider using '#align finset.map_disj_union Finset.map_disjUnionₓ'. -/
theorem map_disjUnion {f : α ↪ β} (s₁ s₂ : Finset α) (h) (h' := (disjoint_map _).mpr h) :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  eq_of_veq <| Multiset.map_add _ _ _
#align finset.map_disj_union Finset.map_disjUnion

/- warning: finset.map_disj_union' -> Finset.map_disjUnion' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : Function.Embedding.{succ u1, succ u2} α β} (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α) (h' : Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (h : optParam.{0} (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂) (Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂) (Finset.disjoint_map.{u1, u2} α β s₁ s₂ f) h')), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Finset.disjUnion.{u1} α s₁ s₂ h)) (Finset.disjUnion.{u2} β (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂) h')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : Function.Embedding.{succ u2, succ u1} α β} (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α) (h' : Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (h : optParam.{0} (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂) (Iff.mp (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂)) (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂) (Finset.disjoint_map.{u1, u2} α β s₁ s₂ f) h')), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Finset.disjUnion.{u2} α s₁ s₂ h)) (Finset.disjUnion.{u1} β (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂) h')
Case conversion may be inaccurate. Consider using '#align finset.map_disj_union' Finset.map_disjUnion'ₓ'. -/
/-- A version of `finset.map_disj_union` for writing in the other direction. -/
theorem map_disjUnion' {f : α ↪ β} (s₁ s₂ : Finset α) (h') (h := (disjoint_map _).mp h') :
    (s₁.disjUnion s₂ h).map f = (s₁.map f).disjUnion (s₂.map f) h' :=
  map_disjUnion _ _ _
#align finset.map_disj_union' Finset.map_disjUnion'

/- warning: finset.map_union -> Finset.map_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : Function.Embedding.{succ u1, succ u2} α β} (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : Function.Embedding.{succ u2, succ u1} α β} (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂))
Case conversion may be inaccurate. Consider using '#align finset.map_union Finset.map_unionₓ'. -/
theorem map_union [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_union, Set.image_union]
#align finset.map_union Finset.map_union

/- warning: finset.map_inter -> Finset.map_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {f : Function.Embedding.{succ u1, succ u2} α β} (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) (Finset.map.{u1, u2} α β f s₁) (Finset.map.{u1, u2} α β f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] {f : Function.Embedding.{succ u2, succ u1} α β} (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) (Finset.map.{u2, u1} α β f s₁) (Finset.map.{u2, u1} α β f s₂))
Case conversion may be inaccurate. Consider using '#align finset.map_inter Finset.map_interₓ'. -/
theorem map_inter [DecidableEq α] [DecidableEq β] {f : α ↪ β} (s₁ s₂ : Finset α) :
    (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
  coe_injective <| by simp only [coe_map, coe_inter, Set.image_inter f.injective]
#align finset.map_inter Finset.map_inter

/- warning: finset.map_singleton -> Finset.map_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (a : α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a)) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (a : α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a)) (Singleton.singleton.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a))
Case conversion may be inaccurate. Consider using '#align finset.map_singleton Finset.map_singletonₓ'. -/
@[simp]
theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
  coe_injective <| by simp only [coe_map, coe_singleton, Set.image_singleton]
#align finset.map_singleton Finset.map_singleton

/- warning: finset.map_insert -> Finset.map_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β) (a : α) (s : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β) (a : α) (s : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Insert.insert.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} β) (Finset.instInsertFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align finset.map_insert Finset.map_insertₓ'. -/
@[simp]
theorem map_insert [DecidableEq α] [DecidableEq β] (f : α ↪ β) (a : α) (s : Finset α) :
    (insert a s).map f = insert (f a) (s.map f) := by
  simp only [insert_eq, map_union, map_singleton]
#align finset.map_insert Finset.map_insert

/- warning: finset.map_cons -> Finset.map_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : Function.Embedding.{succ u1, succ u2} α β) (a : α) (s : Finset.{u1} α) (ha : Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Finset.cons.{u1} α a s ha)) (Finset.cons.{u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s) (Eq.mpr.{0} (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s))) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (id_tag Tactic.IdTag.simp (Eq.{1} Prop (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s))) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))) ((fun (a : Prop) (a_1 : Prop) (e_1 : Eq.{1} Prop a a_1) => congr_arg.{1, 1} Prop Prop a a_1 Not e_1) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Eq.trans.{1} Prop (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a_1 : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a))) ((fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) a) (Eq.trans.{1} Prop (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a_1 : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a)))) (Exists.{succ u1} α (fun (a_1 : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a))) (propext (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.map.{u1, u2} α β f s)) (Exists.{succ u1} α (fun (a_1 : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a)))) (Finset.mem_map.{u1, u2} α β f s (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))) ((fun (p : α -> Prop) (p_1 : α -> Prop) (e_1 : Eq.{succ u1} (α -> Prop) p p_1) => congr_arg.{succ u1, 1} (α -> Prop) Prop p p_1 (Exists.{succ u1} α) e_1) (fun (a_1 : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))) (fun (a_1 : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a)) (funext.{succ u1, 1} α (fun (x : α) => Prop) (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f x) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))) (fun (x : α) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (Eq.{succ u1} α x a)) (fun (a_1 : α) => Eq.trans.{1} Prop (Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))) (Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => (fun (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u1} α a_1 a) (Iff.mpr (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Iff.refl (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s)) h))) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a)) (exists_prop_congr' (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u2} β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a_1) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a)) (fun (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u1} α a_1 a) (fun (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => EmbeddingLike.apply_eq_iff_eq.{max 1 (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.embeddingLike.{succ u1, succ u2} α β) f a_1 a) (Iff.refl (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s))) (propext (Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (fun (h : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) => Eq.{succ u1} α a_1 a)) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a)) (exists_prop (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a_1 s) (Eq.{succ u1} α a_1 a))))))) (propext (Exists.{succ u1} α (fun (a_1 : α) => And ((fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) a_1) (Eq.{succ u1} α a_1 a))) ((fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) a) (exists_eq_right.{succ u1} α (fun (a : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) a))))) (Eq.mp.{0} (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) (rfl.{1} Prop (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))) ha)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : Function.Embedding.{succ u2, succ u1} α β) (a : α) (s : Finset.{u2} α) (ha : Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Finset.cons.{u2} α a s ha)) (Finset.cons.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) f s) (Eq.mpr.{0} (Not (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a)) (Finset.instMembershipFinset.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) f s))) (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) (id.{0} (Eq.{1} Prop (Not (Membership.mem.{u1, u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Finset.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a)) (Finset.instMembershipFinset.{u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) f s))) (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s))) (congrArg.{1, 1} Prop Prop (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s)) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) Not (Eq.trans.{1} Prop (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (a_1 : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a_1 s) (Eq.{succ u2} α a_1 a))) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (Eq.trans.{1} Prop (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Finset.map.{u2, u1} α β f s)) (Exists.{succ u2} α (fun (a_1 : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a_1 s) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a)))) (Exists.{succ u2} α (fun (a_1 : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a_1 s) (Eq.{succ u2} α a_1 a))) (Mathlib.Data.Finset.Image._auxLemma.2.{u2, u1} α β f s (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => β) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a)) (congrArg.{succ u2, 1} (α -> Prop) Prop (fun (x : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a))) (fun (a_1 : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a_1 s) (Eq.{succ u2} α a_1 a)) (Exists.{succ u2} α) (funext.{succ u2, 1} α (fun (x : α) => Prop) (fun (x : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a))) (fun (x : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (Eq.{succ u2} α x a)) (fun (a_1 : α) => congrArg.{1, 1} Prop Prop (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a)) (Eq.{succ u2} α a_1 a) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a_1 s)) (Mathlib.Data.FunLike.Embedding._auxLemma.1.{succ u2, max (succ u2) (succ u1), succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β) f a_1 a))))) (Std.Logic._auxLemma.39.{succ u2} α (fun (a : α) => Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) a)))) ha))
Case conversion may be inaccurate. Consider using '#align finset.map_cons Finset.map_consₓ'. -/
@[simp]
theorem map_cons (f : α ↪ β) (a : α) (s : Finset α) (ha : a ∉ s) :
    (cons a s ha).map f = cons (f a) (s.map f) (by simpa using ha) :=
  eq_of_veq <| Multiset.map_cons f a s.val
#align finset.map_cons Finset.map_cons

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

alias map_nonempty ↔ _ Nonempty.map
#align finset.nonempty.map Finset.Nonempty.map

#print Finset.attach_map_val /-
theorem attach_map_val {s : Finset α} : s.attach.map (Embedding.subtype _) = s :=
  eq_of_veq <| by rw [map_val, attach_val] <;> exact attach_map_val _
#align finset.attach_map_val Finset.attach_map_val
-/

/- warning: finset.disjoint_range_add_left_embedding -> Finset.disjoint_range_addLeftEmbedding is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.orderBot.{0} Nat) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b))
but is expected to have type
  forall (a : Nat) (b : Nat), Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{0} Nat) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_range_add_left_embedding Finset.disjoint_range_addLeftEmbeddingₓ'. -/
theorem disjoint_range_addLeftEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addLeftEmbedding a) (range b)) :=
  by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding_apply, mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_left_embedding Finset.disjoint_range_addLeftEmbedding

/- warning: finset.disjoint_range_add_right_embedding -> Finset.disjoint_range_addRightEmbedding is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.orderBot.{0} Nat) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addRightEmbedding.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) a) (Finset.range b))
but is expected to have type
  forall (a : Nat) (b : Nat), Disjoint.{0} (Finset.{0} Nat) (Finset.partialOrder.{0} Nat) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{0} Nat) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addRightEmbedding.{0} Nat (AddRightCancelMonoid.toAddRightCancelSemigroup.{0} Nat (AddCancelMonoid.toAddRightCancelMonoid.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) a) (Finset.range b))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_range_add_right_embedding Finset.disjoint_range_addRightEmbeddingₓ'. -/
theorem disjoint_range_addRightEmbedding (a b : ℕ) :
    Disjoint (range a) (map (addRightEmbedding a) (range b)) :=
  by
  refine' disjoint_iff_inf_le.mpr _
  intro k hk
  simp only [exists_prop, mem_range, inf_eq_inter, mem_map, addLeftEmbedding_apply, mem_inter] at hk
  obtain ⟨a, haQ, ha⟩ := hk.2
  simpa [← ha] using hk.1
#align finset.disjoint_range_add_right_embedding Finset.disjoint_range_addRightEmbedding

/- warning: finset.map_disj_Union -> Finset.map_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : Function.Embedding.{succ u1, succ u2} α β} {s : Finset.{u1} α} {t : β -> (Finset.{u3} γ)} {h : Set.PairwiseDisjoint.{u3, u2} (Finset.{u3} γ) β (Finset.partialOrder.{u3} γ) (Finset.orderBot.{u3} γ) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) (Finset.map.{u1, u2} α β f s)) t}, Eq.{succ u3} (Finset.{u3} γ) (Finset.disjUnionₓ.{u2, u3} β γ (Finset.map.{u1, u2} α β f s) t h) (Finset.disjUnionₓ.{u1, u3} α γ s (fun (a : α) => t (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a)) (fun (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (hab : Ne.{succ u1} α a b) => h (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Finset.mem_map_of_mem.{u1, u2} α β f a s ha) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f b) (Finset.mem_map_of_mem.{u1, u2} α β f b s hb) (Function.Injective.ne.{succ u1, succ u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) (Function.Embedding.injective.{succ u1, succ u2} α β f) a b hab)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {f : Function.Embedding.{succ u3, succ u2} α β} {s : Finset.{u3} α} {t : β -> (Finset.{u1} γ)} {h : Set.PairwiseDisjoint.{u1, u2} (Finset.{u1} γ) β (Finset.partialOrder.{u1} γ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} γ) (Finset.toSet.{u2} β (Finset.map.{u3, u2} α β f s)) t}, Eq.{succ u1} (Finset.{u1} γ) (Finset.disjUnionᵢ.{u2, u1} β γ (Finset.map.{u3, u2} α β f s) t h) (Finset.disjUnionᵢ.{u3, u1} α γ s (fun (a : α) => t (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f a)) (fun (a : α) (ha : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Finset.toSet.{u3} α s)) (b : α) (hb : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) b (Finset.toSet.{u3} α s)) (hab : Ne.{succ u3} α a b) => h (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f a) (Finset.mem_map_of_mem.{u2, u3} α β f a s ha) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f b) (Finset.mem_map_of_mem.{u2, u3} α β f b s hb) (Function.Injective.ne.{succ u2, succ u3} α β (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} α β)) f) (Function.Embedding.injective.{succ u2, succ u3} α β f) a b hab)))
Case conversion may be inaccurate. Consider using '#align finset.map_disj_Union Finset.map_disjUnionᵢₓ'. -/
theorem map_disjUnionᵢ {f : α ↪ β} {s : Finset α} {t : β → Finset γ} {h} :
    (s.map f).disjUnionₓ t h =
      s.disjUnionₓ (fun a => t (f a)) fun a ha b hb hab =>
        h (mem_map_of_mem _ ha) (mem_map_of_mem _ hb) (f.Injective.Ne hab) :=
  eq_of_veq <| Multiset.bind_map _ _ _
#align finset.map_disj_Union Finset.map_disjUnionᵢ

/- warning: finset.disj_Union_map -> Finset.disjUnionᵢ_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {f : Function.Embedding.{succ u2, succ u3} β γ} {h : Set.PairwiseDisjoint.{u2, u1} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) t}, Eq.{succ u3} (Finset.{u3} γ) (Finset.map.{u2, u3} β γ f (Finset.disjUnionₓ.{u1, u2} α β s t h)) (Finset.disjUnionₓ.{u1, u3} α γ s (fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) (fun (a : α) (ha : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (b : α) (hb : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) (hab : Ne.{succ u1} α a b) => Iff.mpr (Disjoint.{u3} (Finset.{u3} γ) (Finset.partialOrder.{u3} γ) (Finset.orderBot.{u3} γ) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) (forall {{a_1 : γ}}, (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a_1 ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) -> (Not (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) a_1 ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)))) (Finset.disjoint_left.{u3} γ ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) (fun (x : γ) (hxa : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) (hxb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) => Exists.dcases_on.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a_1) x)) (fun (_fresh.650.53762 : Exists.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a_1) x))) => False) (Iff.mp (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x (Finset.map.{u2, u3} β γ f (t a))) (Exists.{succ u2} β (fun (a_1 : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a_1) x))) (Finset.mem_map.{u2, u3} β γ f (t a) x) hxa) (fun (xa : β) (h_1 : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) x)) => Exists.dcases_on.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) x) (fun (h_1 : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) x)) => False) h_1 (fun (hfa : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) (h_1_h : Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) x) => Eq.ndrec.{0, succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) (fun (x : γ) => (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) -> False) (fun (hxa : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) (hxb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) => Exists.dcases_on.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa))) (fun (_fresh.650.53848 : Exists.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)))) => False) (Iff.mp (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) (Finset.map.{u2, u3} β γ f (t b))) (Exists.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f a) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)))) (Finset.mem_map.{u2, u3} β γ f (t b) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)) hxb) (fun (xb : β) (h_1 : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa))) => Exists.dcases_on.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)) (fun (h_1 : Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) => Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa))) => False) h_1 (fun (hfb : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t b)) (hfab : Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)) => Eq.ndrec.{0, succ u2} β xb (fun (xa : β) => (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xa (t a)) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) -> (Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xa)) -> False) (fun (hfa : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) xb (t a)) (hxa : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) a)) (hxb : Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) ((fun (a : α) => Finset.map.{u2, u3} β γ f (t a)) b)) (hfab : Eq.{succ u3} γ (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} β γ) (fun (_x : Function.Embedding.{succ u2, succ u3} β γ) => β -> γ) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} β γ) f xb)) => Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (t a) (t b)) (forall {{a_1 : β}}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t a)) -> (Not (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) a_1 (t b)))) (Finset.disjoint_left.{u2} β (t a) (t b)) (h a ha b hb hab) xb hfa hfb) xa (Function.Embedding.injective.{succ u2, succ u3} β γ f xb xa hfab) hfa hxa hxb hfab))) x h_1_h hxa hxb)))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Finset.{u3} α} {t : α -> (Finset.{u2} β)} {f : Function.Embedding.{succ u2, succ u1} β γ} {h : Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} β) α (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (Finset.toSet.{u3} α s) t}, Eq.{succ u1} (Finset.{u1} γ) (Finset.map.{u2, u1} β γ f (Finset.disjUnionᵢ.{u3, u2} α β s t h)) (Finset.disjUnionᵢ.{u3, u1} α γ s (fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) (fun (a : α) (ha : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a (Finset.toSet.{u3} α s)) (b : α) (hb : Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) b (Finset.toSet.{u3} α s)) (hab : Ne.{succ u3} α a b) => Iff.mpr (Disjoint.{u1} (Finset.{u1} γ) (Finset.partialOrder.{u1} γ) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} γ) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) (forall {{a_1 : γ}}, (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a_1 ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) -> (Not (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) a_1 ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)))) (Finset.disjoint_left.{u1} γ ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) (fun (x : γ) (hxa : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) (hxb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) => Exists.casesOn.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a_1) x)) (fun (_fresh.650.53762 : Exists.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a_1) x))) => False) (Iff.mp (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x (Finset.map.{u2, u1} β γ f (t a))) (Exists.{succ u2} β (fun (a_1 : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a_1) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a_1) x))) (Finset.mem_map.{u2, u1} β γ f (t a) x) hxa) (fun (xa : β) (h_1 : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xa) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) x)) => And.casesOn.{0} (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xa) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) x) (fun (h_1 : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (t a)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xa) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) x)) => False) h_1 (fun (hfa : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (t a)) (h_1_h : Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xa) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) x) => Eq.ndrec.{0, succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xa) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) (fun (x : γ) => (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) -> (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) x ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) -> False) (fun (hxa : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) (hxb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) => Exists.casesOn.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa))) (fun (_fresh.650.53848 : Exists.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)))) => False) (Iff.mp (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) (Finset.map.{u2, u1} β γ f (t b))) (Exists.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)))) (Finset.mem_map.{u2, u1} β γ f (t b) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)) hxb) (fun (xb : β) (h_1 : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa))) => And.casesOn.{0} (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)) (fun (h_1 : And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (t b)) (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa))) => False) h_1 (fun (hfb : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (t b)) (hfab : Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)) => Eq.ndrec.{0, succ u2} β xb (fun (xa : β) => (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xa (t a)) -> (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) -> (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) -> (Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xa)) -> False) (fun (hfa : Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) xb (t a)) (hxa : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) a)) (hxb : Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) ((fun (a : α) => Finset.map.{u2, u1} β γ f (t a)) b)) (hfab : Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} β γ) β γ (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} β γ)) f xb)) => Iff.mp (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) (t a) (t b)) (forall {{a_1 : β}}, (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (t a)) -> (Not (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) a_1 (t b)))) (Finset.disjoint_left.{u2} β (t a) (t b)) (h a ha b hb hab) xb hfa hfb) xa (Function.Embedding.injective.{succ u1, succ u2} β γ f xb xa hfab) hfa hxa hxb hfab))) x h_1_h hxa hxb)))))
Case conversion may be inaccurate. Consider using '#align finset.disj_Union_map Finset.disjUnionᵢ_mapₓ'. -/
theorem disjUnionᵢ_map {s : Finset α} {t : α → Finset β} {f : β ↪ γ} {h} :
    (s.disjUnionₓ t h).map f =
      s.disjUnionₓ (fun a => (t a).map f) fun a ha b hb hab =>
        disjoint_left.mpr fun x hxa hxb =>
          by
          obtain ⟨xa, hfa, rfl⟩ := mem_map.mp hxa
          obtain ⟨xb, hfb, hfab⟩ := mem_map.mp hxb
          obtain rfl := f.injective hfab
          exact disjoint_left.mp (h ha hb hab) hfa hfb :=
  eq_of_veq <| Multiset.map_bind _ _ _
#align finset.disj_Union_map Finset.disjUnionᵢ_map

end Map

/- warning: finset.range_add_one' -> Finset.range_add_one' is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.hasInsert.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))) (Finset.map.{0, 0} Nat Nat (Function.Embedding.mk.{1, 1} Nat Nat (fun (i : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) i (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (fun (i : Nat) (j : Nat) => Nat.succ.inj i j)) (Finset.range n)))
but is expected to have type
  forall (n : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Insert.insert.{0, 0} Nat (Finset.{0} Nat) (Finset.instInsertFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)) (Finset.map.{0, 0} Nat Nat (Function.Embedding.mk.{1, 1} Nat Nat (fun (i : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (fun (i : Nat) (j : Nat) => of_eq_true ((Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) j (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Eq.{1} Nat i j)) (Eq.trans.{1} Prop ((Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) j (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Eq.{1} Nat i j)) ((Eq.{1} Nat i j) -> (Eq.{1} Nat i j)) True (implies_congr.{0, 0} (Eq.{1} Nat (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) i (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) j (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Eq.{1} Nat i j) (Eq.{1} Nat i j) (Eq.{1} Nat i j) (Mathlib.Algebra.Group.Defs._auxLemma.4.{0} Nat instAddNat (IsCancelAdd.toIsRightCancelAdd.{0} Nat instAddNat (AddCancelMonoid.toIsCancelAdd.{0} Nat (AddCancelCommMonoid.toAddCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)) i j) (Eq.refl.{1} Prop (Eq.{1} Nat i j))) (Std.Logic._auxLemma.6 (Eq.{1} Nat i j))))) (Finset.range n)))
Case conversion may be inaccurate. Consider using '#align finset.range_add_one' Finset.range_add_one'ₓ'. -/
theorem range_add_one' (n : ℕ) :
    range (n + 1) = insert 0 ((range n).map ⟨fun i => i + 1, fun i j => Nat.succ.inj⟩) := by
  ext (⟨⟩ | ⟨n⟩) <;> simp [Nat.succ_eq_add_one, Nat.zero_lt_succ n]
#align finset.range_add_one' Finset.range_add_one'

/-! ### image -/


section Image

variable [DecidableEq β]

#print Finset.image /-
/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : Finset α) : Finset β :=
  (s.1.map f).toFinset
#align finset.image Finset.image
-/

/- warning: finset.image_val -> Finset.image_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (f : α -> β) (s : Finset.{u1} α), Eq.{succ u2} (Multiset.{u2} β) (Finset.val.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Multiset.dedup.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.map.{u1, u2} α β f (Finset.val.{u1} α s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (f : α -> β) (s : Finset.{u2} α), Eq.{succ u1} (Multiset.{u1} β) (Finset.val.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Multiset.dedup.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.map.{u2, u1} α β f (Finset.val.{u2} α s)))
Case conversion may be inaccurate. Consider using '#align finset.image_val Finset.image_valₓ'. -/
@[simp]
theorem image_val (f : α → β) (s : Finset α) : (image f s).1 = (s.1.map f).dedup :=
  rfl
#align finset.image_val Finset.image_val

#print Finset.image_empty /-
@[simp]
theorem image_empty (f : α → β) : (∅ : Finset α).image f = ∅ :=
  rfl
#align finset.image_empty Finset.image_empty
-/

variable {f g : α → β} {s : Finset α} {t : Finset β} {a : α} {b c : β}

/- warning: finset.mem_image -> Finset.mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {b : β}, Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) => Eq.{succ u2} β (f a) b)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {b : β}, Iff (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) (Eq.{succ u2} β (f a) b)))
Case conversion may be inaccurate. Consider using '#align finset.mem_image Finset.mem_imageₓ'. -/
@[simp]
theorem mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b := by
  simp only [mem_def, image_val, mem_dedup, Multiset.mem_map, exists_prop]
#align finset.mem_image Finset.mem_image

/- warning: finset.mem_image_of_mem -> Finset.mem_image_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} (f : α -> β) {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f a) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} (f : α -> β) {a : α}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f a) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.mem_image_of_mem Finset.mem_image_of_memₓ'. -/
theorem mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f :=
  mem_image.2 ⟨_, h, rfl⟩
#align finset.mem_image_of_mem Finset.mem_image_of_mem

#print Finset.forall_image /-
theorem forall_image {p : β → Prop} : (∀ b ∈ s.image f, p b) ↔ ∀ a ∈ s, p (f a) := by
  simp only [mem_image, forall_exists_index, forall_apply_eq_imp_iff₂]
#align finset.forall_image Finset.forall_image
-/

#print Finset.mem_image_const /-
@[simp]
theorem mem_image_const : c ∈ s.image (const α b) ↔ s.Nonempty ∧ b = c :=
  by
  rw [mem_image]
  simp only [exists_prop, const_apply, exists_and_right]
  rfl
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

/- warning: finset.image_congr -> Finset.image_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {g : α -> β} {s : Finset.{u1} α}, (Set.EqOn.{u1, u2} α β f g ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {g : α -> β} {s : Finset.{u2} α}, (Set.EqOn.{u2, u1} α β f g (Finset.toSet.{u2} α s)) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) g s))
Case conversion may be inaccurate. Consider using '#align finset.image_congr Finset.image_congrₓ'. -/
theorem image_congr (h : (s : Set α).EqOn f g) : Finset.image f s = Finset.image g s :=
  by
  ext
  simp_rw [mem_image]
  exact bex_congr fun x hx => by rw [h hx]
#align finset.image_congr Finset.image_congr

/- warning: function.injective.mem_finset_image -> Function.Injective.mem_finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {a : α}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f a) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s : Finset.{u2} α} {a : α}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f a) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s))
Case conversion may be inaccurate. Consider using '#align function.injective.mem_finset_image Function.Injective.mem_finset_imageₓ'. -/
theorem Function.Injective.mem_finset_image (hf : Injective f) : f a ∈ s.image f ↔ a ∈ s :=
  by
  refine' ⟨fun h => _, Finset.mem_image_of_mem f⟩
  obtain ⟨y, hy, heq⟩ := mem_image.1 h
  exact hf HEq ▸ hy
#align function.injective.mem_finset_image Function.Injective.mem_finset_image

/- warning: finset.filter_mem_image_eq_image -> Finset.filter_mem_image_eq_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (f : α -> β) (s : Finset.{u1} α) (t : Finset.{u2} β), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (f x) t)) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.filter.{u2} β (fun (y : β) => Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (fun (a : β) => Finset.decidableMem.{u2} β (fun (a : β) (b : β) => _inst_1 a b) a (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) t) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (f : α -> β) (s : Finset.{u2} α) (t : Finset.{u1} β), (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (f x) t)) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.filter.{u1} β (fun (y : β) => Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (fun (a : β) => Finset.decidableMem.{u1} β (fun (a : β) (b : β) => _inst_1 a b) a (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) t) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.filter_mem_image_eq_image Finset.filter_mem_image_eq_imageₓ'. -/
theorem filter_mem_image_eq_image (f : α → β) (s : Finset α) (t : Finset β) (h : ∀ x ∈ s, f x ∈ t) :
    (t.filterₓ fun y => y ∈ s.image f) = s.image f :=
  by
  ext
  rw [mem_filter, mem_image]
  simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp]
  rintro x xel rfl
  exact h _ xel
#align finset.filter_mem_image_eq_image Finset.filter_mem_image_eq_image

/- warning: finset.fiber_nonempty_iff_mem_image -> Finset.fiber_nonempty_iff_mem_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (f : α -> β) (s : Finset.{u1} α) (y : β), Iff (Finset.Nonempty.{u1} α (Finset.filter.{u1} α (fun (x : α) => Eq.{succ u2} β (f x) y) (fun (a : α) => _inst_1 (f a) y) s)) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (f : α -> β) (s : Finset.{u2} α) (y : β), Iff (Finset.Nonempty.{u2} α (Finset.filter.{u2} α (fun (x : α) => Eq.{succ u1} β (f x) y) (fun (a : α) => _inst_1 (f a) y) s)) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.fiber_nonempty_iff_mem_image Finset.fiber_nonempty_iff_mem_imageₓ'. -/
theorem fiber_nonempty_iff_mem_image (f : α → β) (s : Finset α) (y : β) :
    (s.filterₓ fun x => f x = y).Nonempty ↔ y ∈ s.image f := by simp [Finset.Nonempty]
#align finset.fiber_nonempty_iff_mem_image Finset.fiber_nonempty_iff_mem_image

#print Finset.coe_image /-
@[simp, norm_cast]
theorem coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
  Set.ext fun _ => mem_image.trans Set.mem_image_iff_bex.symm
#align finset.coe_image Finset.coe_image
-/

/- warning: finset.nonempty.image -> Finset.Nonempty.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (f : α -> β), Finset.Nonempty.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α}, (Finset.Nonempty.{u2} α s) -> (forall (f : α -> β), Finset.Nonempty.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.image Finset.Nonempty.imageₓ'. -/
protected theorem Nonempty.image (h : s.Nonempty) (f : α → β) : (s.image f).Nonempty :=
  let ⟨a, ha⟩ := h
  ⟨f a, mem_image_of_mem f ha⟩
#align finset.nonempty.image Finset.Nonempty.image

#print Finset.Nonempty.image_iff /-
@[simp]
theorem Nonempty.image_iff (f : α → β) : (s.image f).Nonempty ↔ s.Nonempty :=
  ⟨fun ⟨y, hy⟩ =>
    let ⟨x, hx, _⟩ := mem_image.mp hy
    ⟨x, hx⟩,
    fun h => h.image f⟩
#align finset.nonempty.image_iff Finset.Nonempty.image_iff
-/

/- warning: finset.image_to_finset -> Finset.image_toFinset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u1} α] {s : Multiset.{u1} α}, Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s)) (Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.map.{u1, u2} α β f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u2} α] {s : Multiset.{u2} α}, Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Multiset.toFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s)) (Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Multiset.map.{u2, u1} α β f s))
Case conversion may be inaccurate. Consider using '#align finset.image_to_finset Finset.image_toFinsetₓ'. -/
theorem image_toFinset [DecidableEq α] {s : Multiset α} : s.toFinset.image f = (s.map f).toFinset :=
  ext fun _ => by simp only [mem_image, Multiset.mem_toFinset, exists_prop, Multiset.mem_map]
#align finset.image_to_finset Finset.image_toFinset

/- warning: finset.image_val_of_inj_on -> Finset.image_val_of_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α}, (Set.InjOn.{u1, u2} α β f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) -> (Eq.{succ u2} (Multiset.{u2} β) (Finset.val.{u2} β (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Multiset.map.{u1, u2} α β f (Finset.val.{u1} α s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s : Finset.{u2} α}, (Set.InjOn.{u2, u1} α β f (Finset.toSet.{u2} α s)) -> (Eq.{succ u1} (Multiset.{u1} β) (Finset.val.{u1} β (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s)) (Multiset.map.{u2, u1} α β f (Finset.val.{u2} α s)))
Case conversion may be inaccurate. Consider using '#align finset.image_val_of_inj_on Finset.image_val_of_injOnₓ'. -/
theorem image_val_of_injOn (H : Set.InjOn f s) : (image f s).1 = s.1.map f :=
  (s.2.map_onₓ H).dedup
#align finset.image_val_of_inj_on Finset.image_val_of_injOn

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

/- warning: function.semiconj.finset_image -> Function.Semiconj.finset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β} {ga : α -> α} {gb : β -> β}, (Function.Semiconj.{u1, u2} α β f ga gb) -> (Function.Semiconj.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f) (Finset.image.{u1, u1} α α (fun (a : α) (b : α) => _inst_2 a b) ga) (Finset.image.{u2, u2} β β (fun (a : β) (b : β) => _inst_1 a b) gb))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β} {ga : α -> α} {gb : β -> β}, (Function.Semiconj.{u2, u1} α β f ga gb) -> (Function.Semiconj.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f) (Finset.image.{u2, u2} α α (fun (a : α) (b : α) => _inst_2 a b) ga) (Finset.image.{u1, u1} β β (fun (a : β) (b : β) => _inst_1 a b) gb))
Case conversion may be inaccurate. Consider using '#align function.semiconj.finset_image Function.Semiconj.finset_imageₓ'. -/
theorem Function.Semiconj.finset_image [DecidableEq α] {f : α → β} {ga : α → α} {gb : β → β}
    (h : Function.Semiconj f ga gb) : Function.Semiconj (image f) (image ga) (image gb) := fun s =>
  image_comm h
#align function.semiconj.finset_image Function.Semiconj.finset_image

#print Function.Commute.finset_image /-
theorem Function.Commute.finset_image [DecidableEq α] {f g : α → α} (h : Function.Commute f g) :
    Function.Commute (image f) (image g) :=
  h.finset_image
#align function.commute.finset_image Function.Commute.finset_image
-/

/- warning: finset.image_subset_image -> Finset.image_subset_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_image Finset.image_subset_imageₓ'. -/
theorem image_subset_image {s₁ s₂ : Finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f := by
  simp only [subset_def, image_val, subset_dedup', dedup_subset', Multiset.map_subset_map h]
#align finset.image_subset_image Finset.image_subset_image

#print Finset.image_subset_iff /-
theorem image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
  calc
    s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t := by norm_cast
    _ ↔ _ := Set.image_subset_iff
    
#align finset.image_subset_iff Finset.image_subset_iff
-/

/- warning: finset.image_mono -> Finset.image_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (f : α -> β), Monotone.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (f : α -> β), Monotone.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f)
Case conversion may be inaccurate. Consider using '#align finset.image_mono Finset.image_monoₓ'. -/
theorem image_mono (f : α → β) : Monotone (Finset.image f) := fun _ _ => image_subset_image
#align finset.image_mono Finset.image_mono

/- warning: finset.image_subset_image_iff -> Finset.image_subset_image_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} {s : Finset.{u1} α} {t : Finset.{u1} α}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} {s : Finset.{u2} α} {t : Finset.{u2} α}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_image_iff Finset.image_subset_image_iffₓ'. -/
theorem image_subset_image_iff {t : Finset α} (hf : Injective f) : s.image f ⊆ t.image f ↔ s ⊆ t :=
  by
  simp_rw [← coe_subset]
  push_cast
  exact Set.image_subset_image_iff hf
#align finset.image_subset_image_iff Finset.image_subset_image_iff

#print Finset.coe_image_subset_range /-
theorem coe_image_subset_range : ↑(s.image f) ⊆ Set.range f :=
  calc
    ↑(s.image f) = f '' ↑s := coe_image
    _ ⊆ Set.range f := Set.image_subset_range f ↑s
    
#align finset.coe_image_subset_range Finset.coe_image_subset_range
-/

#print Finset.image_filter /-
theorem image_filter {p : β → Prop} [DecidablePred p] :
    (s.image f).filterₓ p = (s.filterₓ (p ∘ f)).image f :=
  ext fun b => by
    simp only [mem_filter, mem_image, exists_prop] <;>
      exact
        ⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩ <;> exact ⟨x, ⟨h1, h2⟩, rfl⟩, by
          rintro ⟨x, ⟨h1, h2⟩, rfl⟩ <;> exact ⟨⟨x, h1, rfl⟩, h2⟩⟩
#align finset.image_filter Finset.image_filter
-/

/- warning: finset.image_union -> Finset.image_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β} (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂)) (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β} (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂)) (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂))
Case conversion may be inaccurate. Consider using '#align finset.image_union Finset.image_unionₓ'. -/
theorem image_union [DecidableEq α] {f : α → β} (s₁ s₂ : Finset α) :
    (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
  ext fun _ => by simp only [mem_image, mem_union, exists_prop, or_and_right, exists_or]
#align finset.image_union Finset.image_union

/- warning: finset.image_inter_subset -> Finset.image_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (f : α -> β) (s : Finset.{u1} α) (t : Finset.{u1} α), HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (f : α -> β) (s : Finset.{u2} α) (t : Finset.{u2} α), HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f t))
Case conversion may be inaccurate. Consider using '#align finset.image_inter_subset Finset.image_inter_subsetₓ'. -/
theorem image_inter_subset [DecidableEq α] (f : α → β) (s t : Finset α) :
    (s ∩ t).image f ⊆ s.image f ∩ t.image f :=
  subset_inter (image_subset_image <| inter_subset_left _ _) <|
    image_subset_image <| inter_subset_right _ _
#align finset.image_inter_subset Finset.image_inter_subset

/- warning: finset.image_inter_of_inj_on -> Finset.image_inter_of_injOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β} (s : Finset.{u1} α) (t : Finset.{u1} α), (Set.InjOn.{u1, u2} α β f (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) t))) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β} (s : Finset.{u2} α) (t : Finset.{u2} α), (Set.InjOn.{u2, u1} α β f (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (Finset.toSet.{u2} α s) (Finset.toSet.{u2} α t))) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f t)))
Case conversion may be inaccurate. Consider using '#align finset.image_inter_of_inj_on Finset.image_inter_of_injOnₓ'. -/
theorem image_inter_of_injOn [DecidableEq α] {f : α → β} (s t : Finset α)
    (hf : Set.InjOn f (s ∪ t)) : (s ∩ t).image f = s.image f ∩ t.image f :=
  (image_inter_subset _ _ _).antisymm fun x =>
    by
    simp only [mem_inter, mem_image]
    rintro ⟨⟨a, ha, rfl⟩, b, hb, h⟩
    exact ⟨a, ⟨ha, by rwa [← hf (Or.inr hb) (Or.inl ha) h]⟩, rfl⟩
#align finset.image_inter_of_inj_on Finset.image_inter_of_injOn

/- warning: finset.image_inter -> Finset.image_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), (Function.Injective.{succ u1, succ u2} α β f) -> (Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂)) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {f : α -> β} [_inst_2 : DecidableEq.{succ u2} α] (s₁ : Finset.{u2} α) (s₂ : Finset.{u2} α), (Function.Injective.{succ u2, succ u1} α β f) -> (Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) s₁ s₂)) (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₁) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s₂)))
Case conversion may be inaccurate. Consider using '#align finset.image_inter Finset.image_interₓ'. -/
theorem image_inter [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective f) :
    (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
  image_inter_of_injOn _ _ <| hf.InjOn _
#align finset.image_inter Finset.image_inter

#print Finset.image_singleton /-
@[simp]
theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
  ext fun x => by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm
#align finset.image_singleton Finset.image_singleton
-/

/- warning: finset.image_insert -> Finset.image_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (f : α -> β) (a : α) (s : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Insert.insert.{u2, u2} β (Finset.{u2} β) (Finset.hasInsert.{u2} β (fun (a : β) (b : β) => _inst_1 a b)) (f a) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (f : α -> β) (a : α) (s : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Insert.insert.{u1, u1} β (Finset.{u1} β) (Finset.instInsertFinset.{u1} β (fun (a : β) (b : β) => _inst_1 a b)) (f a) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s))
Case conversion may be inaccurate. Consider using '#align finset.image_insert Finset.image_insertₓ'. -/
@[simp]
theorem image_insert [DecidableEq α] (f : α → β) (a : α) (s : Finset α) :
    (insert a s).image f = insert (f a) (s.image f) := by
  simp only [insert_eq, image_singleton, image_union]
#align finset.image_insert Finset.image_insert

/- warning: finset.erase_image_subset_image_erase -> Finset.erase_image_subset_image_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (f : α -> β) (s : Finset.{u1} α) (a : α), HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) (Finset.erase.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (f a)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (f : α -> β) (s : Finset.{u2} α) (a : α), HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) (Finset.erase.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (f a)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a))
Case conversion may be inaccurate. Consider using '#align finset.erase_image_subset_image_erase Finset.erase_image_subset_image_eraseₓ'. -/
theorem erase_image_subset_image_erase [DecidableEq α] (f : α → β) (s : Finset α) (a : α) :
    (s.image f).eraseₓ (f a) ⊆ (s.eraseₓ a).image f :=
  by
  simp only [subset_iff, and_imp, exists_prop, mem_image, exists_imp, mem_erase]
  rintro b hb x hx rfl
  exact ⟨_, ⟨ne_of_apply_ne f hb, hx⟩, rfl⟩
#align finset.erase_image_subset_image_erase Finset.erase_image_subset_image_erase

/- warning: finset.image_erase -> Finset.image_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (forall (s : Finset.{u1} α) (a : α), Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Finset.erase.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (forall (s : Finset.{u2} α) (a : α), Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Finset.erase.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (f a)))
Case conversion may be inaccurate. Consider using '#align finset.image_erase Finset.image_eraseₓ'. -/
@[simp]
theorem image_erase [DecidableEq α] {f : α → β} (hf : Injective f) (s : Finset α) (a : α) :
    (s.eraseₓ a).image f = (s.image f).eraseₓ (f a) :=
  by
  refine' (erase_image_subset_image_erase _ _ _).antisymm' fun b => _
  simp only [mem_image, exists_prop, mem_erase]
  rintro ⟨a', ⟨haa', ha'⟩, rfl⟩
  exact ⟨hf.ne haa', a', ha', rfl⟩
#align finset.image_erase Finset.image_erase

#print Finset.image_eq_empty /-
@[simp]
theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
  ⟨fun h => eq_empty_of_forall_not_mem fun a m => ne_empty_of_mem (mem_image_of_mem _ m) h, fun e =>
    e.symm ▸ rfl⟩
#align finset.image_eq_empty Finset.image_eq_empty
-/

/- warning: disjoint.of_image_finset -> Disjoint.of_image_finset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : Finset.{u1} α} {f : α -> β}, (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) -> (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : Finset.{u2} α} {f : α -> β}, (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) -> (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s t)
Case conversion may be inaccurate. Consider using '#align disjoint.of_image_finset Disjoint.of_image_finsetₓ'. -/
@[simp]
theorem Disjoint.of_image_finset {s t : Finset α} {f : α → β}
    (h : Disjoint (s.image f) (t.image f)) : Disjoint s t :=
  disjoint_iff_ne.2 fun a ha b hb =>
    ne_of_apply_ne f <| h.forall_ne_finset (mem_image_of_mem _ ha) (mem_image_of_mem _ hb)
#align disjoint.of_image_finset Disjoint.of_image_finset

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

/- warning: finset.range_add -> Finset.range_add is a dubious translation:
lean 3 declaration is
  forall (a : Nat) (b : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) a b)) (Union.union.{0} (Finset.{0} Nat) (Finset.hasUnion.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b)))
but is expected to have type
  forall (a : Nat) (b : Nat), Eq.{1} (Finset.{0} Nat) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) a b)) (Union.union.{0} (Finset.{0} Nat) (Finset.instUnionFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (Finset.range a) (Finset.map.{0, 0} Nat Nat (addLeftEmbedding.{0} Nat (AddLeftCancelMonoid.toAddLeftCancelSemigroup.{0} Nat (AddCancelCommMonoid.toAddLeftCancelMonoid.{0} Nat (OrderedCancelAddCommMonoid.toCancelAddCommMonoid.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) a) (Finset.range b)))
Case conversion may be inaccurate. Consider using '#align finset.range_add Finset.range_addₓ'. -/
theorem range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (addLeftEmbedding a) :=
  by
  rw [← val_inj, union_val]
  exact Multiset.range_add_eq_union a b
#align finset.range_add Finset.range_add

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

/- warning: finset.attach_insert -> Finset.attach_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)))) (Finset.attach.{u1} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Insert.insert.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)))) (Finset.hasInsert.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (fun (a_1 : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (b : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) => Subtype.decidableEq.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (a : α) (b : α) => _inst_2 a b) a_1 b)) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) a (Finset.mem_insert_self.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s)) (Finset.image.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (fun (a_1 : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (b : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) => Subtype.decidableEq.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (a : α) (b : α) => _inst_2 a b) a_1 b) (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s)) => Subtype.mk.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x) (Finset.mem_insert_of_mem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x) a (Subtype.property.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) x))) (Finset.attach.{u1} α s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : DecidableEq.{succ u1} α] {a : α} {s : Finset.{u1} α}, Eq.{succ u1} (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)))) (Finset.attach.{u1} α (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Insert.insert.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (Finset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)))) (Finset.instInsertFinset.{u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (fun (a_1 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (b : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (a : α) (b : α) => _inst_2 a b) a_1 b)) (Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) a (Finset.mem_insert_self.{u1} α (fun (a : α) (b : α) => _inst_2 a b) a s)) (Finset.image.{u1, u1} (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) (Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (fun (a_1 : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) (b : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s))) => Subtype.instDecidableEqSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (fun (a : α) (b : α) => _inst_2 a b) a_1 b) (fun (x : Subtype.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s)) => Subtype.mk.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_2 a b)) a s)) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) x) (Finset.mem_insert_of_mem.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) x) a (Subtype.property.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) x))) (Finset.attach.{u1} α s)))
Case conversion may be inaccurate. Consider using '#align finset.attach_insert Finset.attach_insertₓ'. -/
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

/- warning: finset.map_eq_image -> Finset.map_eq_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) s)
Case conversion may be inaccurate. Consider using '#align finset.map_eq_image Finset.map_eq_imageₓ'. -/
theorem map_eq_image (f : α ↪ β) (s : Finset α) : s.map f = s.image f :=
  eq_of_veq (s.map f).2.dedup.symm
#align finset.map_eq_image Finset.map_eq_image

/- warning: finset.disjoint_image -> Finset.disjoint_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α} {t : Finset.{u1} α} {f : α -> β}, (Function.Injective.{succ u1, succ u2} α β f) -> (Iff (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α} {t : Finset.{u2} α} {f : α -> β}, (Function.Injective.{succ u2, succ u1} α β f) -> (Iff (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f t)) (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s t))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_image Finset.disjoint_imageₓ'. -/
@[simp]
theorem disjoint_image {s t : Finset α} {f : α → β} (hf : Injective f) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t := by
  convert disjoint_map ⟨_, hf⟩ <;> simp [map_eq_image]
#align finset.disjoint_image Finset.disjoint_image

/- warning: finset.image_const -> Finset.image_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (b : β), Eq.{succ u2} (Finset.{u2} β) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (fun (a : α) => b) s) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] {s : Finset.{u2} α}, (Finset.Nonempty.{u2} α s) -> (forall (b : β), Eq.{succ u1} (Finset.{u1} β) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (fun (a : α) => b) s) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b))
Case conversion may be inaccurate. Consider using '#align finset.image_const Finset.image_constₓ'. -/
theorem image_const {s : Finset α} (h : s.Nonempty) (b : β) : (s.image fun a => b) = singleton b :=
  ext fun b' => by
    simp only [mem_image, exists_prop, exists_and_right, h.bex, true_and_iff, mem_singleton,
      eq_comm]
#align finset.image_const Finset.image_const

/- warning: finset.map_erase -> Finset.map_erase is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (f : Function.Embedding.{succ u1, succ u2} α β) (s : Finset.{u1} α) (a : α), Eq.{succ u2} (Finset.{u2} β) (Finset.map.{u1, u2} α β f (Finset.erase.{u1} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Finset.erase.{u2} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.map.{u1, u2} α β f s) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (f : Function.Embedding.{succ u2, succ u1} α β) (s : Finset.{u2} α) (a : α), Eq.{succ u1} (Finset.{u1} β) (Finset.map.{u2, u1} α β f (Finset.erase.{u2} α (fun (a : α) (b : α) => _inst_2 a b) s a)) (Finset.erase.{u1} β (fun (a : β) (b : β) => _inst_1 a b) (Finset.map.{u2, u1} α β f s) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a))
Case conversion may be inaccurate. Consider using '#align finset.map_erase Finset.map_eraseₓ'. -/
@[simp]
theorem map_erase [DecidableEq α] (f : α ↪ β) (s : Finset α) (a : α) :
    (s.eraseₓ a).map f = (s.map f).eraseₓ (f a) :=
  by
  simp_rw [map_eq_image]
  exact s.image_erase f.2 a
#align finset.map_erase Finset.map_erase

/- warning: finset.image_bUnion -> Finset.image_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u3} γ] {f : α -> β} {s : Finset.{u1} α} {t : β -> (Finset.{u3} γ)}, Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) f s) t) (Finset.bunionᵢ.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => t (f a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u3} γ] {f : α -> β} {s : Finset.{u2} α} {t : β -> (Finset.{u3} γ)}, Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) f s) t) (Finset.bunionᵢ.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => t (f a)))
Case conversion may be inaccurate. Consider using '#align finset.image_bUnion Finset.image_bunionᵢₓ'. -/
theorem image_bunionᵢ [DecidableEq γ] {f : α → β} {s : Finset α} {t : β → Finset γ} :
    (s.image f).bunionᵢ t = s.bunionᵢ fun a => t (f a) :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by simp only [image_insert, bUnion_insert, ih]
#align finset.image_bUnion Finset.image_bunionᵢ

/- warning: finset.bUnion_image -> Finset.bunionᵢ_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u3} γ] {s : Finset.{u1} α} {t : α -> (Finset.{u2} β)} {f : β -> γ}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) f (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Finset.bunionᵢ.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) f (t a)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u3} γ] {s : Finset.{u2} α} {t : α -> (Finset.{u1} β)} {f : β -> γ}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) f (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) s t)) (Finset.bunionᵢ.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_2 a b) s (fun (a : α) => Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_2 a b) f (t a)))
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image Finset.bunionᵢ_imageₓ'. -/
theorem bunionᵢ_image [DecidableEq γ] {s : Finset α} {t : α → Finset β} {f : β → γ} :
    (s.bunionᵢ t).image f = s.bunionᵢ fun a => (t a).image f :=
  haveI := Classical.decEq α
  Finset.induction_on s rfl fun a s has ih => by simp only [bUnion_insert, image_union, ih]
#align finset.bUnion_image Finset.bunionᵢ_image

/- warning: finset.image_bUnion_filter_eq -> Finset.image_bunionᵢ_filter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u2} β] [_inst_2 : DecidableEq.{succ u1} α] (s : Finset.{u2} β) (g : β -> α), Eq.{succ u2} (Finset.{u2} β) (Finset.bunionᵢ.{u1, u2} α β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u2, u1} β α (fun (a : α) (b : α) => _inst_2 a b) g s) (fun (a : α) => Finset.filter.{u2} β (fun (c : β) => Eq.{succ u1} α (g c) a) (fun (a_1 : β) => _inst_2 (g a_1) a) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} β] [_inst_2 : DecidableEq.{succ u2} α] (s : Finset.{u1} β) (g : β -> α), Eq.{succ u1} (Finset.{u1} β) (Finset.bunionᵢ.{u2, u1} α β (fun (a : β) (b : β) => _inst_1 a b) (Finset.image.{u1, u2} β α (fun (a : α) (b : α) => _inst_2 a b) g s) (fun (a : α) => Finset.filter.{u1} β (fun (c : β) => Eq.{succ u2} α (g c) a) (fun (a_1 : β) => _inst_2 (g a_1) a) s)) s
Case conversion may be inaccurate. Consider using '#align finset.image_bUnion_filter_eq Finset.image_bunionᵢ_filter_eqₓ'. -/
theorem image_bunionᵢ_filter_eq [DecidableEq α] (s : Finset β) (g : β → α) :
    ((s.image g).bunionᵢ fun a => s.filterₓ fun c => g c = a) = s :=
  bunionᵢ_filter_eq_of_maps_to fun x => mem_image_of_mem g
#align finset.image_bUnion_filter_eq Finset.image_bunionᵢ_filter_eq

#print Finset.bunionᵢ_singleton /-
theorem bunionᵢ_singleton {f : α → β} : (s.bunionᵢ fun a => {f a}) = s.image f :=
  ext fun x => by simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]
#align finset.bUnion_singleton Finset.bunionᵢ_singleton
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

/- warning: finset.fin_map -> Finset.fin_map is a dubious translation:
lean 3 declaration is
  forall {n : Nat} {s : Finset.{0} Nat}, Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.fin n s)) (Finset.filter.{0} Nat (fun (_x : Nat) => LT.lt.{0} Nat Nat.hasLt _x n) (fun (a : Nat) => Nat.decidableLt a n) s)
but is expected to have type
  forall {n : Nat} {s : Finset.{0} Nat}, Eq.{1} (Finset.{0} Nat) (Finset.map.{0, 0} (Fin n) Nat (Fin.valEmbedding n) (Finset.fin n s)) (Finset.filter.{0} Nat (fun (_x : Nat) => LT.lt.{0} Nat instLTNat _x n) (fun (a : Nat) => Nat.decLt a n) s)
Case conversion may be inaccurate. Consider using '#align finset.fin_map Finset.fin_mapₓ'. -/
@[simp]
theorem fin_map {n} {s : Finset ℕ} : (s.Fin n).map Fin.valEmbedding = s.filterₓ (· < n) := by
  simp [Finset.fin, Finset.map_map]
#align finset.fin_map Finset.fin_map

#print Finset.subset_image_iff /-
theorem subset_image_iff [DecidableEq β] {s : Set α} {t : Finset β} {f : α → β} :
    ↑t ⊆ f '' s ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ s'.image f = t :=
  by
  constructor; swap
  · rintro ⟨t, ht, rfl⟩
    rw [coe_image]
    exact Set.image_subset f ht
  intro h
  letI : CanLift β s (f ∘ coe) fun y => y ∈ f '' s := ⟨fun y ⟨x, hxt, hy⟩ => ⟨⟨x, hxt⟩, hy⟩⟩
  lift t to Finset s using h
  refine' ⟨t.map (embedding.subtype _), map_subtype_subset _, _⟩
  ext y; simp
#align finset.subset_image_iff Finset.subset_image_iff
-/

/- warning: finset.range_sdiff_zero -> Finset.range_sdiff_zero is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (SDiff.sdiff.{0} (Finset.{0} Nat) (Finset.hasSdiff.{0} Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.hasSingleton.{0} Nat) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => Nat.decidableEq a b) Nat.succ (Finset.range n))
but is expected to have type
  forall {n : Nat}, Eq.{1} (Finset.{0} Nat) (SDiff.sdiff.{0} (Finset.{0} Nat) (Finset.instSDiffFinset.{0} Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b)) (Finset.range (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (Finset.instSingletonFinset.{0} Nat) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Finset.image.{0, 0} Nat Nat (fun (a : Nat) (b : Nat) => instDecidableEqNat a b) Nat.succ (Finset.range n))
Case conversion may be inaccurate. Consider using '#align finset.range_sdiff_zero Finset.range_sdiff_zeroₓ'. -/
theorem range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image Nat.succ :=
  by
  induction' n with k hk
  · simp
  nth_rw 2 [range_succ]
  rw [range_succ, image_insert, ← hk, insert_sdiff_of_not_mem]
  simp
#align finset.range_sdiff_zero Finset.range_sdiff_zero

end Finset

/- warning: multiset.to_finset_map -> Multiset.toFinset_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : α -> β) (m : Multiset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (Multiset.toFinset.{u2} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u1, u2} α β f m)) (Finset.image.{u1, u2} α β (fun (a : β) (b : β) => _inst_2 a b) f (Multiset.toFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b) m))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : α -> β) (m : Multiset.{u2} α), Eq.{succ u1} (Finset.{u1} β) (Multiset.toFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b) (Multiset.map.{u2, u1} α β f m)) (Finset.image.{u2, u1} α β (fun (a : β) (b : β) => _inst_2 a b) f (Multiset.toFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b) m))
Case conversion may be inaccurate. Consider using '#align multiset.to_finset_map Multiset.toFinset_mapₓ'. -/
theorem Multiset.toFinset_map [DecidableEq α] [DecidableEq β] (f : α → β) (m : Multiset α) :
    (m.map f).toFinset = m.toFinset.image f :=
  Finset.val_inj.1 (Multiset.dedup_map_dedup_eq _ _).symm
#align multiset.to_finset_map Multiset.toFinset_map

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

/- warning: equiv.finset_congr_apply -> Equiv.finsetCongr_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β) (s : Finset.{u1} α), Eq.{succ u2} (Finset.{u2} β) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) (fun (_x : Equiv.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) => (Finset.{u1} α) -> (Finset.{u2} β)) (Equiv.hasCoeToFun.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) (Equiv.finsetCongr.{u1, u2} α β e) s) (Finset.map.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β e) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β) (s : Finset.{u2} α), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finset.{u2} α) => Finset.{u1} β) s) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β)) (Finset.{u2} α) (fun (_x : Finset.{u2} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Finset.{u2} α) => Finset.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β)) (Equiv.finsetCongr.{u2, u1} α β e) s) (Finset.map.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β e) s)
Case conversion may be inaccurate. Consider using '#align equiv.finset_congr_apply Equiv.finsetCongr_applyₓ'. -/
@[simp]
theorem finsetCongr_apply (e : α ≃ β) (s : Finset α) : e.finsetCongr s = s.map e.toEmbedding :=
  rfl
#align equiv.finset_congr_apply Equiv.finsetCongr_apply

#print Equiv.finsetCongr_refl /-
@[simp]
theorem finsetCongr_refl : (Equiv.refl α).finsetCongr = Equiv.refl _ :=
  by
  ext
  simp
#align equiv.finset_congr_refl Equiv.finsetCongr_refl
-/

/- warning: equiv.finset_congr_symm -> Equiv.finsetCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2)} (Equiv.{succ u2, succ u1} (Finset.{u2} β) (Finset.{u1} α)) (Equiv.symm.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β) (Equiv.finsetCongr.{u1, u2} α β e)) (Equiv.finsetCongr.{u2, u1} β α (Equiv.symm.{succ u1, succ u2} α β e))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} (Finset.{u1} β) (Finset.{u2} α)) (Equiv.symm.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β) (Equiv.finsetCongr.{u2, u1} α β e)) (Equiv.finsetCongr.{u1, u2} β α (Equiv.symm.{succ u2, succ u1} α β e))
Case conversion may be inaccurate. Consider using '#align equiv.finset_congr_symm Equiv.finsetCongr_symmₓ'. -/
@[simp]
theorem finsetCongr_symm (e : α ≃ β) : e.finsetCongr.symm = e.symm.finsetCongr :=
  rfl
#align equiv.finset_congr_symm Equiv.finsetCongr_symm

/- warning: equiv.finset_congr_trans -> Equiv.finsetCongr_trans is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (e : Equiv.{succ u1, succ u2} α β) (e' : Equiv.{succ u2, succ u3} β γ), Eq.{max 1 (max (succ u1) (succ u3)) (succ u3) (succ u1)} (Equiv.{succ u1, succ u3} (Finset.{u1} α) (Finset.{u3} γ)) (Equiv.trans.{succ u1, succ u2, succ u3} (Finset.{u1} α) (Finset.{u2} β) (Finset.{u3} γ) (Equiv.finsetCongr.{u1, u2} α β e) (Equiv.finsetCongr.{u2, u3} β γ e')) (Equiv.finsetCongr.{u1, u3} α γ (Equiv.trans.{succ u1, succ u2, succ u3} α β γ e e'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} (e : Equiv.{succ u3, succ u2} α β) (e' : Equiv.{succ u2, succ u1} β γ), Eq.{max (succ u3) (succ u1)} (Equiv.{succ u3, succ u1} (Finset.{u3} α) (Finset.{u1} γ)) (Equiv.trans.{succ u3, succ u2, succ u1} (Finset.{u3} α) (Finset.{u2} β) (Finset.{u1} γ) (Equiv.finsetCongr.{u3, u2} α β e) (Equiv.finsetCongr.{u2, u1} β γ e')) (Equiv.finsetCongr.{u3, u1} α γ (Equiv.trans.{succ u3, succ u2, succ u1} α β γ e e'))
Case conversion may be inaccurate. Consider using '#align equiv.finset_congr_trans Equiv.finsetCongr_transₓ'. -/
@[simp]
theorem finsetCongr_trans (e : α ≃ β) (e' : β ≃ γ) :
    e.finsetCongr.trans e'.finsetCongr = (e.trans e').finsetCongr :=
  by
  ext
  simp [-Finset.mem_map, -Equiv.trans_toEmbedding]
#align equiv.finset_congr_trans Equiv.finsetCongr_trans

/- warning: equiv.finset_congr_to_embedding -> Equiv.finsetCongr_toEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.{succ u1, succ u2} α β), Eq.{max 1 (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β)) (Equiv.toEmbedding.{succ u1, succ u2} (Finset.{u1} α) (Finset.{u2} β) (Equiv.finsetCongr.{u1, u2} α β e)) (RelEmbedding.toEmbedding.{u1, u2} (Finset.{u1} α) (Finset.{u2} β) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u2} (Finset.{u2} β) (Preorder.toLE.{u2} (Finset.{u2} β) (PartialOrder.toPreorder.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β)))) (Finset.mapEmbedding.{u1, u2} α β (Equiv.toEmbedding.{succ u1, succ u2} α β e)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (e : Equiv.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (Function.Embedding.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β)) (Equiv.toEmbedding.{succ u2, succ u1} (Finset.{u2} α) (Finset.{u1} β) (Equiv.finsetCongr.{u2, u1} α β e)) (RelEmbedding.toEmbedding.{u2, u1} (Finset.{u2} α) (Finset.{u1} β) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u2} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u2} α) => LE.le.{u2} (Finset.{u2} α) (Preorder.toLE.{u2} (Finset.{u2} α) (PartialOrder.toPreorder.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} β) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} β) => LE.le.{u1} (Finset.{u1} β) (Preorder.toLE.{u1} (Finset.{u1} β) (PartialOrder.toPreorder.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.mapEmbedding.{u2, u1} α β (Equiv.toEmbedding.{succ u2, succ u1} α β e)))
Case conversion may be inaccurate. Consider using '#align equiv.finset_congr_to_embedding Equiv.finsetCongr_toEmbeddingₓ'. -/
theorem finsetCongr_toEmbedding (e : α ≃ β) :
    e.finsetCongr.toEmbedding = (Finset.mapEmbedding e.toEmbedding).toEmbedding :=
  rfl
#align equiv.finset_congr_to_embedding Equiv.finsetCongr_toEmbedding

end Equiv

