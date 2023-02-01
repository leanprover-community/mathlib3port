/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather

! This file was ported from Lean 3 source module data.finset.option
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card
import Mathbin.Order.Hom.Basic

/-!
# Finite sets in `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define

* `option.to_finset`: construct an empty or singleton `finset α` from an `option α`;
* `finset.insert_none`: given `s : finset α`, lift it to a finset on `option α` using `option.some`
  and then insert `option.none`;
* `finset.erase_none`: given `s : finset (option α)`, returns `t : finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/


variable {α β : Type _}

open Function

namespace Option

#print Option.toFinset /-
/-- Construct an empty or singleton finset from an `option` -/
def toFinset (o : Option α) : Finset α :=
  o.elim ∅ singleton
#align option.to_finset Option.toFinset
-/

#print Option.toFinset_none /-
@[simp]
theorem toFinset_none : none.toFinset = (∅ : Finset α) :=
  rfl
#align option.to_finset_none Option.toFinset_none
-/

#print Option.toFinset_some /-
@[simp]
theorem toFinset_some {a : α} : (some a).toFinset = {a} :=
  rfl
#align option.to_finset_some Option.toFinset_some
-/

#print Option.mem_toFinset /-
@[simp]
theorem mem_toFinset {a : α} {o : Option α} : a ∈ o.toFinset ↔ a ∈ o := by
  cases o <;> simp [eq_comm]
#align option.mem_to_finset Option.mem_toFinset
-/

#print Option.card_toFinset /-
theorem card_toFinset (o : Option α) : o.toFinset.card = o.elim 0 1 := by cases o <;> rfl
#align option.card_to_finset Option.card_toFinset
-/

end Option

namespace Finset

#print Finset.insertNone /-
/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insertNone : Finset α ↪o Finset (Option α) :=
  OrderEmbedding.ofMapLeIff (fun s => cons none (s.map Embedding.some) <| by simp) fun s t =>
    cons_subset_cons.trans map_subset_map
#align finset.insert_none Finset.insertNone
-/

/- warning: finset.mem_insert_none -> Finset.mem_insertNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {o : Option.{u1} α}, Iff (Membership.Mem.{u1, u1} (Option.{u1} α) (Finset.{u1} (Option.{u1} α)) (Finset.hasMem.{u1} (Option.{u1} α)) o (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) s)) (forall (a : α), (Membership.Mem.{u1, u1} α (Option.{u1} α) (Option.hasMem.{u1} α) a o) -> (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {o : Option.{u1} α}, Iff (Membership.mem.{u1, u1} (Option.{u1} α) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) s) (Finset.instMembershipFinset.{u1} (Option.{u1} α)) o (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) s)) (forall (a : α), (Membership.mem.{u1, u1} α (Option.{u1} α) (Option.instMembershipOption.{u1} α) a o) -> (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align finset.mem_insert_none Finset.mem_insertNoneₓ'. -/
/-⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, s.nodup.map $ λ a b, option.some.inj⟩⟩-/
@[simp]
theorem mem_insertNone {s : Finset α} : ∀ {o : Option α}, o ∈ s.insertNone ↔ ∀ a ∈ o, a ∈ s
  | none => iff_of_true (Multiset.mem_cons_self _ _) fun a h => by cases h
  | some a => Multiset.mem_cons.trans <| by simp <;> rfl
#align finset.mem_insert_none Finset.mem_insertNone

/- warning: finset.some_mem_insert_none -> Finset.some_mem_insertNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Membership.Mem.{u1, u1} (Option.{u1} α) (Finset.{u1} (Option.{u1} α)) (Finset.hasMem.{u1} (Option.{u1} α)) (Option.some.{u1} α a) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) s)) (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {a : α}, Iff (Membership.mem.{u1, u1} (Option.{u1} α) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) s) (Finset.instMembershipFinset.{u1} (Option.{u1} α)) (Option.some.{u1} α a) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) s)) (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align finset.some_mem_insert_none Finset.some_mem_insertNoneₓ'. -/
theorem some_mem_insertNone {s : Finset α} {a : α} : some a ∈ s.insertNone ↔ a ∈ s := by simp
#align finset.some_mem_insert_none Finset.some_mem_insertNone

/- warning: finset.card_insert_none -> Finset.card_insertNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Option.{u1} α) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) s)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (Finset.card.{u1} α s) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{1} Nat (Finset.card.{u1} (Option.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) s)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (Finset.card.{u1} α s) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finset.card_insert_none Finset.card_insertNoneₓ'. -/
@[simp]
theorem card_insertNone (s : Finset α) : s.insertNone.card = s.card + 1 := by simp [insert_none]
#align finset.card_insert_none Finset.card_insertNone

#print Finset.eraseNone /-
/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def eraseNone : Finset (Option α) →o Finset α :=
  (Finset.mapEmbedding (Equiv.optionIsSomeEquiv α).toEmbedding).toOrderHom.comp
    ⟨Finset.subtype _, subtype_mono⟩
#align finset.erase_none Finset.eraseNone
-/

#print Finset.mem_eraseNone /-
@[simp]
theorem mem_eraseNone {s : Finset (Option α)} {x : α} : x ∈ s.eraseNone ↔ some x ∈ s := by
  simp [erase_none]
#align finset.mem_erase_none Finset.mem_eraseNone
-/

#print Finset.eraseNone_eq_bUnion /-
theorem eraseNone_eq_bUnion [DecidableEq α] (s : Finset (Option α)) :
    s.eraseNone = s.bunionᵢ Option.toFinset := by
  ext
  simp
#align finset.erase_none_eq_bUnion Finset.eraseNone_eq_bUnion
-/

#print Finset.eraseNone_map_some /-
@[simp]
theorem eraseNone_map_some (s : Finset α) : (s.map Embedding.some).eraseNone = s :=
  by
  ext
  simp
#align finset.erase_none_map_some Finset.eraseNone_map_some
-/

#print Finset.eraseNone_image_some /-
@[simp]
theorem eraseNone_image_some [DecidableEq (Option α)] (s : Finset α) :
    (s.image some).eraseNone = s := by simpa only [map_eq_image] using erase_none_map_some s
#align finset.erase_none_image_some Finset.eraseNone_image_some
-/

#print Finset.coe_eraseNone /-
@[simp]
theorem coe_eraseNone (s : Finset (Option α)) : (s.eraseNone : Set α) = some ⁻¹' s :=
  Set.ext fun x => mem_eraseNone
#align finset.coe_erase_none Finset.coe_eraseNone
-/

#print Finset.eraseNone_union /-
@[simp]
theorem eraseNone_union [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∪ t).eraseNone = s.eraseNone ∪ t.eraseNone :=
  by
  ext
  simp
#align finset.erase_none_union Finset.eraseNone_union
-/

#print Finset.eraseNone_inter /-
@[simp]
theorem eraseNone_inter [DecidableEq (Option α)] [DecidableEq α] (s t : Finset (Option α)) :
    (s ∩ t).eraseNone = s.eraseNone ∩ t.eraseNone :=
  by
  ext
  simp
#align finset.erase_none_inter Finset.eraseNone_inter
-/

#print Finset.eraseNone_empty /-
@[simp]
theorem eraseNone_empty : (∅ : Finset (Option α)).eraseNone = ∅ :=
  by
  ext
  simp
#align finset.erase_none_empty Finset.eraseNone_empty
-/

#print Finset.eraseNone_none /-
@[simp]
theorem eraseNone_none : ({none} : Finset (Option α)).eraseNone = ∅ :=
  by
  ext
  simp
#align finset.erase_none_none Finset.eraseNone_none
-/

#print Finset.image_some_eraseNone /-
@[simp]
theorem image_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.image some = s.eraseₓ none := by ext (_ | x) <;> simp
#align finset.image_some_erase_none Finset.image_some_eraseNone
-/

#print Finset.map_some_eraseNone /-
@[simp]
theorem map_some_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    s.eraseNone.map Embedding.some = s.eraseₓ none := by
  rw [map_eq_image, embedding.some_apply, image_some_erase_none]
#align finset.map_some_erase_none Finset.map_some_eraseNone
-/

/- warning: finset.insert_none_erase_none -> Finset.insert_none_eraseNone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} (Option.{u1} α)] (s : Finset.{u1} (Option.{u1} α)), Eq.{succ u1} (Finset.{u1} (Option.{u1} α)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (fun (_x : OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) => (Finset.{u1} (Option.{u1} α)) -> (Finset.{u1} α)) (OrderHom.hasCoeToFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.eraseNone.{u1} α) s)) (Insert.insert.{u1, u1} (Option.{u1} α) (Finset.{u1} (Option.{u1} α)) (Finset.hasInsert.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => _inst_1 a b)) (Option.none.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} (Option.{u1} α)] (s : Finset.{u1} (Option.{u1} α)), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) (OrderHom.toFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.eraseNone.{u1} α) s)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) (OrderHom.toFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.eraseNone.{u1} α) s)) (Insert.insert.{u1, u1} (Option.{u1} α) (Finset.{u1} (Option.{u1} α)) (Finset.instInsertFinset.{u1} (Option.{u1} α) (fun (a : Option.{u1} α) (b : Option.{u1} α) => _inst_1 a b)) (Option.none.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align finset.insert_none_erase_none Finset.insert_none_eraseNoneₓ'. -/
@[simp]
theorem insert_none_eraseNone [DecidableEq (Option α)] (s : Finset (Option α)) :
    insertNone (eraseNone s) = insert none s := by ext (_ | x) <;> simp
#align finset.insert_none_erase_none Finset.insert_none_eraseNone

/- warning: finset.erase_none_insert_none -> Finset.eraseNone_insert_none is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (fun (_x : OrderHom.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) => (Finset.{u1} (Option.{u1} α)) -> (Finset.{u1} α)) (OrderHom.hasCoeToFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Finset.eraseNone.{u1} α) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))))) (fun (_x : RelEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) => (Finset.{u1} α) -> (Finset.{u1} (Option.{u1} α))) (RelEmbedding.hasCoeToFun.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)))) (LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))))) (Finset.insertNone.{u1} α) s)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (OrderHom.toFun.{u1, u1} (Finset.{u1} (Option.{u1} α)) (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α))) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α)) (Finset.eraseNone.{u1} α) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (fun (_x : Finset.{u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Finset.{u1} α) => Finset.{u1} (Option.{u1} α)) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α))) (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)))) (RelEmbedding.toEmbedding.{u1, u1} (Finset.{u1} α) (Finset.{u1} (Option.{u1} α)) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.680 : Finset.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.682 : Finset.{u1} α) => LE.le.{u1} (Finset.{u1} α) (Preorder.toLE.{u1} (Finset.{u1} α) (PartialOrder.toPreorder.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α))) x._@.Mathlib.Order.Hom.Basic._hyg.680 x._@.Mathlib.Order.Hom.Basic._hyg.682) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.695 : Finset.{u1} (Option.{u1} α)) (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Finset.{u1} (Option.{u1} α)) => LE.le.{u1} (Finset.{u1} (Option.{u1} α)) (Preorder.toLE.{u1} (Finset.{u1} (Option.{u1} α)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Option.{u1} α)) (Finset.partialOrder.{u1} (Option.{u1} α)))) x._@.Mathlib.Order.Hom.Basic._hyg.695 x._@.Mathlib.Order.Hom.Basic._hyg.697) (Finset.insertNone.{u1} α)) s)) s
Case conversion may be inaccurate. Consider using '#align finset.erase_none_insert_none Finset.eraseNone_insert_noneₓ'. -/
@[simp]
theorem eraseNone_insert_none (s : Finset α) : eraseNone (insertNone s) = s :=
  by
  ext
  simp
#align finset.erase_none_insert_none Finset.eraseNone_insert_none

end Finset

