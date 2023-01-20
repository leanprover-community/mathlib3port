/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.fold
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Data.Finset.Image
import Mathbin.Data.Multiset.Fold

/-!
# The fold operation for a commutative associative operation over a finset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Finset

open Multiset

variable {α β γ : Type _}

/-! ### fold -/


section Fold

variable (op : β → β → β) [hc : IsCommutative β op] [ha : IsAssociative β op]

-- mathport name: op
local notation a " * " b => op a b

include hc ha

#print Finset.fold /-
/-- `fold op b f s` folds the commutative associative operation `op` over the
  `f`-image of `s`, i.e. `fold (+) b f {1,2,3} = f 1 + f 2 + f 3 + b`. -/
def fold (b : β) (f : α → β) (s : Finset α) : β :=
  (s.1.map f).fold op b
#align finset.fold Finset.fold
-/

variable {op} {f : α → β} {b : β} {s : Finset α} {a : α}

#print Finset.fold_empty /-
@[simp]
theorem fold_empty : (∅ : Finset α).fold op b f = b :=
  rfl
#align finset.fold_empty Finset.fold_empty
-/

/- warning: finset.fold_cons -> Finset.fold_cons is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {a : α} (h : Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)), Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Finset.cons.{u1} α a s h)) (op (f a) (Finset.fold.{u1, u2} α β op hc ha b f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {a : α} (h : Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)), Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b f (Finset.cons.{u2} α a s h)) (op (f a) (Finset.fold.{u2, u1} α β op hc ha b f s))
Case conversion may be inaccurate. Consider using '#align finset.fold_cons Finset.fold_consₓ'. -/
@[simp]
theorem fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a * s.fold op b f :=
  by
  dsimp only [fold]
  rw [cons_val, Multiset.map_cons, fold_cons_left]
#align finset.fold_cons Finset.fold_cons

/- warning: finset.fold_insert -> Finset.fold_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α], (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (op (f a) (Finset.fold.{u1, u2} α β op hc ha b f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {a : α} [_inst_1 : DecidableEq.{succ u2} α], (Not (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s)) -> (Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b f (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (op (f a) (Finset.fold.{u2, u1} α β op hc ha b f s)))
Case conversion may be inaccurate. Consider using '#align finset.fold_insert Finset.fold_insertₓ'. -/
@[simp]
theorem fold_insert [DecidableEq α] (h : a ∉ s) : (insert a s).fold op b f = f a * s.fold op b f :=
  by unfold fold <;> rw [insert_val, ndinsert_of_not_mem h, Multiset.map_cons, fold_cons_left]
#align finset.fold_insert Finset.fold_insert

#print Finset.fold_singleton /-
@[simp]
theorem fold_singleton : ({a} : Finset α).fold op b f = f a * b :=
  rfl
#align finset.fold_singleton Finset.fold_singleton
-/

/- warning: finset.fold_map -> Finset.fold_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {g : Function.Embedding.{succ u3, succ u1} γ α} {s : Finset.{u3} γ}, Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Finset.map.{u3, u1} γ α g s)) (Finset.fold.{u3, u2} γ β op hc ha b (Function.comp.{succ u3, succ u1, succ u2} γ α β f (coeFn.{max 1 (succ u3) (succ u1), max (succ u3) (succ u1)} (Function.Embedding.{succ u3, succ u1} γ α) (fun (_x : Function.Embedding.{succ u3, succ u1} γ α) => γ -> α) (Function.Embedding.hasCoeToFun.{succ u3, succ u1} γ α) g)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {g : Function.Embedding.{succ u3, succ u2} γ α} {s : Finset.{u3} γ}, Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b f (Finset.map.{u3, u2} γ α g s)) (Finset.fold.{u3, u1} γ β op hc ha b (Function.comp.{succ u3, succ u2, succ u1} γ α β f (FunLike.coe.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ α) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u3), succ u3, succ u2} (Function.Embedding.{succ u3, succ u2} γ α) γ α (Function.instEmbeddingLikeEmbedding.{succ u3, succ u2} γ α)) g)) s)
Case conversion may be inaccurate. Consider using '#align finset.fold_map Finset.fold_mapₓ'. -/
@[simp]
theorem fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, map, Multiset.map_map]
#align finset.fold_map Finset.fold_map

/- warning: finset.fold_image -> Finset.fold_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} [_inst_1 : DecidableEq.{succ u1} α] {g : γ -> α} {s : Finset.{u3} γ}, (forall (x : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) x s) -> (forall (y : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) y s) -> (Eq.{succ u1} α (g x) (g y)) -> (Eq.{succ u3} γ x y))) -> (Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) g s)) (Finset.fold.{u3, u2} γ β op hc ha b (Function.comp.{succ u3, succ u1, succ u2} γ α β f g) s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} [_inst_1 : DecidableEq.{succ u3} α] {g : γ -> α} {s : Finset.{u2} γ}, (forall (x : γ), (Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) x s) -> (forall (y : γ), (Membership.mem.{u2, u2} γ (Finset.{u2} γ) (Finset.instMembershipFinset.{u2} γ) y s) -> (Eq.{succ u3} α (g x) (g y)) -> (Eq.{succ u2} γ x y))) -> (Eq.{succ u1} β (Finset.fold.{u3, u1} α β op hc ha b f (Finset.image.{u2, u3} γ α (fun (a : α) (b : α) => _inst_1 a b) g s)) (Finset.fold.{u2, u1} γ β op hc ha b (Function.comp.{succ u2, succ u3, succ u1} γ α β f g) s))
Case conversion may be inaccurate. Consider using '#align finset.fold_image Finset.fold_imageₓ'. -/
@[simp]
theorem fold_image [DecidableEq α] {g : γ → α} {s : Finset γ}
    (H : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) : (s.image g).fold op b f = s.fold op b (f ∘ g) := by
  simp only [fold, image_val_of_inj_on H, Multiset.map_map]
#align finset.fold_image Finset.fold_image

/- warning: finset.fold_congr -> Finset.fold_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {g : α -> β}, (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Eq.{succ u2} β (f x) (g x))) -> (Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f s) (Finset.fold.{u1, u2} α β op hc ha b g s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {g : α -> β}, (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (Eq.{succ u1} β (f x) (g x))) -> (Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b f s) (Finset.fold.{u2, u1} α β op hc ha b g s))
Case conversion may be inaccurate. Consider using '#align finset.fold_congr Finset.fold_congrₓ'. -/
@[congr]
theorem fold_congr {g : α → β} (H : ∀ x ∈ s, f x = g x) : s.fold op b f = s.fold op b g := by
  rw [fold, fold, map_congr rfl H]
#align finset.fold_congr Finset.fold_congr

#print Finset.fold_op_distrib /-
theorem fold_op_distrib {f g : α → β} {b₁ b₂ : β} :
    (s.fold op (b₁ * b₂) fun x => f x * g x) = s.fold op b₁ f * s.fold op b₂ g := by
  simp only [fold, fold_distrib]
#align finset.fold_op_distrib Finset.fold_op_distrib
-/

/- warning: finset.fold_const -> Finset.fold_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {b : β} {s : Finset.{u1} α} [_inst_1 : Decidable (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)))] (c : β), (Eq.{succ u2} β (op c (op b c)) (op b c)) -> (Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b (fun (_x : α) => c) s) (ite.{succ u2} β (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) _inst_1 b (op b c)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {b : β} {s : Finset.{u2} α} [_inst_1 : Decidable (Eq.{succ u2} (Finset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)))] (c : β), (Eq.{succ u1} β (op c (op b c)) (op b c)) -> (Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b (fun (_x : α) => c) s) (ite.{succ u1} β (Eq.{succ u2} (Finset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) _inst_1 b (op b c)))
Case conversion may be inaccurate. Consider using '#align finset.fold_const Finset.fold_constₓ'. -/
theorem fold_const [Decidable (s = ∅)] (c : β) (h : op c (op b c) = op b c) :
    Finset.fold op b (fun _ => c) s = if s = ∅ then b else op b c := by
  classical
    induction' s using Finset.induction_on with x s hx IH
    · simp
    · simp only [Finset.fold_insert hx, IH, if_false, Finset.insert_ne_empty]
      split_ifs
      · rw [hc.comm]
      · exact h
#align finset.fold_const Finset.fold_const

/- warning: finset.fold_hom -> Finset.fold_hom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {op' : γ -> γ -> γ} [_inst_1 : IsCommutative.{u3} γ op'] [_inst_2 : IsAssociative.{u3} γ op'] {m : β -> γ}, (forall (x : β) (y : β), Eq.{succ u3} γ (m (op x y)) (op' (m x) (m y))) -> (Eq.{succ u3} γ (Finset.fold.{u1, u3} α γ op' _inst_1 _inst_2 (m b) (fun (x : α) => m (f x)) s) (m (Finset.fold.{u1, u2} α β op hc ha b f s)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {op' : γ -> γ -> γ} [_inst_1 : IsCommutative.{u3} γ op'] [_inst_2 : IsAssociative.{u3} γ op'] {m : β -> γ}, (forall (x : β) (y : β), Eq.{succ u3} γ (m (op x y)) (op' (m x) (m y))) -> (Eq.{succ u3} γ (Finset.fold.{u2, u3} α γ op' _inst_1 _inst_2 (m b) (fun (x : α) => m (f x)) s) (m (Finset.fold.{u2, u1} α β op hc ha b f s)))
Case conversion may be inaccurate. Consider using '#align finset.fold_hom Finset.fold_homₓ'. -/
theorem fold_hom {op' : γ → γ → γ} [IsCommutative γ op'] [IsAssociative γ op'] {m : β → γ}
    (hm : ∀ x y, m (op x y) = op' (m x) (m y)) :
    (s.fold op' (m b) fun x => m (f x)) = m (s.fold op b f) := by
  rw [fold, fold, ← fold_hom op hm, Multiset.map_map]
#align finset.fold_hom Finset.fold_hom

/- warning: finset.fold_disj_union -> Finset.fold_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {b₁ : β} {b₂ : β} (h : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s₁ s₂), Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha (op b₁ b₂) f (Finset.disjUnion.{u1} α s₁ s₂ h)) (op (Finset.fold.{u1, u2} α β op hc ha b₁ f s₁) (Finset.fold.{u1, u2} α β op hc ha b₂ f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {b₁ : β} {b₂ : β} (h : Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s₁ s₂), Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha (op b₁ b₂) f (Finset.disjUnion.{u2} α s₁ s₂ h)) (op (Finset.fold.{u2, u1} α β op hc ha b₁ f s₁) (Finset.fold.{u2, u1} α β op hc ha b₂ f s₂))
Case conversion may be inaccurate. Consider using '#align finset.fold_disj_union Finset.fold_disjUnionₓ'. -/
theorem fold_disjUnion {s₁ s₂ : Finset α} {b₁ b₂ : β} (h) :
    (s₁.disjUnion s₂ h).fold op (b₁ * b₂) f = s₁.fold op b₁ f * s₂.fold op b₂ f :=
  (congr_arg _ <| Multiset.map_add _ _ _).trans (Multiset.fold_add _ _ _ _ _)
#align finset.fold_disj_union Finset.fold_disjUnion

/- warning: finset.fold_disj_Union -> Finset.fold_disjUnionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {ι : Type.{u3}} {s : Finset.{u3} ι} {t : ι -> (Finset.{u1} α)} {b : ι -> β} {b₀ : β} (h : Set.PairwiseDisjoint.{u1, u3} (Finset.{u1} α) ι (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} ι) (Set.{u3} ι) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} ι) (Set.{u3} ι) (Finset.Set.hasCoeT.{u3} ι))) s) t), Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha (Finset.fold.{u3, u2} ι β op hc ha b₀ b s) f (Finset.disjUnionₓ.{u3, u1} ι α s t h)) (Finset.fold.{u3, u2} ι β op hc ha b₀ (fun (i : ι) => Finset.fold.{u1, u2} α β op hc ha (b i) f (t i)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {ι : Type.{u3}} {s : Finset.{u3} ι} {t : ι -> (Finset.{u2} α)} {b : ι -> β} {b₀ : β} (h : Set.PairwiseDisjoint.{u2, u3} (Finset.{u2} α) ι (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) (Finset.toSet.{u3} ι s) t), Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha (Finset.fold.{u3, u1} ι β op hc ha b₀ b s) f (Finset.disjUnionᵢ.{u3, u2} ι α s t h)) (Finset.fold.{u3, u1} ι β op hc ha b₀ (fun (i : ι) => Finset.fold.{u2, u1} α β op hc ha (b i) f (t i)) s)
Case conversion may be inaccurate. Consider using '#align finset.fold_disj_Union Finset.fold_disjUnionᵢₓ'. -/
theorem fold_disjUnionᵢ {ι : Type _} {s : Finset ι} {t : ι → Finset α} {b : ι → β} {b₀ : β} (h) :
    (s.disjUnion t h).fold op (s.fold op b₀ b) f = s.fold op b₀ fun i => (t i).fold op (b i) f :=
  (congr_arg _ <| Multiset.map_bind _ _ _).trans (Multiset.fold_bind _ _ _ _ _)
#align finset.fold_disj_Union Finset.fold_disjUnionᵢ

/- warning: finset.fold_union_inter -> Finset.fold_union_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} [_inst_1 : DecidableEq.{succ u1} α] {s₁ : Finset.{u1} α} {s₂ : Finset.{u1} α} {b₁ : β} {b₂ : β}, Eq.{succ u2} β (op (Finset.fold.{u1, u2} α β op hc ha b₁ f (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Finset.fold.{u1, u2} α β op hc ha b₂ f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂))) (op (Finset.fold.{u1, u2} α β op hc ha b₂ f s₁) (Finset.fold.{u1, u2} α β op hc ha b₁ f s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} [_inst_1 : DecidableEq.{succ u2} α] {s₁ : Finset.{u2} α} {s₂ : Finset.{u2} α} {b₁ : β} {b₂ : β}, Eq.{succ u1} β (op (Finset.fold.{u2, u1} α β op hc ha b₁ f (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂)) (Finset.fold.{u2, u1} α β op hc ha b₂ f (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s₁ s₂))) (op (Finset.fold.{u2, u1} α β op hc ha b₂ f s₁) (Finset.fold.{u2, u1} α β op hc ha b₁ f s₂))
Case conversion may be inaccurate. Consider using '#align finset.fold_union_inter Finset.fold_union_interₓ'. -/
theorem fold_union_inter [DecidableEq α] {s₁ s₂ : Finset α} {b₁ b₂ : β} :
    ((s₁ ∪ s₂).fold op b₁ f * (s₁ ∩ s₂).fold op b₂ f) = s₁.fold op b₂ f * s₂.fold op b₁ f := by
  unfold fold <;>
    rw [← fold_add op, ← Multiset.map_add, union_val, inter_val, union_add_inter, Multiset.map_add,
      hc.comm, fold_add]
#align finset.fold_union_inter Finset.fold_union_inter

/- warning: finset.fold_insert_idem -> Finset.fold_insert_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {a : α} [_inst_1 : DecidableEq.{succ u1} α] [hi : IsIdempotent.{u2} β op], Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (op (f a) (Finset.fold.{u1, u2} α β op hc ha b f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {a : α} [_inst_1 : DecidableEq.{succ u2} α] [hi : IsIdempotent.{u1} β op], Eq.{succ u1} β (Finset.fold.{u2, u1} α β op hc ha b f (Insert.insert.{u2, u2} α (Finset.{u2} α) (Finset.instInsertFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (op (f a) (Finset.fold.{u2, u1} α β op hc ha b f s))
Case conversion may be inaccurate. Consider using '#align finset.fold_insert_idem Finset.fold_insert_idemₓ'. -/
@[simp]
theorem fold_insert_idem [DecidableEq α] [hi : IsIdempotent β op] :
    (insert a s).fold op b f = f a * s.fold op b f :=
  by
  by_cases a ∈ s
  · rw [← insert_erase h]
    simp [← ha.assoc, hi.idempotent]
  · apply fold_insert h
#align finset.fold_insert_idem Finset.fold_insert_idem

/- warning: finset.fold_image_idem -> Finset.fold_image_idem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} [_inst_1 : DecidableEq.{succ u1} α] {g : γ -> α} {s : Finset.{u3} γ} [hi : IsIdempotent.{u2} β op], Eq.{succ u2} β (Finset.fold.{u1, u2} α β op hc ha b f (Finset.image.{u3, u1} γ α (fun (a : α) (b : α) => _inst_1 a b) g s)) (Finset.fold.{u3, u2} γ β op hc ha b (Function.comp.{succ u3, succ u1, succ u2} γ α β f g) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} [_inst_1 : DecidableEq.{succ u3} α] {g : γ -> α} {s : Finset.{u2} γ} [hi : IsIdempotent.{u1} β op], Eq.{succ u1} β (Finset.fold.{u3, u1} α β op hc ha b f (Finset.image.{u2, u3} γ α (fun (a : α) (b : α) => _inst_1 a b) g s)) (Finset.fold.{u2, u1} γ β op hc ha b (Function.comp.{succ u2, succ u3, succ u1} γ α β f g) s)
Case conversion may be inaccurate. Consider using '#align finset.fold_image_idem Finset.fold_image_idemₓ'. -/
theorem fold_image_idem [DecidableEq α] {g : γ → α} {s : Finset γ} [hi : IsIdempotent β op] :
    (image g s).fold op b f = s.fold op b (f ∘ g) :=
  by
  induction' s using Finset.cons_induction with x xs hx ih
  · rw [fold_empty, image_empty, fold_empty]
  · haveI := Classical.decEq γ
    rw [fold_cons, cons_eq_insert, image_insert, fold_insert_idem, ih]
#align finset.fold_image_idem Finset.fold_image_idem

#print Finset.fold_ite' /-
/-- A stronger version of `finset.fold_ite`, but relies on
an explicit proof of idempotency on the seed element, rather
than relying on typeclass idempotency over the whole type. -/
theorem fold_ite' {g : α → β} (hb : op b b = b) (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  by
  classical
    induction' s using Finset.induction_on with x s hx IH
    · simp [hb]
    · simp only [[anonymous], Finset.fold_insert hx]
      split_ifs with h h
      · have : x ∉ Finset.filter p s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, ha.assoc, IH]
      · have : x ∉ Finset.filter (fun i => ¬p i) s := by simp [hx]
        simp [Finset.filter_insert, h, Finset.fold_insert this, IH, ← ha.assoc, hc.comm]
#align finset.fold_ite' Finset.fold_ite'
-/

#print Finset.fold_ite /-
/-- A weaker version of `finset.fold_ite'`,
relying on typeclass idempotency over the whole type,
instead of solely on the seed element.
However, this is easier to use because it does not generate side goals. -/
theorem fold_ite [IsIdempotent β op] {g : α → β} (p : α → Prop) [DecidablePred p] :
    Finset.fold op b (fun i => ite (p i) (f i) (g i)) s =
      op (Finset.fold op b f (s.filter p)) (Finset.fold op b g (s.filter fun i => ¬p i)) :=
  fold_ite' (IsIdempotent.idempotent _) _
#align finset.fold_ite Finset.fold_ite
-/

/- warning: finset.fold_op_rel_iff_and -> Finset.fold_op_rel_iff_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {r : β -> β -> Prop}, (forall {x : β} {y : β} {z : β}, Iff (r x (op y z)) (And (r x y) (r x z))) -> (forall {c : β}, Iff (r c (Finset.fold.{u1, u2} α β op hc ha b f s)) (And (r c b) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (r c (f x)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {r : β -> β -> Prop}, (forall {x : β} {y : β} {z : β}, Iff (r x (op y z)) (And (r x y) (r x z))) -> (forall {c : β}, Iff (r c (Finset.fold.{u2, u1} α β op hc ha b f s)) (And (r c b) (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (r c (f x)))))
Case conversion may be inaccurate. Consider using '#align finset.fold_op_rel_iff_and Finset.fold_op_rel_iff_andₓ'. -/
theorem fold_op_rel_iff_and {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∧ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∧ ∀ x ∈ s, r c (f x) := by
  classical
    apply Finset.induction_on s
    · simp
    clear s
    intro a s ha IH
    rw [Finset.fold_insert ha, hr, IH, ← and_assoc', and_comm' (r c (f a)), and_assoc']
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨h₁, h₂⟩
      intro b hb
      rw [Finset.mem_insert] at hb
      rcases hb with (rfl | hb) <;> solve_by_elim
    · intro h
      constructor
      · exact h a (Finset.mem_insert_self _ _)
      · intro b hb
        apply h b
        rw [Finset.mem_insert]
        right
        exact hb
#align finset.fold_op_rel_iff_and Finset.fold_op_rel_iff_and

/- warning: finset.fold_op_rel_iff_or -> Finset.fold_op_rel_iff_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {op : β -> β -> β} [hc : IsCommutative.{u2} β op] [ha : IsAssociative.{u2} β op] {f : α -> β} {b : β} {s : Finset.{u1} α} {r : β -> β -> Prop}, (forall {x : β} {y : β} {z : β}, Iff (r x (op y z)) (Or (r x y) (r x z))) -> (forall {c : β}, Iff (r c (Finset.fold.{u1, u2} α β op hc ha b f s)) (Or (r c b) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => r c (f x))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {op : β -> β -> β} [hc : IsCommutative.{u1} β op] [ha : IsAssociative.{u1} β op] {f : α -> β} {b : β} {s : Finset.{u2} α} {r : β -> β -> Prop}, (forall {x : β} {y : β} {z : β}, Iff (r x (op y z)) (Or (r x y) (r x z))) -> (forall {c : β}, Iff (r c (Finset.fold.{u2, u1} α β op hc ha b f s)) (Or (r c b) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) (r c (f x))))))
Case conversion may be inaccurate. Consider using '#align finset.fold_op_rel_iff_or Finset.fold_op_rel_iff_orₓ'. -/
theorem fold_op_rel_iff_or {r : β → β → Prop} (hr : ∀ {x y z}, r x (op y z) ↔ r x y ∨ r x z)
    {c : β} : r c (s.fold op b f) ↔ r c b ∨ ∃ x ∈ s, r c (f x) := by
  classical
    apply Finset.induction_on s
    · simp
    clear s
    intro a s ha IH
    rw [Finset.fold_insert ha, hr, IH, ← or_assoc', or_comm' (r c (f a)), or_assoc']
    apply or_congr Iff.rfl
    constructor
    · rintro (h₁ | ⟨x, hx, h₂⟩)
      · use a
        simp [h₁]
      · refine' ⟨x, by simp [hx], h₂⟩
    · rintro ⟨x, hx, h⟩
      rw [mem_insert] at hx
      cases hx
      · left
        rwa [hx] at h
      · right
        exact ⟨x, hx, h⟩
#align finset.fold_op_rel_iff_or Finset.fold_op_rel_iff_or

omit hc ha

#print Finset.fold_union_empty_singleton /-
@[simp]
theorem fold_union_empty_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ∪ ·) ∅ singleton s = s :=
  by
  apply Finset.induction_on s
  · simp only [fold_empty]
  · intro a s has ih
    rw [fold_insert has, ih, insert_eq]
#align finset.fold_union_empty_singleton Finset.fold_union_empty_singleton
-/

/- warning: finset.fold_sup_bot_singleton -> Finset.fold_sup_bot_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.fold.{u1, u1} α (Finset.{u1} α) (HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))))) (Finset.hasUnion.Union.is_commutative.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Finset.hasUnion.Union.is_associative.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) (Bot.bot.{u1} (Finset.{u1} α) (GeneralizedBooleanAlgebra.toHasBot.{u1} (Finset.{u1} α) (Finset.generalizedBooleanAlgebra.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α)) s) s
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} α) (Finset.fold.{u1, u1} α (Finset.{u1} α) (fun (x._@.Mathlib.Data.Finset.Fold._hyg.2820 : Finset.{u1} α) (x._@.Mathlib.Data.Finset.Fold._hyg.2822 : Finset.{u1} α) => HasSup.sup.{u1} (Finset.{u1} α) (SemilatticeSup.toHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) x._@.Mathlib.Data.Finset.Fold._hyg.2820 x._@.Mathlib.Data.Finset.Fold._hyg.2822) (instIsCommutativeSupToHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (instIsAssociativeSupToHasSup.{u1} (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Bot.bot.{u1} (Finset.{u1} α) (GeneralizedBooleanAlgebra.toBot.{u1} (Finset.{u1} α) (Finset.instGeneralizedBooleanAlgebraFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)))) (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α)) s) s
Case conversion may be inaccurate. Consider using '#align finset.fold_sup_bot_singleton Finset.fold_sup_bot_singletonₓ'. -/
theorem fold_sup_bot_singleton [DecidableEq α] (s : Finset α) :
    Finset.fold (· ⊔ ·) ⊥ singleton s = s :=
  fold_union_empty_singleton s
#align finset.fold_sup_bot_singleton Finset.fold_sup_bot_singleton

section Order

variable [LinearOrder β] (c : β)

/- warning: finset.le_fold_min -> Finset.le_fold_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (Finset.fold.{u1, u2} α β (LinearOrder.min.{u2} β _inst_1) (inf_is_commutative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (inf_is_associative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s)) (And (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c b) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (Finset.fold.{u1, u2} α β (Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_1)) (instIsCommutativeMinToMin.{u2} β _inst_1) (instIsAssociativeMinToMin.{u2} β _inst_1) b f s)) (And (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c b) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (f x))))
Case conversion may be inaccurate. Consider using '#align finset.le_fold_min Finset.le_fold_minₓ'. -/
theorem le_fold_min : c ≤ s.fold min b f ↔ c ≤ b ∧ ∀ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_and fun x y z => le_min_iff
#align finset.le_fold_min Finset.le_fold_min

/- warning: finset.fold_min_le -> Finset.fold_min_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (Finset.fold.{u1, u2} α β (LinearOrder.min.{u2} β _inst_1) (inf_is_commutative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (inf_is_associative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s) c) (Or (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) b c) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f x) c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (Finset.fold.{u1, u2} α β (Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_1)) (instIsCommutativeMinToMin.{u2} β _inst_1) (instIsAssociativeMinToMin.{u2} β _inst_1) b f s) c) (Or (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) b c) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f x) c))))
Case conversion may be inaccurate. Consider using '#align finset.fold_min_le Finset.fold_min_leₓ'. -/
theorem fold_min_le : s.fold min b f ≤ c ↔ b ≤ c ∨ ∃ x ∈ s, f x ≤ c :=
  by
  show _ ≥ _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  show _ ≤ _ ↔ _
  exact min_le_iff
#align finset.fold_min_le Finset.fold_min_le

/- warning: finset.lt_fold_min -> Finset.lt_fold_min is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (Finset.fold.{u1, u2} α β (LinearOrder.min.{u2} β _inst_1) (inf_is_commutative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (inf_is_associative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s)) (And (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c b) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (f x))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (Finset.fold.{u1, u2} α β (Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_1)) (instIsCommutativeMinToMin.{u2} β _inst_1) (instIsAssociativeMinToMin.{u2} β _inst_1) b f s)) (And (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c b) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (f x))))
Case conversion may be inaccurate. Consider using '#align finset.lt_fold_min Finset.lt_fold_minₓ'. -/
theorem lt_fold_min : c < s.fold min b f ↔ c < b ∧ ∀ x ∈ s, c < f x :=
  fold_op_rel_iff_and fun x y z => lt_min_iff
#align finset.lt_fold_min Finset.lt_fold_min

/- warning: finset.fold_min_lt -> Finset.fold_min_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (Finset.fold.{u1, u2} α β (LinearOrder.min.{u2} β _inst_1) (inf_is_commutative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (inf_is_associative.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s) c) (Or (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) b c) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f x) c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (Finset.fold.{u1, u2} α β (Min.min.{u2} β (LinearOrder.toMin.{u2} β _inst_1)) (instIsCommutativeMinToMin.{u2} β _inst_1) (instIsAssociativeMinToMin.{u2} β _inst_1) b f s) c) (Or (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) b c) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f x) c))))
Case conversion may be inaccurate. Consider using '#align finset.fold_min_lt Finset.fold_min_ltₓ'. -/
theorem fold_min_lt : s.fold min b f < c ↔ b < c ∨ ∃ x ∈ s, f x < c :=
  by
  show _ > _ ↔ _
  apply fold_op_rel_iff_or
  intro x y z
  show _ < _ ↔ _
  exact min_lt_iff
#align finset.fold_min_lt Finset.fold_min_lt

/- warning: finset.fold_max_le -> Finset.fold_max_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (Finset.fold.{u1, u2} α β (LinearOrder.max.{u2} β _inst_1) (sup_is_commutative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (sup_is_associative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s) c) (And (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) b c) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f x) c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (Finset.fold.{u1, u2} α β (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1)) (instIsCommutativeMaxToMax.{u2} β _inst_1) (instIsAssociativeMaxToMax.{u2} β _inst_1) b f s) c) (And (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) b c) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f x) c)))
Case conversion may be inaccurate. Consider using '#align finset.fold_max_le Finset.fold_max_leₓ'. -/
theorem fold_max_le : s.fold max b f ≤ c ↔ b ≤ c ∧ ∀ x ∈ s, f x ≤ c :=
  by
  show _ ≥ _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  show _ ≤ _ ↔ _
  exact max_le_iff
#align finset.fold_max_le Finset.fold_max_le

/- warning: finset.le_fold_max -> Finset.le_fold_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (Finset.fold.{u1, u2} α β (LinearOrder.max.{u2} β _inst_1) (sup_is_commutative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (sup_is_associative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s)) (Or (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c b) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (f x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (Finset.fold.{u1, u2} α β (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1)) (instIsCommutativeMaxToMax.{u2} β _inst_1) (instIsAssociativeMaxToMax.{u2} β _inst_1) b f s)) (Or (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c b) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (f x)))))
Case conversion may be inaccurate. Consider using '#align finset.le_fold_max Finset.le_fold_maxₓ'. -/
theorem le_fold_max : c ≤ s.fold max b f ↔ c ≤ b ∨ ∃ x ∈ s, c ≤ f x :=
  fold_op_rel_iff_or fun x y z => le_max_iff
#align finset.le_fold_max Finset.le_fold_max

/- warning: finset.fold_max_lt -> Finset.fold_max_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (Finset.fold.{u1, u2} α β (LinearOrder.max.{u2} β _inst_1) (sup_is_commutative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (sup_is_associative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s) c) (And (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) b c) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) (f x) c)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (Finset.fold.{u1, u2} α β (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1)) (instIsCommutativeMaxToMax.{u2} β _inst_1) (instIsAssociativeMaxToMax.{u2} β _inst_1) b f s) c) (And (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) b c) (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) (f x) c)))
Case conversion may be inaccurate. Consider using '#align finset.fold_max_lt Finset.fold_max_ltₓ'. -/
theorem fold_max_lt : s.fold max b f < c ↔ b < c ∧ ∀ x ∈ s, f x < c :=
  by
  show _ > _ ↔ _
  apply fold_op_rel_iff_and
  intro x y z
  show _ < _ ↔ _
  exact max_lt_iff
#align finset.fold_max_lt Finset.fold_max_lt

/- warning: finset.lt_fold_max -> Finset.lt_fold_max is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (Finset.fold.{u1, u2} α β (LinearOrder.max.{u2} β _inst_1) (sup_is_commutative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) (sup_is_associative.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))) b f s)) (Or (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c b) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))) c (f x)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} {b : β} {s : Finset.{u1} α} [_inst_1 : LinearOrder.{u2} β] (c : β), Iff (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (Finset.fold.{u1, u2} α β (Max.max.{u2} β (LinearOrder.toMax.{u2} β _inst_1)) (instIsCommutativeMaxToMax.{u2} β _inst_1) (instIsAssociativeMaxToMax.{u2} β _inst_1) b f s)) (Or (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c b) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) c (f x)))))
Case conversion may be inaccurate. Consider using '#align finset.lt_fold_max Finset.lt_fold_maxₓ'. -/
theorem lt_fold_max : c < s.fold max b f ↔ c < b ∨ ∃ x ∈ s, c < f x :=
  fold_op_rel_iff_or fun x y z => lt_max_iff
#align finset.lt_fold_max Finset.lt_fold_max

/- warning: finset.fold_max_add -> Finset.fold_max_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_1 : LinearOrder.{u2} β] [_inst_2 : Add.{u2} β] [_inst_3 : CovariantClass.{u2, u2} β β (Function.swap.{succ u2, succ u2, succ u2} β β (fun (ᾰ : β) (ᾰ : β) => β) (HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_2))) (LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_1))))))] (n : WithBot.{u2} β) (s : Finset.{u1} α), Eq.{succ u2} (WithBot.{u2} β) (Finset.fold.{u1, u2} α (WithBot.{u2} β) (LinearOrder.max.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (sup_is_commutative.{u2} (WithBot.{u2} β) (Lattice.toSemilatticeSup.{u2} (WithBot.{u2} β) (WithBot.lattice.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (sup_is_associative.{u2} (WithBot.{u2} β) (Lattice.toSemilatticeSup.{u2} (WithBot.{u2} β) (WithBot.lattice.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (Bot.bot.{u2} (WithBot.{u2} β) (WithBot.hasBot.{u2} β)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} β) (WithBot.{u2} β) (WithBot.{u2} β) (instHAdd.{u2} (WithBot.{u2} β) (WithBot.hasAdd.{u2} β _inst_2)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (WithBot.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (WithBot.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (WithBot.{u2} β) (WithBot.hasCoeT.{u2} β))) (f x)) n) s) (HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} β) (WithBot.{u2} β) (WithBot.{u2} β) (instHAdd.{u2} (WithBot.{u2} β) (WithBot.hasAdd.{u2} β _inst_2)) (Finset.fold.{u1, u2} α (WithBot.{u2} β) (LinearOrder.max.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (sup_is_commutative.{u2} (WithBot.{u2} β) (Lattice.toSemilatticeSup.{u2} (WithBot.{u2} β) (WithBot.lattice.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (sup_is_associative.{u2} (WithBot.{u2} β) (Lattice.toSemilatticeSup.{u2} (WithBot.{u2} β) (WithBot.lattice.{u2} β (LinearOrder.toLattice.{u2} β _inst_1)))) (Bot.bot.{u2} (WithBot.{u2} β) (WithBot.hasBot.{u2} β)) (Function.comp.{succ u1, succ u2, succ u2} α β (WithBot.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) β (WithBot.{u2} β) (HasLiftT.mk.{succ u2, succ u2} β (WithBot.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} β (WithBot.{u2} β) (WithBot.hasCoeT.{u2} β)))) f) s) n)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} [_inst_1 : LinearOrder.{u2} β] [_inst_2 : Add.{u2} β] [_inst_3 : CovariantClass.{u2, u2} β β (Function.swap.{succ u2, succ u2, succ u2} β β (fun (ᾰ : β) (ᾰ : β) => β) (fun (x._@.Mathlib.Data.Finset.Fold._hyg.3745 : β) (x._@.Mathlib.Data.Finset.Fold._hyg.3747 : β) => HAdd.hAdd.{u2, u2, u2} β β β (instHAdd.{u2} β _inst_2) x._@.Mathlib.Data.Finset.Fold._hyg.3745 x._@.Mathlib.Data.Finset.Fold._hyg.3747)) (fun (x._@.Mathlib.Data.Finset.Fold._hyg.3760 : β) (x._@.Mathlib.Data.Finset.Fold._hyg.3762 : β) => LE.le.{u2} β (Preorder.toLE.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_1)))))) x._@.Mathlib.Data.Finset.Fold._hyg.3760 x._@.Mathlib.Data.Finset.Fold._hyg.3762)] (n : WithBot.{u2} β) (s : Finset.{u1} α), Eq.{succ u2} (WithBot.{u2} β) (Finset.fold.{u1, u2} α (WithBot.{u2} β) (Max.max.{u2} (WithBot.{u2} β) (LinearOrder.toMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1))) (instIsCommutativeMaxToMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (instIsAssociativeMaxToMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (Bot.bot.{u2} (WithBot.{u2} β) (WithBot.bot.{u2} β)) (fun (x : α) => HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} β) (WithBot.{u2} β) (WithBot.{u2} β) (instHAdd.{u2} (WithBot.{u2} β) (WithBot.add.{u2} β _inst_2)) (WithBot.some.{u2} β (f x)) n) s) (HAdd.hAdd.{u2, u2, u2} (WithBot.{u2} β) (WithBot.{u2} β) (WithBot.{u2} β) (instHAdd.{u2} (WithBot.{u2} β) (WithBot.add.{u2} β _inst_2)) (Finset.fold.{u1, u2} α (WithBot.{u2} β) (Max.max.{u2} (WithBot.{u2} β) (LinearOrder.toMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1))) (instIsCommutativeMaxToMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (instIsAssociativeMaxToMax.{u2} (WithBot.{u2} β) (WithBot.linearOrder.{u2} β _inst_1)) (Bot.bot.{u2} (WithBot.{u2} β) (WithBot.bot.{u2} β)) (Function.comp.{succ u1, succ u2, succ u2} α β (WithBot.{u2} β) (WithBot.some.{u2} β) f) s) n)
Case conversion may be inaccurate. Consider using '#align finset.fold_max_add Finset.fold_max_addₓ'. -/
theorem fold_max_add [Add β] [CovariantClass β β (Function.swap (· + ·)) (· ≤ ·)] (n : WithBot β)
    (s : Finset α) : (s.fold max ⊥ fun x : α => ↑(f x) + n) = s.fold max ⊥ (coe ∘ f) + n := by
  classical apply s.induction_on <;> simp (config := { contextual := true }) [max_add_add_right]
#align finset.fold_max_add Finset.fold_max_add

end Order

end Fold

end Finset

