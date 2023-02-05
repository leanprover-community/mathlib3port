/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.finset.n_ary
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Prod

/-!
# N-ary images of finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `finset.image₂`, the binary image of finsets. This is the finset version of
`set.image2`. This is mostly useful to define pointwise operations.

## Notes

This file is very similar to `data.set.n_ary`, `order.filter.n_ary` and `data.option.n_ary`. Please
keep them in sync.

We do not define `finset.image₃` as its only purpose would be to prove properties of `finset.image₂`
and `set.image2` already fulfills this task.
-/


open Function Set

namespace Finset

variable {α α' β β' γ γ' δ δ' ε ε' : Type _} [DecidableEq α'] [DecidableEq β'] [DecidableEq γ]
  [DecidableEq γ'] [DecidableEq δ] [DecidableEq δ'] [DecidableEq ε] [DecidableEq ε']
  {f f' : α → β → γ} {g g' : α → β → γ → δ} {s s' : Finset α} {t t' : Finset β} {u u' : Finset γ}
  {a a' : α} {b b' : β} {c : γ}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.image₂ /-
/-- The image of a binary function `f : α → β → γ` as a function `finset α → finset β → finset γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) : Finset γ :=
  (s ×ˢ t).image <| uncurry f
#align finset.image₂ Finset.image₂
-/

/- warning: finset.mem_image₂ -> Finset.mem_image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {c : γ}, Iff (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) c (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u2} β (fun (b : β) => And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (And (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) (Eq.{succ u3} γ (f a b) c)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β} {c : γ}, Iff (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) c (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Exists.{succ u2} α (fun (a : α) => Exists.{succ u1} β (fun (b : β) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) (And (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) (Eq.{succ u3} γ (f a b) c)))))
Case conversion may be inaccurate. Consider using '#align finset.mem_image₂ Finset.mem_image₂ₓ'. -/
@[simp]
theorem mem_image₂ : c ∈ image₂ f s t ↔ ∃ a b, a ∈ s ∧ b ∈ t ∧ f a b = c := by
  simp [image₂, and_assoc']
#align finset.mem_image₂ Finset.mem_image₂

/- warning: finset.coe_image₂ -> Finset.coe_image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] (f : α -> β -> γ) (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u3} (Set.{u3} γ) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Set.image2.{u1, u2, u3} α β γ f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] (f : α -> β -> γ) (s : Finset.{u3} α) (t : Finset.{u2} β), Eq.{succ u1} (Set.{u1} γ) (Finset.toSet.{u1} γ (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Set.image2.{u3, u2, u1} α β γ f (Finset.toSet.{u3} α s) (Finset.toSet.{u2} β t))
Case conversion may be inaccurate. Consider using '#align finset.coe_image₂ Finset.coe_image₂ₓ'. -/
@[simp, norm_cast]
theorem coe_image₂ (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t : Set γ) = Set.image2 f s t :=
  Set.ext fun _ => mem_image₂
#align finset.coe_image₂ Finset.coe_image₂

/- warning: finset.card_image₂_le -> Finset.card_image₂_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] (f : α -> β -> γ) (s : Finset.{u1} α) (t : Finset.{u2} β), LE.le.{0} Nat Nat.hasLe (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] (f : α -> β -> γ) (s : Finset.{u3} α) (t : Finset.{u2} β), LE.le.{0} Nat instLENat (Finset.card.{u1} γ (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u3} α s) (Finset.card.{u2} β t))
Case conversion may be inaccurate. Consider using '#align finset.card_image₂_le Finset.card_image₂_leₓ'. -/
theorem card_image₂_le (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (image₂ f s t).card ≤ s.card * t.card :=
  card_image_le.trans_eq <| card_product _ _
#align finset.card_image₂_le Finset.card_image₂_le

/- warning: finset.card_image₂_iff -> Finset.card_image₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, Iff (Eq.{1} Nat (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t))) (Set.InjOn.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (x : Prod.{u1, u2} α β) => f (Prod.fst.{u1, u2} α β x) (Prod.snd.{u1, u2} α β x)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, Iff (Eq.{1} Nat (Finset.card.{u3} γ (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) (Finset.card.{u1} β t))) (Set.InjOn.{max u2 u1, u3} (Prod.{u2, u1} α β) γ (fun (x : Prod.{u2, u1} α β) => f (Prod.fst.{u2, u1} α β x) (Prod.snd.{u2, u1} α β x)) (Set.prod.{u2, u1} α β (Finset.toSet.{u2} α s) (Finset.toSet.{u1} β t)))
Case conversion may be inaccurate. Consider using '#align finset.card_image₂_iff Finset.card_image₂_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem card_image₂_iff :
    (image₂ f s t).card = s.card * t.card ↔ (s ×ˢ t : Set (α × β)).InjOn fun x => f x.1 x.2 :=
  by
  rw [← card_product, ← coe_product]
  exact card_image_iff
#align finset.card_image₂_iff Finset.card_image₂_iff

/- warning: finset.card_image₂ -> Finset.card_image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ}, (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (forall (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{1} Nat (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ}, (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (forall (s : Finset.{u3} α) (t : Finset.{u2} β), Eq.{1} Nat (Finset.card.{u1} γ (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u3} α s) (Finset.card.{u2} β t)))
Case conversion may be inaccurate. Consider using '#align finset.card_image₂ Finset.card_image₂ₓ'. -/
theorem card_image₂ (hf : Injective2 f) (s : Finset α) (t : Finset β) :
    (image₂ f s t).card = s.card * t.card :=
  (card_image_of_injective _ hf.uncurry).trans <| card_product _ _
#align finset.card_image₂ Finset.card_image₂

/- warning: finset.mem_image₂_of_mem -> Finset.mem_image₂_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (f a b) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {a : α} {b : β}, (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) -> (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b t) -> (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (f a b) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t))
Case conversion may be inaccurate. Consider using '#align finset.mem_image₂_of_mem Finset.mem_image₂_of_memₓ'. -/
theorem mem_image₂_of_mem (ha : a ∈ s) (hb : b ∈ t) : f a b ∈ image₂ f s t :=
  mem_image₂.2 ⟨a, b, ha, hb, rfl⟩
#align finset.mem_image₂_of_mem Finset.mem_image₂_of_mem

/- warning: finset.mem_image₂_iff -> Finset.mem_image₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {a : α} {b : β}, (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Iff (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (f a b) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {a : α} {b : β}, (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (Iff (Membership.mem.{u1, u1} γ (Finset.{u1} γ) (Finset.instMembershipFinset.{u1} γ) (f a b) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (And (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b t)))
Case conversion may be inaccurate. Consider using '#align finset.mem_image₂_iff Finset.mem_image₂_iffₓ'. -/
theorem mem_image₂_iff (hf : Injective2 f) : f a b ∈ image₂ f s t ↔ a ∈ s ∧ b ∈ t := by
  rw [← mem_coe, coe_image₂, mem_image2_iff hf, mem_coe, mem_coe]
#align finset.mem_image₂_iff Finset.mem_image₂_iff

/- warning: finset.image₂_subset -> Finset.image₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t'))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {s' : Finset.{u3} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, (HasSubset.Subset.{u3} (Finset.{u3} α) (Finset.instHasSubsetFinset.{u3} α) s s') -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.instHasSubsetFinset.{u2} β) t t') -> (HasSubset.Subset.{u1} (Finset.{u1} γ) (Finset.instHasSubsetFinset.{u1} γ) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t'))
Case conversion may be inaccurate. Consider using '#align finset.image₂_subset Finset.image₂_subsetₓ'. -/
theorem image₂_subset (hs : s ⊆ s') (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s' t' :=
  by
  rw [← coe_subset, coe_image₂, coe_image₂]
  exact image2_subset hs ht
#align finset.image₂_subset Finset.image₂_subset

/- warning: finset.image₂_subset_left -> Finset.image₂_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {t' : Finset.{u3} β}, (HasSubset.Subset.{u3} (Finset.{u3} β) (Finset.instHasSubsetFinset.{u3} β) t t') -> (HasSubset.Subset.{u2} (Finset.{u2} γ) (Finset.instHasSubsetFinset.{u2} γ) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
Case conversion may be inaccurate. Consider using '#align finset.image₂_subset_left Finset.image₂_subset_leftₓ'. -/
theorem image₂_subset_left (ht : t ⊆ t') : image₂ f s t ⊆ image₂ f s t' :=
  image₂_subset Subset.rfl ht
#align finset.image₂_subset_left Finset.image₂_subset_left

/- warning: finset.image₂_subset_right -> Finset.image₂_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {s' : Finset.{u3} α} {t : Finset.{u1} β}, (HasSubset.Subset.{u3} (Finset.{u3} α) (Finset.instHasSubsetFinset.{u3} α) s s') -> (HasSubset.Subset.{u2} (Finset.{u2} γ) (Finset.instHasSubsetFinset.{u2} γ) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_subset_right Finset.image₂_subset_rightₓ'. -/
theorem image₂_subset_right (hs : s ⊆ s') : image₂ f s t ⊆ image₂ f s' t :=
  image₂_subset hs Subset.rfl
#align finset.image₂_subset_right Finset.image₂_subset_right

/- warning: finset.image_subset_image₂_left -> Finset.image_subset_image₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {b : β}, (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image.{u1, u3} α γ (fun (a : α) => f a b) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {b : β}, (Membership.mem.{u3, u3} β (Finset.{u3} β) (Finset.instMembershipFinset.{u3} β) b t) -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet.{u2} γ) (Set.image.{u1, u2} α γ (fun (a : α) => f a b) (Finset.toSet.{u1} α s)) (Finset.toSet.{u2} γ (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_image₂_left Finset.image_subset_image₂_leftₓ'. -/
theorem image_subset_image₂_left (hb : b ∈ t) : (fun a => f a b) '' s ⊆ image₂ f s t :=
  ball_image_of_ball fun a ha => mem_image₂_of_mem ha hb
#align finset.image_subset_image₂_left Finset.image_subset_image₂_left

/- warning: finset.image_subset_image₂_right -> Finset.image_subset_image₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {a : α}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) (Set.image.{u2, u3} β γ (f a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t)) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u1} β} {a : α}, (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) -> (HasSubset.Subset.{u2} (Set.{u2} γ) (Set.instHasSubsetSet.{u2} γ) (Set.image.{u1, u2} β γ (f a) (Finset.toSet.{u1} β t)) (Finset.toSet.{u2} γ (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
Case conversion may be inaccurate. Consider using '#align finset.image_subset_image₂_right Finset.image_subset_image₂_rightₓ'. -/
theorem image_subset_image₂_right (ha : a ∈ s) : f a '' t ⊆ image₂ f s t :=
  ball_image_of_ball fun b => mem_image₂_of_mem ha
#align finset.image_subset_image₂_right Finset.image_subset_image₂_right

/- warning: finset.forall_image₂_iff -> Finset.forall_image₂_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {p : γ -> Prop}, Iff (forall (z : γ), (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) z (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (p z)) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y t) -> (p (f x y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β} {p : γ -> Prop}, Iff (forall (z : γ), (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) z (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (p z)) (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y t) -> (p (f x y))))
Case conversion may be inaccurate. Consider using '#align finset.forall_image₂_iff Finset.forall_image₂_iffₓ'. -/
theorem forall_image₂_iff {p : γ → Prop} :
    (∀ z ∈ image₂ f s t, p z) ↔ ∀ x ∈ s, ∀ y ∈ t, p (f x y) := by
  simp_rw [← mem_coe, coe_image₂, forall_image2_iff]
#align finset.forall_image₂_iff Finset.forall_image₂_iff

/- warning: finset.image₂_subset_iff -> Finset.image₂_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {u : Finset.{u3} γ}, Iff (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) u) (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) y t) -> (Membership.Mem.{u3, u3} γ (Finset.{u3} γ) (Finset.hasMem.{u3} γ) (f x y) u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β} {u : Finset.{u3} γ}, Iff (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.instHasSubsetFinset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) u) (forall (x : α), (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) y t) -> (Membership.mem.{u3, u3} γ (Finset.{u3} γ) (Finset.instMembershipFinset.{u3} γ) (f x y) u)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_subset_iff Finset.image₂_subset_iffₓ'. -/
@[simp]
theorem image₂_subset_iff : image₂ f s t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, f x y ∈ u :=
  forall_image₂_iff
#align finset.image₂_subset_iff Finset.image₂_subset_iff

/- warning: finset.image₂_nonempty_iff -> Finset.image₂_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, Iff (Finset.Nonempty.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (And (Finset.Nonempty.{u1} α s) (Finset.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, Iff (Finset.Nonempty.{u3} γ (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (And (Finset.Nonempty.{u2} α s) (Finset.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_nonempty_iff Finset.image₂_nonempty_iffₓ'. -/
@[simp]
theorem image₂_nonempty_iff : (image₂ f s t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  by
  rw [← coe_nonempty, coe_image₂]
  exact image2_nonempty_iff
#align finset.image₂_nonempty_iff Finset.image₂_nonempty_iff

/- warning: finset.nonempty.image₂ -> Finset.Nonempty.image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u3} α s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{u1} γ (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.image₂ Finset.Nonempty.image₂ₓ'. -/
theorem Nonempty.image₂ (hs : s.Nonempty) (ht : t.Nonempty) : (image₂ f s t).Nonempty :=
  image₂_nonempty_iff.2 ⟨hs, ht⟩
#align finset.nonempty.image₂ Finset.Nonempty.image₂

/- warning: finset.nonempty.of_image₂_left -> Finset.Nonempty.of_image₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (Finset.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{u3} γ (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (Finset.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.of_image₂_left Finset.Nonempty.of_image₂_leftₓ'. -/
theorem Nonempty.of_image₂_left (h : (image₂ f s t).Nonempty) : s.Nonempty :=
  (image₂_nonempty_iff.1 h).1
#align finset.nonempty.of_image₂_left Finset.Nonempty.of_image₂_left

/- warning: finset.nonempty.of_image₂_right -> Finset.Nonempty.of_image₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (Finset.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{u3} γ (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) -> (Finset.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.of_image₂_right Finset.Nonempty.of_image₂_rightₓ'. -/
theorem Nonempty.of_image₂_right (h : (image₂ f s t).Nonempty) : t.Nonempty :=
  (image₂_nonempty_iff.1 h).2
#align finset.nonempty.of_image₂_right Finset.Nonempty.of_image₂_right

/- warning: finset.image₂_empty_left -> Finset.image₂_empty_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u2} β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α)) t) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.hasEmptyc.{u3} γ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u1} β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α)) t) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.instEmptyCollectionFinset.{u3} γ))
Case conversion may be inaccurate. Consider using '#align finset.image₂_empty_left Finset.image₂_empty_leftₓ'. -/
@[simp]
theorem image₂_empty_left : image₂ f ∅ t = ∅ :=
  coe_injective <| by simp
#align finset.image₂_empty_left Finset.image₂_empty_left

/- warning: finset.image₂_empty_right -> Finset.image₂_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.hasEmptyc.{u3} γ))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.instEmptyCollectionFinset.{u3} γ))
Case conversion may be inaccurate. Consider using '#align finset.image₂_empty_right Finset.image₂_empty_rightₓ'. -/
@[simp]
theorem image₂_empty_right : image₂ f s ∅ = ∅ :=
  coe_injective <| by simp
#align finset.image₂_empty_right Finset.image₂_empty_right

/- warning: finset.image₂_eq_empty_iff -> Finset.image₂_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, Iff (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.hasEmptyc.{u3} γ))) (Or (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Eq.{succ u2} (Finset.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, Iff (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (EmptyCollection.emptyCollection.{u3} (Finset.{u3} γ) (Finset.instEmptyCollectionFinset.{u3} γ))) (Or (Eq.{succ u2} (Finset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (Eq.{succ u1} (Finset.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))))
Case conversion may be inaccurate. Consider using '#align finset.image₂_eq_empty_iff Finset.image₂_eq_empty_iffₓ'. -/
@[simp]
theorem image₂_eq_empty_iff : image₂ f s t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp_rw [← not_nonempty_iff_eq_empty, image₂_nonempty_iff, not_and_or]
#align finset.image₂_eq_empty_iff Finset.image₂_eq_empty_iff

/- warning: finset.image₂_singleton_left -> Finset.image₂_singleton_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u2} β} {a : α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (b : β) => f a b) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u1} β} {a : α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a) t) (Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (b : β) => f a b) t)
Case conversion may be inaccurate. Consider using '#align finset.image₂_singleton_left Finset.image₂_singleton_leftₓ'. -/
@[simp]
theorem image₂_singleton_left : image₂ f {a} t = t.image fun b => f a b :=
  ext fun x => by simp
#align finset.image₂_singleton_left Finset.image₂_singleton_left

/- warning: finset.image₂_singleton_right -> Finset.image₂_singleton_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {b : β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Finset.image.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (a : α) => f a b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {b : β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Finset.image.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (a : α) => f a b) s)
Case conversion may be inaccurate. Consider using '#align finset.image₂_singleton_right Finset.image₂_singleton_rightₓ'. -/
@[simp]
theorem image₂_singleton_right : image₂ f s {b} = s.image fun a => f a b :=
  ext fun x => by simp
#align finset.image₂_singleton_right Finset.image₂_singleton_right

/- warning: finset.image₂_singleton_left' -> Finset.image₂_singleton_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u2} β} {a : α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (f a) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {t : Finset.{u1} β} {a : α}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a) t) (Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (f a) t)
Case conversion may be inaccurate. Consider using '#align finset.image₂_singleton_left' Finset.image₂_singleton_left'ₓ'. -/
theorem image₂_singleton_left' : image₂ f {a} t = t.image (f a) :=
  image₂_singleton_left
#align finset.image₂_singleton_left' Finset.image₂_singleton_left'

/- warning: finset.image₂_singleton -> Finset.image₂_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Singleton.singleton.{u3, u3} γ (Finset.{u3} γ) (Finset.hasSingleton.{u3} γ) (f a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {a : α} {b : β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Singleton.singleton.{u3, u3} γ (Finset.{u3} γ) (Finset.instSingletonFinset.{u3} γ) (f a b))
Case conversion may be inaccurate. Consider using '#align finset.image₂_singleton Finset.image₂_singletonₓ'. -/
theorem image₂_singleton : image₂ f {a} {b} = {f a b} := by simp
#align finset.image₂_singleton Finset.image₂_singleton

/- warning: finset.image₂_union_left -> Finset.image₂_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u1} α], Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Union.union.{u3} (Finset.{u3} γ) (Finset.hasUnion.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {s' : Finset.{u3} α} {t : Finset.{u1} β} [_inst_9 : DecidableEq.{succ u3} α], Eq.{succ u2} (Finset.{u2} γ) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Union.union.{u3} (Finset.{u3} α) (Finset.instUnionFinset.{u3} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Union.union.{u2} (Finset.{u2} γ) (Finset.instUnionFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_union_left Finset.image₂_union_leftₓ'. -/
theorem image₂_union_left [DecidableEq α] : image₂ f (s ∪ s') t = image₂ f s t ∪ image₂ f s' t :=
  coe_injective <| by
    push_cast
    exact image2_union_left
#align finset.image₂_union_left Finset.image₂_union_left

/- warning: finset.image₂_union_right -> Finset.image₂_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u2} β], Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Union.union.{u3} (Finset.{u3} γ) (Finset.hasUnion.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {t' : Finset.{u3} β} [_inst_9 : DecidableEq.{succ u3} β], Eq.{succ u2} (Finset.{u2} γ) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Union.union.{u3} (Finset.{u3} β) (Finset.instUnionFinset.{u3} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Union.union.{u2} (Finset.{u2} γ) (Finset.instUnionFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
Case conversion may be inaccurate. Consider using '#align finset.image₂_union_right Finset.image₂_union_rightₓ'. -/
theorem image₂_union_right [DecidableEq β] : image₂ f s (t ∪ t') = image₂ f s t ∪ image₂ f s t' :=
  coe_injective <| by
    push_cast
    exact image2_union_right
#align finset.image₂_union_right Finset.image₂_union_right

/- warning: finset.image₂_inter_left -> Finset.image₂_inter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u1} α], (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {s' : Finset.{u3} α} {t : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u3} α], (Function.Injective2.{succ u3, succ u2, succ u1} α β γ f) -> (Eq.{succ u1} (Finset.{u1} γ) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u3} (Finset.{u3} α) (Finset.instInterFinset.{u3} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Inter.inter.{u1} (Finset.{u1} γ) (Finset.instInterFinset.{u1} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_inter_left Finset.image₂_inter_leftₓ'. -/
theorem image₂_inter_left [DecidableEq α] (hf : Injective2 f) :
    image₂ f (s ∩ s') t = image₂ f s t ∩ image₂ f s' t :=
  coe_injective <| by
    push_cast
    exact image2_inter_left hf
#align finset.image₂_inter_left Finset.image₂_inter_left

/- warning: finset.image₂_inter_right -> Finset.image₂_inter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u2} β], (Function.Injective2.{succ u1, succ u2, succ u3} α β γ f) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t')))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u3} β} {t' : Finset.{u3} β} [_inst_9 : DecidableEq.{succ u3} β], (Function.Injective2.{succ u2, succ u3, succ u1} α β γ f) -> (Eq.{succ u1} (Finset.{u1} γ) (Finset.image₂.{u2, u3, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Inter.inter.{u3} (Finset.{u3} β) (Finset.instInterFinset.{u3} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Inter.inter.{u1} (Finset.{u1} γ) (Finset.instInterFinset.{u1} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u2, u3, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u2, u3, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t')))
Case conversion may be inaccurate. Consider using '#align finset.image₂_inter_right Finset.image₂_inter_rightₓ'. -/
theorem image₂_inter_right [DecidableEq β] (hf : Injective2 f) :
    image₂ f s (t ∩ t') = image₂ f s t ∩ image₂ f s t' :=
  coe_injective <| by
    push_cast
    exact image2_inter_right hf
#align finset.image₂_inter_right Finset.image₂_inter_right

/- warning: finset.image₂_inter_subset_left -> Finset.image₂_inter_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u1} α], HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u3} α} {s' : Finset.{u3} α} {t : Finset.{u1} β} [_inst_9 : DecidableEq.{succ u3} α], HasSubset.Subset.{u2} (Finset.{u2} γ) (Finset.instHasSubsetFinset.{u2} γ) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u3} (Finset.{u3} α) (Finset.instInterFinset.{u3} α (fun (a : α) (b : α) => _inst_9 a b)) s s') t) (Inter.inter.{u2} (Finset.{u2} γ) (Finset.instInterFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_inter_subset_left Finset.image₂_inter_subset_leftₓ'. -/
theorem image₂_inter_subset_left [DecidableEq α] :
    image₂ f (s ∩ s') t ⊆ image₂ f s t ∩ image₂ f s' t :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_left
#align finset.image₂_inter_subset_left Finset.image₂_inter_subset_left

/- warning: finset.image₂_inter_subset_right -> Finset.image₂_inter_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u2} β], HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {t' : Finset.{u3} β} [_inst_9 : DecidableEq.{succ u3} β], HasSubset.Subset.{u2} (Finset.{u2} γ) (Finset.instHasSubsetFinset.{u2} γ) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Inter.inter.{u3} (Finset.{u3} β) (Finset.instInterFinset.{u3} β (fun (a : β) (b : β) => _inst_9 a b)) t t')) (Inter.inter.{u2} (Finset.{u2} γ) (Finset.instInterFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t'))
Case conversion may be inaccurate. Consider using '#align finset.image₂_inter_subset_right Finset.image₂_inter_subset_rightₓ'. -/
theorem image₂_inter_subset_right [DecidableEq β] :
    image₂ f s (t ∩ t') ⊆ image₂ f s t ∩ image₂ f s t' :=
  coe_subset.1 <| by
    push_cast
    exact image2_inter_subset_right
#align finset.image₂_inter_subset_right Finset.image₂_inter_subset_right

/- warning: finset.image₂_congr -> Finset.image₂_congr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {f' : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (forall (b : β), (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Eq.{succ u3} γ (f a b) (f' a b)))) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f' s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {f' : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β}, (forall (a : α), (Membership.mem.{u3, u3} α (Finset.{u3} α) (Finset.instMembershipFinset.{u3} α) a s) -> (forall (b : β), (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) b t) -> (Eq.{succ u1} γ (f a b) (f' a b)))) -> (Eq.{succ u1} (Finset.{u1} γ) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f' s t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_congr Finset.image₂_congrₓ'. -/
theorem image₂_congr (h : ∀ a ∈ s, ∀ b ∈ t, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  coe_injective <| by
    push_cast
    exact image2_congr h
#align finset.image₂_congr Finset.image₂_congr

/- warning: finset.image₂_congr' -> Finset.image₂_congr' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {f' : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (f' a b)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f' s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {f' : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (f' a b)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f' s t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_congr' Finset.image₂_congr'ₓ'. -/
/-- A common special case of `image₂_congr` -/
theorem image₂_congr' (h : ∀ a b, f a b = f' a b) : image₂ f s t = image₂ f' s t :=
  image₂_congr fun a _ b _ => h a b
#align finset.image₂_congr' Finset.image₂_congr'

/- warning: finset.subset_image₂ -> Finset.subset_image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {u : Finset.{u3} γ} {s : Set.{u1} α} {t : Set.{u2} β}, (HasSubset.Subset.{u3} (Set.{u3} γ) (Set.hasSubset.{u3} γ) ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (Finset.{u3} γ) (Set.{u3} γ) (HasLiftT.mk.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (CoeTCₓ.coe.{succ u3, succ u3} (Finset.{u3} γ) (Set.{u3} γ) (Finset.Set.hasCoeT.{u3} γ))) u) (Set.image2.{u1, u2, u3} α β γ f s t)) -> (Exists.{succ u1} (Finset.{u1} α) (fun (s' : Finset.{u1} α) => Exists.{succ u2} (Finset.{u2} β) (fun (t' : Finset.{u2} β) => And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s') s) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t') t) (HasSubset.Subset.{u3} (Finset.{u3} γ) (Finset.hasSubset.{u3} γ) u (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t'))))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} {u : Finset.{u1} γ} {s : Set.{u3} α} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} γ) (Set.instHasSubsetSet.{u1} γ) (Finset.toSet.{u1} γ u) (Set.image2.{u3, u2, u1} α β γ f s t)) -> (Exists.{succ u3} (Finset.{u3} α) (fun (s' : Finset.{u3} α) => Exists.{succ u2} (Finset.{u2} β) (fun (t' : Finset.{u2} β) => And (HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (Finset.toSet.{u3} α s') s) (And (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Finset.toSet.{u2} β t') t) (HasSubset.Subset.{u1} (Finset.{u1} γ) (Finset.instHasSubsetFinset.{u1} γ) u (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s' t'))))))
Case conversion may be inaccurate. Consider using '#align finset.subset_image₂ Finset.subset_image₂ₓ'. -/
theorem subset_image₂ {s : Set α} {t : Set β} (hu : ↑u ⊆ image2 f s t) :
    ∃ (s' : Finset α)(t' : Finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ image₂ f s' t' :=
  by
  apply Finset.induction_on' u
  · exact ⟨∅, ∅, Set.empty_subset _, Set.empty_subset _, empty_subset _⟩
  rintro a u ha _ _ ⟨s', t', hs, hs', h⟩
  obtain ⟨x, y, hx, hy, ha⟩ := hu ha
  haveI := Classical.decEq α
  haveI := Classical.decEq β
  refine' ⟨insert x s', insert y t', _⟩
  simp_rw [coe_insert, Set.insert_subset]
  exact
    ⟨⟨hx, hs⟩, ⟨hy, hs'⟩,
      insert_subset.2
        ⟨mem_image₂.2 ⟨x, y, mem_insert_self _ _, mem_insert_self _ _, ha⟩,
          h.trans <| image₂_subset (subset_insert _ _) <| subset_insert _ _⟩⟩
#align finset.subset_image₂ Finset.subset_image₂

variable (s t)

/- warning: finset.card_image₂_singleton_left -> Finset.card_image₂_singleton_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} (t : Finset.{u2} β) {a : α}, (Function.Injective.{succ u2, succ u3} β γ (f a)) -> (Eq.{1} Nat (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t)) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} (t : Finset.{u3} β) {a : α}, (Function.Injective.{succ u3, succ u2} β γ (f a)) -> (Eq.{1} Nat (Finset.card.{u2} γ (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t)) (Finset.card.{u3} β t))
Case conversion may be inaccurate. Consider using '#align finset.card_image₂_singleton_left Finset.card_image₂_singleton_leftₓ'. -/
theorem card_image₂_singleton_left (hf : Injective (f a)) : (image₂ f {a} t).card = t.card := by
  rw [image₂_singleton_left, card_image_of_injective _ hf]
#align finset.card_image₂_singleton_left Finset.card_image₂_singleton_left

/- warning: finset.card_image₂_singleton_right -> Finset.card_image₂_singleton_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} (s : Finset.{u1} α) {b : β}, (Function.Injective.{succ u1, succ u3} α γ (fun (a : α) => f a b)) -> (Eq.{1} Nat (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b))) (Finset.card.{u1} α s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} (s : Finset.{u3} α) {b : β}, (Function.Injective.{succ u3, succ u2} α γ (fun (a : α) => f a b)) -> (Eq.{1} Nat (Finset.card.{u2} γ (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b))) (Finset.card.{u3} α s))
Case conversion may be inaccurate. Consider using '#align finset.card_image₂_singleton_right Finset.card_image₂_singleton_rightₓ'. -/
theorem card_image₂_singleton_right (hf : Injective fun a => f a b) :
    (image₂ f s {b}).card = s.card := by rw [image₂_singleton_right, card_image_of_injective _ hf]
#align finset.card_image₂_singleton_right Finset.card_image₂_singleton_right

/- warning: finset.image₂_singleton_inter -> Finset.image₂_singleton_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {a : α} [_inst_9 : DecidableEq.{succ u2} β] (t₁ : Finset.{u2} β) (t₂ : Finset.{u2} β), (Function.Injective.{succ u2, succ u3} β γ (f a)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_9 a b)) t₁ t₂)) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t₁) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t₂)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {a : α} [_inst_9 : DecidableEq.{succ u3} β] (t₁ : Finset.{u3} β) (t₂ : Finset.{u3} β), (Function.Injective.{succ u3, succ u2} β γ (f a)) -> (Eq.{succ u2} (Finset.{u2} γ) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) (Inter.inter.{u3} (Finset.{u3} β) (Finset.instInterFinset.{u3} β (fun (a : β) (b : β) => _inst_9 a b)) t₁ t₂)) (Inter.inter.{u2} (Finset.{u2} γ) (Finset.instInterFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t₁) (Finset.image₂.{u1, u3, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) t₂)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_singleton_inter Finset.image₂_singleton_interₓ'. -/
theorem image₂_singleton_inter [DecidableEq β] (t₁ t₂ : Finset β) (hf : Injective (f a)) :
    image₂ f {a} (t₁ ∩ t₂) = image₂ f {a} t₁ ∩ image₂ f {a} t₂ := by
  simp_rw [image₂_singleton_left, image_inter _ _ hf]
#align finset.image₂_singleton_inter Finset.image₂_singleton_inter

/- warning: finset.image₂_inter_singleton -> Finset.image₂_inter_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {b : β} [_inst_9 : DecidableEq.{succ u1} α] (s₁ : Finset.{u1} α) (s₂ : Finset.{u1} α), (Function.Injective.{succ u1, succ u3} α γ (fun (a : α) => f a b)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_9 a b)) s₁ s₂) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Inter.inter.{u3} (Finset.{u3} γ) (Finset.hasInter.{u3} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s₁ (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s₂ (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_3 : DecidableEq.{succ u2} γ] {f : α -> β -> γ} {b : β} [_inst_9 : DecidableEq.{succ u3} α] (s₁ : Finset.{u3} α) (s₂ : Finset.{u3} α), (Function.Injective.{succ u3, succ u2} α γ (fun (a : α) => f a b)) -> (Eq.{succ u2} (Finset.{u2} γ) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Inter.inter.{u3} (Finset.{u3} α) (Finset.instInterFinset.{u3} α (fun (a : α) (b : α) => _inst_9 a b)) s₁ s₂) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Inter.inter.{u2} (Finset.{u2} γ) (Finset.instInterFinset.{u2} γ (fun (a : γ) (b : γ) => _inst_3 a b)) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s₁ (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Finset.image₂.{u3, u1, u2} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s₂ (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b))))
Case conversion may be inaccurate. Consider using '#align finset.image₂_inter_singleton Finset.image₂_inter_singletonₓ'. -/
theorem image₂_inter_singleton [DecidableEq α] (s₁ s₂ : Finset α) (hf : Injective fun a => f a b) :
    image₂ f (s₁ ∩ s₂) {b} = image₂ f s₁ {b} ∩ image₂ f s₂ {b} := by
  simp_rw [image₂_singleton_right, image_inter _ _ hf]
#align finset.image₂_inter_singleton Finset.image₂_inter_singleton

/- warning: finset.card_le_card_image₂_left -> Finset.card_le_card_image₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} (t : Finset.{u2} β) {s : Finset.{u1} α}, (Finset.Nonempty.{u1} α s) -> (forall (a : α), Function.Injective.{succ u2, succ u3} β γ (f a)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u2} β t) (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} (t : Finset.{u2} β) {s : Finset.{u3} α}, (Finset.Nonempty.{u3} α s) -> (forall (a : α), Function.Injective.{succ u2, succ u1} β γ (f a)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} β t) (Finset.card.{u1} γ (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_image₂_left Finset.card_le_card_image₂_leftₓ'. -/
theorem card_le_card_image₂_left {s : Finset α} (hs : s.Nonempty) (hf : ∀ a, Injective (f a)) :
    t.card ≤ (image₂ f s t).card := by
  obtain ⟨a, ha⟩ := hs
  rw [← card_image₂_singleton_left _ (hf a)]
  exact card_le_of_subset (image₂_subset_right <| singleton_subset_iff.2 ha)
#align finset.card_le_card_image₂_left Finset.card_le_card_image₂_left

/- warning: finset.card_le_card_image₂_right -> Finset.card_le_card_image₂_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} (s : Finset.{u1} α) {t : Finset.{u2} β}, (Finset.Nonempty.{u2} β t) -> (forall (b : β), Function.Injective.{succ u1, succ u3} α γ (fun (a : α) => f a b)) -> (LE.le.{0} Nat Nat.hasLe (Finset.card.{u1} α s) (Finset.card.{u3} γ (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] {f : α -> β -> γ} (s : Finset.{u2} α) {t : Finset.{u3} β}, (Finset.Nonempty.{u3} β t) -> (forall (b : β), Function.Injective.{succ u2, succ u1} α γ (fun (a : α) => f a b)) -> (LE.le.{0} Nat instLENat (Finset.card.{u2} α s) (Finset.card.{u1} γ (Finset.image₂.{u2, u3, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)))
Case conversion may be inaccurate. Consider using '#align finset.card_le_card_image₂_right Finset.card_le_card_image₂_rightₓ'. -/
theorem card_le_card_image₂_right {t : Finset β} (ht : t.Nonempty)
    (hf : ∀ b, Injective fun a => f a b) : s.card ≤ (image₂ f s t).card :=
  by
  obtain ⟨b, hb⟩ := ht
  rw [← card_image₂_singleton_right _ (hf b)]
  exact card_le_of_subset (image₂_subset_left <| singleton_subset_iff.2 hb)
#align finset.card_le_card_image₂_right Finset.card_le_card_image₂_right

variable {s t}

/- warning: finset.bUnion_image_left -> Finset.bunionᵢ_image_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_3 a b) s (fun (a : α) => Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (f a) t)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β}, Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_3 a b) s (fun (a : α) => Finset.image.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) (f a) t)) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)
Case conversion may be inaccurate. Consider using '#align finset.bUnion_image_left Finset.bunionᵢ_image_leftₓ'. -/
theorem bunionᵢ_image_left : (s.bunionᵢ fun a => t.image <| f a) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.unionᵢ_image_left _
#align finset.bUnion_image_left Finset.bunionᵢ_image_left

#print Finset.bunionᵢ_image_right /-
theorem bunionᵢ_image_right : (t.bunionᵢ fun b => s.image fun a => f a b) = image₂ f s t :=
  coe_injective <| by
    push_cast
    exact Set.unionᵢ_image_right _
#align finset.bUnion_image_right Finset.bunionᵢ_image_right
-/

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `finset.image₂` of those operations.

The proof pattern is `image₂_lemma operation_lemma`. For example, `image₂_comm mul_comm` proves that
`image₂ (*) f g = image₂ (*) g f` in a `comm_semigroup`.
-/


/- warning: finset.image_image₂ -> Finset.image_image₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_3 : DecidableEq.{succ u3} γ] [_inst_5 : DecidableEq.{succ u4} δ] {s : Finset.{u1} α} {t : Finset.{u2} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u4} (Finset.{u4} δ) (Finset.image.{u3, u4} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u1, u2, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) (fun (a : α) (b : β) => g (f a b)) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_3 : DecidableEq.{succ u3} γ] [_inst_5 : DecidableEq.{succ u4} δ] {s : Finset.{u2} α} {t : Finset.{u1} β} (f : α -> β -> γ) (g : γ -> δ), Eq.{succ u4} (Finset.{u4} δ) (Finset.image.{u3, u4} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u1, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) (fun (a : α) (b : β) => g (f a b)) s t)
Case conversion may be inaccurate. Consider using '#align finset.image_image₂ Finset.image_image₂ₓ'. -/
theorem image_image₂ (f : α → β → γ) (g : γ → δ) :
    (image₂ f s t).image g = image₂ (fun a b => g (f a b)) s t :=
  coe_injective <| by
    push_cast
    exact image_image2 _ _
#align finset.image_image₂ Finset.image_image₂

#print Finset.image₂_image_left /-
theorem image₂_image_left (f : γ → β → δ) (g : α → γ) :
    image₂ f (s.image g) t = image₂ (fun a b => f (g a) b) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_left _ _
#align finset.image₂_image_left Finset.image₂_image_left
-/

/- warning: finset.image₂_image_right -> Finset.image₂_image_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_3 : DecidableEq.{succ u3} γ] [_inst_5 : DecidableEq.{succ u4} δ] {s : Finset.{u1} α} {t : Finset.{u2} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u4} (Finset.{u4} δ) (Finset.image₂.{u1, u3, u4} α γ δ (fun (a : δ) (b : δ) => _inst_5 a b) f s (Finset.image.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_3 a b) g t)) (Finset.image₂.{u1, u2, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) (fun (a : α) (b : β) => f a (g b)) s t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {δ : Type.{u4}} [_inst_3 : DecidableEq.{succ u2} γ] [_inst_5 : DecidableEq.{succ u4} δ] {s : Finset.{u3} α} {t : Finset.{u1} β} (f : α -> γ -> δ) (g : β -> γ), Eq.{succ u4} (Finset.{u4} δ) (Finset.image₂.{u3, u2, u4} α γ δ (fun (a : δ) (b : δ) => _inst_5 a b) f s (Finset.image.{u1, u2} β γ (fun (a : γ) (b : γ) => _inst_3 a b) g t)) (Finset.image₂.{u3, u1, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) (fun (a : α) (b : β) => f a (g b)) s t)
Case conversion may be inaccurate. Consider using '#align finset.image₂_image_right Finset.image₂_image_rightₓ'. -/
theorem image₂_image_right (f : α → γ → δ) (g : β → γ) :
    image₂ f s (t.image g) = image₂ (fun a b => f a (g b)) s t :=
  coe_injective <| by
    push_cast
    exact image2_image_right _ _
#align finset.image₂_image_right Finset.image₂_image_right

/- warning: finset.image₂_swap -> Finset.image₂_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] (f : α -> β -> γ) (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u2, u1, u3} β α γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (a : β) (b : α) => f b a) t s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] (f : α -> β -> γ) (s : Finset.{u3} α) (t : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} γ) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u2, u3, u1} β α γ (fun (a : γ) (b : γ) => _inst_3 a b) (fun (a : β) (b : α) => f b a) t s)
Case conversion may be inaccurate. Consider using '#align finset.image₂_swap Finset.image₂_swapₓ'. -/
theorem image₂_swap (f : α → β → γ) (s : Finset α) (t : Finset β) :
    image₂ f s t = image₂ (fun a b => f b a) t s :=
  coe_injective <| by
    push_cast
    exact image2_swap _ _ _
#align finset.image₂_swap Finset.image₂_swap

/- warning: finset.image₂_mk_eq_product -> Finset.image₂_mk_eq_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_9 : DecidableEq.{succ u1} α] [_inst_10 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.image₂.{u1, u2, max u1 u2} α β (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_9 a b) (fun (a : β) (b : β) => _inst_10 a b) a b) (Prod.mk.{u1, u2} α β) s t) (Finset.product.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_9 : DecidableEq.{succ u2} α] [_inst_10 : DecidableEq.{succ u1} β] (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.image₂.{u2, u1, max u1 u2} α β (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_9 a b) (fun (a : β) (b : β) => _inst_10 a b) a b) (Prod.mk.{u2, u1} α β) s t) (Finset.product.{u2, u1} α β s t)
Case conversion may be inaccurate. Consider using '#align finset.image₂_mk_eq_product Finset.image₂_mk_eq_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image₂_mk_eq_product [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    image₂ Prod.mk s t = s ×ˢ t := by ext <;> simp [Prod.ext_iff]
#align finset.image₂_mk_eq_product Finset.image₂_mk_eq_product

/- warning: finset.image₂_curry -> Finset.image₂_curry is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] (f : (Prod.{u1, u2} α β) -> γ) (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) (Function.curry.{u1, u2, u3} α β γ f) s t) (Finset.image.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] (f : (Prod.{u3, u2} α β) -> γ) (s : Finset.{u3} α) (t : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} γ) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) (Function.curry.{u3, u2, u1} α β γ f) s t) (Finset.image.{max u3 u2, u1} (Prod.{u3, u2} α β) γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.product.{u3, u2} α β s t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_curry Finset.image₂_curryₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image₂_curry (f : α × β → γ) (s : Finset α) (t : Finset β) :
    image₂ (curry f) s t = (s ×ˢ t).image f := by
  classical rw [← image₂_mk_eq_product, image_image₂, curry]
#align finset.image₂_curry Finset.image₂_curry

/- warning: finset.image_uncurry_product -> Finset.image_uncurry_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] (f : α -> β -> γ) (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ u3} (Finset.{u3} γ) (Finset.image.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (a : γ) (b : γ) => _inst_3 a b) (Function.uncurry.{u1, u2, u3} α β γ f) (Finset.product.{u1, u2} α β s t)) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_3 : DecidableEq.{succ u1} γ] (f : α -> β -> γ) (s : Finset.{u3} α) (t : Finset.{u2} β), Eq.{succ u1} (Finset.{u1} γ) (Finset.image.{max u2 u3, u1} (Prod.{u3, u2} α β) γ (fun (a : γ) (b : γ) => _inst_3 a b) (Function.uncurry.{u3, u2, u1} α β γ f) (Finset.product.{u3, u2} α β s t)) (Finset.image₂.{u3, u2, u1} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)
Case conversion may be inaccurate. Consider using '#align finset.image_uncurry_product Finset.image_uncurry_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_uncurry_product (f : α → β → γ) (s : Finset α) (t : Finset β) :
    (s ×ˢ t).image (uncurry f) = image₂ f s t := by rw [← image₂_curry, curry_uncurry]
#align finset.image_uncurry_product Finset.image_uncurry_product

/- warning: finset.image₂_left -> Finset.image₂_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_9 : DecidableEq.{succ u1} α], (Finset.Nonempty.{u2} β t) -> (Eq.{succ u1} (Finset.{u1} α) (Finset.image₂.{u1, u2, u1} α β α (fun (a : α) (b : α) => _inst_9 a b) (fun (x : α) (y : β) => x) s t) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_9 : DecidableEq.{succ u2} α], (Finset.Nonempty.{u1} β t) -> (Eq.{succ u2} (Finset.{u2} α) (Finset.image₂.{u2, u1, u2} α β α (fun (a : α) (b : α) => _inst_9 a b) (fun (x : α) (y : β) => x) s t) s)
Case conversion may be inaccurate. Consider using '#align finset.image₂_left Finset.image₂_leftₓ'. -/
@[simp]
theorem image₂_left [DecidableEq α] (h : t.Nonempty) : image₂ (fun x y => x) s t = s :=
  coe_injective <| by
    push_cast
    exact image2_left h
#align finset.image₂_left Finset.image₂_left

#print Finset.image₂_right /-
@[simp]
theorem image₂_right [DecidableEq β] (h : s.Nonempty) : image₂ (fun x y => y) s t = t :=
  coe_injective <| by
    push_cast
    exact image2_right h
#align finset.image₂_right Finset.image₂_right
-/

/- warning: finset.image₂_assoc -> Finset.image₂_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {ε : Type.{u4}} {ε' : Type.{u5}} [_inst_5 : DecidableEq.{succ u3} δ] [_inst_7 : DecidableEq.{succ u4} ε] [_inst_8 : DecidableEq.{succ u5} ε'] {s : Finset.{u1} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u4} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u4} (Finset.{u4} ε) (Finset.image₂.{u3, u6, u4} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u1, u2, u3} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u1, u5, u4} α ε' ε (fun (a : ε) (b : ε) => _inst_7 a b) f' s (Finset.image₂.{u2, u6, u5} β γ ε' (fun (a : ε') (b : ε') => _inst_8 a b) g' t u)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {δ : Type.{u4}} {ε : Type.{u5}} {ε' : Type.{u1}} [_inst_5 : DecidableEq.{succ u4} δ] [_inst_7 : DecidableEq.{succ u5} ε] [_inst_8 : DecidableEq.{succ u1} ε'] {s : Finset.{u3} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f (g a b) c) (f' a (g' b c))) -> (Eq.{succ u5} (Finset.{u5} ε) (Finset.image₂.{u4, u6, u5} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u3, u2, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u3, u1, u5} α ε' ε (fun (a : ε) (b : ε) => _inst_7 a b) f' s (Finset.image₂.{u2, u6, u1} β γ ε' (fun (a : ε') (b : ε') => _inst_8 a b) g' t u)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_assoc Finset.image₂_assocₓ'. -/
theorem image₂_assoc {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
    {g' : β → γ → ε'} (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    image₂ f (image₂ g s t) u = image₂ f' s (image₂ g' t u) :=
  coe_injective <| by
    push_cast
    exact image2_assoc h_assoc
#align finset.image₂_assoc Finset.image₂_assoc

/- warning: finset.image₂_comm -> Finset.image₂_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u1, u2, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u2, u1, u3} β α γ (fun (a : γ) (b : γ) => _inst_3 a b) g t s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_3 : DecidableEq.{succ u3} γ] {f : α -> β -> γ} {s : Finset.{u2} α} {t : Finset.{u1} β} {g : β -> α -> γ}, (forall (a : α) (b : β), Eq.{succ u3} γ (f a b) (g b a)) -> (Eq.{succ u3} (Finset.{u3} γ) (Finset.image₂.{u2, u1, u3} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t) (Finset.image₂.{u1, u2, u3} β α γ (fun (a : γ) (b : γ) => _inst_3 a b) g t s))
Case conversion may be inaccurate. Consider using '#align finset.image₂_comm Finset.image₂_commₓ'. -/
theorem image₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : image₂ f s t = image₂ g t s :=
  (image₂_swap _ _ _).trans <| by simp_rw [h_comm]
#align finset.image₂_comm Finset.image₂_comm

/- warning: finset.image₂_left_comm -> Finset.image₂_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {δ' : Type.{u4}} {ε : Type.{u5}} [_inst_5 : DecidableEq.{succ u3} δ] [_inst_6 : DecidableEq.{succ u4} δ'] [_inst_7 : DecidableEq.{succ u5} ε] {s : Finset.{u1} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u5} (Finset.{u5} ε) (Finset.image₂.{u1, u3, u5} α δ ε (fun (a : ε) (b : ε) => _inst_7 a b) f s (Finset.image₂.{u2, u6, u3} β γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g t u)) (Finset.image₂.{u2, u4, u5} β δ' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' t (Finset.image₂.{u1, u6, u4} α γ δ' (fun (a : δ') (b : δ') => _inst_6 a b) f' s u)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {δ : Type.{u3}} {δ' : Type.{u1}} {ε : Type.{u5}} [_inst_5 : DecidableEq.{succ u3} δ] [_inst_6 : DecidableEq.{succ u1} δ'] [_inst_7 : DecidableEq.{succ u5} ε] {s : Finset.{u4} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f a (g b c)) (g' b (f' a c))) -> (Eq.{succ u5} (Finset.{u5} ε) (Finset.image₂.{u4, u3, u5} α δ ε (fun (a : ε) (b : ε) => _inst_7 a b) f s (Finset.image₂.{u2, u6, u3} β γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g t u)) (Finset.image₂.{u2, u1, u5} β δ' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' t (Finset.image₂.{u4, u6, u1} α γ δ' (fun (a : δ') (b : δ') => _inst_6 a b) f' s u)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_left_comm Finset.image₂_left_commₓ'. -/
theorem image₂_left_comm {γ : Type _} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f' : α → γ → δ'} {g' : β → δ' → ε} (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    image₂ f s (image₂ g t u) = image₂ g' t (image₂ f' s u) :=
  coe_injective <| by
    push_cast
    exact image2_left_comm h_left_comm
#align finset.image₂_left_comm Finset.image₂_left_comm

/- warning: finset.image₂_right_comm -> Finset.image₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {δ' : Type.{u4}} {ε : Type.{u5}} [_inst_5 : DecidableEq.{succ u3} δ] [_inst_6 : DecidableEq.{succ u4} δ'] [_inst_7 : DecidableEq.{succ u5} ε] {s : Finset.{u1} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u5} (Finset.{u5} ε) (Finset.image₂.{u3, u6, u5} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u1, u2, u3} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u4, u2, u5} δ' β ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u1, u6, u4} α γ δ' (fun (a : δ') (b : δ') => _inst_6 a b) f' s u) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {δ : Type.{u4}} {δ' : Type.{u1}} {ε : Type.{u5}} [_inst_5 : DecidableEq.{succ u4} δ] [_inst_6 : DecidableEq.{succ u1} δ'] [_inst_7 : DecidableEq.{succ u5} ε] {s : Finset.{u3} α} {t : Finset.{u2} β} {γ : Type.{u6}} {u : Finset.{u6} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u5} ε (f (g a b) c) (g' (f' a c) b)) -> (Eq.{succ u5} (Finset.{u5} ε) (Finset.image₂.{u4, u6, u5} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u3, u2, u4} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u1, u2, u5} δ' β ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u3, u6, u1} α γ δ' (fun (a : δ') (b : δ') => _inst_6 a b) f' s u) t))
Case conversion may be inaccurate. Consider using '#align finset.image₂_right_comm Finset.image₂_right_commₓ'. -/
theorem image₂_right_comm {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f' : α → γ → δ'} {g' : δ' → β → ε} (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    image₂ f (image₂ g s t) u = image₂ g' (image₂ f' s u) t :=
  coe_injective <| by
    push_cast
    exact image2_right_comm h_right_comm
#align finset.image₂_right_comm Finset.image₂_right_comm

/- warning: finset.image_image₂_distrib -> Finset.image_image₂_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_2 : DecidableEq.{succ u4} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u6} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Finset.{u6} δ) (Finset.image.{u5, u6} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u3, u5} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u4, u6} α' β' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g₁ s) (Finset.image.{u3, u4} β β' (fun (a : β') (b : β') => _inst_2 a b) g₂ t)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {γ : Type.{u5}} {δ : Type.{u6}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_2 : DecidableEq.{succ u1} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u6} δ] {f : α -> β -> γ} {s : Finset.{u4} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ a) (g₂ b))) -> (Eq.{succ u6} (Finset.{u6} δ) (Finset.image.{u5, u6} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u4, u3, u5} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u1, u6} α' β' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u4, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g₁ s) (Finset.image.{u3, u1} β β' (fun (a : β') (b : β') => _inst_2 a b) g₂ t)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_distrib Finset.image_image₂_distribₓ'. -/
theorem image_image₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (image₂ f s t).image g = image₂ f' (s.image g₁) (t.image g₂) :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib h_distrib
#align finset.image_image₂_distrib Finset.image_image₂_distrib

/- warning: finset.image_image₂_distrib_left -> Finset.image_image₂_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u3, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u3, u5} α' β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g' s) t))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u1} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' a) b)) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u3, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u1, u2, u5} α' β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u3, u1} α α' (fun (a : α') (b : α') => _inst_1 a b) g' s) t))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_distrib_left Finset.image_image₂_distrib_leftₓ'. -/
/-- Symmetric statement to `finset.image₂_image_left_comm`. -/
theorem image_image₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (image₂ f s t).image g = image₂ f' (s.image g') t :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_left h_distrib
#align finset.image_image₂_distrib_left Finset.image_image₂_distrib_left

/- warning: finset.image_image₂_distrib_right -> Finset.image_image₂_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u1, u3, u5} α β' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g' t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u1} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' a (g' b))) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u3, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u3, u1, u5} α β' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s (Finset.image.{u2, u1} β β' (fun (a : β') (b : β') => _inst_2 a b) g' t)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_distrib_right Finset.image_image₂_distrib_rightₓ'. -/
/-- Symmetric statement to `finset.image_image₂_right_comm`. -/
theorem image_image₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) :
    (image₂ f s t).image g = image₂ f' s (t.image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_distrib_right h_distrib
#align finset.image_image₂_distrib_right Finset.image_image₂_distrib_right

/- warning: finset.image₂_image_left_comm -> Finset.image₂_image_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {s : Finset.{u1} α} {t : Finset.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u4} (Finset.{u4} γ) (Finset.image₂.{u2, u3, u4} α' β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g s) t) (Finset.image.{u5, u4} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u1, u3, u5} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s t)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} [_inst_1 : DecidableEq.{succ u4} α'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u1} δ] {s : Finset.{u2} α} {t : Finset.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f (g a) b) (g' (f' a b))) -> (Eq.{succ u5} (Finset.{u5} γ) (Finset.image₂.{u4, u3, u5} α' β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.image.{u2, u4} α α' (fun (a : α') (b : α') => _inst_1 a b) g s) t) (Finset.image.{u1, u5} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u2, u3, u1} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s t)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_image_left_comm Finset.image₂_image_left_commₓ'. -/
/-- Symmetric statement to `finset.image_image₂_distrib_left`. -/
theorem image₂_image_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) :
    image₂ f (s.image g) t = (image₂ f' s t).image g' :=
  (image_image₂_distrib_left fun a b => (h_left_comm a b).symm).symm
#align finset.image₂_image_left_comm Finset.image₂_image_left_comm

/- warning: finset.image_image₂_right_comm -> Finset.image_image₂_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {s : Finset.{u1} α} {t : Finset.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u4} (Finset.{u4} γ) (Finset.image₂.{u1, u3, u4} α β' γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g t)) (Finset.image.{u5, u4} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u1, u2, u5} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s t)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u1} δ] {s : Finset.{u4} α} {t : Finset.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f a (g b)) (g' (f' a b))) -> (Eq.{succ u5} (Finset.{u5} γ) (Finset.image₂.{u4, u3, u5} α β' γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g t)) (Finset.image.{u1, u5} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u4, u2, u1} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) f' s t)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_right_comm Finset.image_image₂_right_commₓ'. -/
/-- Symmetric statement to `finset.image_image₂_distrib_right`. -/
theorem image_image₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    image₂ f s (t.image g) = (image₂ f' s t).image g' :=
  (image_image₂_distrib_right fun a b => (h_right_comm a b).symm).symm
#align finset.image_image₂_right_comm Finset.image_image₂_right_comm

/- warning: finset.image₂_distrib_subset_left -> Finset.image₂_distrib_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ' : Type.{u4}} {δ : Type.{u5}} {ε : Type.{u6}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_4 : DecidableEq.{succ u4} γ'] [_inst_5 : DecidableEq.{succ u5} δ] [_inst_7 : DecidableEq.{succ u6} ε] {s : Finset.{u1} α} {t : Finset.{u2} β} {γ : Type.{u7}} {u : Finset.{u7} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f a (g b c)) (g' (f₁ a b) (f₂ a c))) -> (HasSubset.Subset.{u6} (Finset.{u6} ε) (Finset.hasSubset.{u6} ε) (Finset.image₂.{u1, u5, u6} α δ ε (fun (a : ε) (b : ε) => _inst_7 a b) f s (Finset.image₂.{u2, u7, u5} β γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g t u)) (Finset.image₂.{u3, u4, u6} β' γ' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u1, u2, u3} α β β' (fun (a : β') (b : β') => _inst_2 a b) f₁ s t) (Finset.image₂.{u1, u7, u4} α γ γ' (fun (a : γ') (b : γ') => _inst_4 a b) f₂ s u)))
but is expected to have type
  forall {α : Type.{u5}} {β : Type.{u3}} {β' : Type.{u2}} {γ' : Type.{u1}} {δ : Type.{u4}} {ε : Type.{u6}} [_inst_2 : DecidableEq.{succ u2} β'] [_inst_4 : DecidableEq.{succ u1} γ'] [_inst_5 : DecidableEq.{succ u4} δ] [_inst_7 : DecidableEq.{succ u6} ε] {s : Finset.{u5} α} {t : Finset.{u3} β} {γ : Type.{u7}} {u : Finset.{u7} γ} {f : α -> δ -> ε} {g : β -> γ -> δ} {f₁ : α -> β -> β'} {f₂ : α -> γ -> γ'} {g' : β' -> γ' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f a (g b c)) (g' (f₁ a b) (f₂ a c))) -> (HasSubset.Subset.{u6} (Finset.{u6} ε) (Finset.instHasSubsetFinset.{u6} ε) (Finset.image₂.{u5, u4, u6} α δ ε (fun (a : ε) (b : ε) => _inst_7 a b) f s (Finset.image₂.{u3, u7, u4} β γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g t u)) (Finset.image₂.{u2, u1, u6} β' γ' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u5, u3, u2} α β β' (fun (a : β') (b : β') => _inst_2 a b) f₁ s t) (Finset.image₂.{u5, u7, u1} α γ γ' (fun (a : γ') (b : γ') => _inst_4 a b) f₂ s u)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_distrib_subset_left Finset.image₂_distrib_subset_leftₓ'. -/
/-- The other direction does not hold because of the `s`-`s` cross terms on the RHS. -/
theorem image₂_distrib_subset_left {γ : Type _} {u : Finset γ} {f : α → δ → ε} {g : β → γ → δ}
    {f₁ : α → β → β'} {f₂ : α → γ → γ'} {g' : β' → γ' → ε}
    (h_distrib : ∀ a b c, f a (g b c) = g' (f₁ a b) (f₂ a c)) :
    image₂ f s (image₂ g t u) ⊆ image₂ g' (image₂ f₁ s t) (image₂ f₂ s u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_left h_distrib
#align finset.image₂_distrib_subset_left Finset.image₂_distrib_subset_left

/- warning: finset.image₂_distrib_subset_right -> Finset.image₂_distrib_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {δ : Type.{u5}} {ε : Type.{u6}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_2 : DecidableEq.{succ u4} β'] [_inst_5 : DecidableEq.{succ u5} δ] [_inst_7 : DecidableEq.{succ u6} ε] {s : Finset.{u1} α} {t : Finset.{u3} β} {γ : Type.{u7}} {u : Finset.{u7} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (g' (f₁ a c) (f₂ b c))) -> (HasSubset.Subset.{u6} (Finset.{u6} ε) (Finset.hasSubset.{u6} ε) (Finset.image₂.{u5, u7, u6} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u1, u3, u5} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u2, u4, u6} α' β' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u1, u7, u2} α γ α' (fun (a : α') (b : α') => _inst_1 a b) f₁ s u) (Finset.image₂.{u3, u7, u4} β γ β' (fun (a : β') (b : β') => _inst_2 a b) f₂ t u)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u1}} {δ : Type.{u5}} {ε : Type.{u6}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_2 : DecidableEq.{succ u1} β'] [_inst_5 : DecidableEq.{succ u5} δ] [_inst_7 : DecidableEq.{succ u6} ε] {s : Finset.{u4} α} {t : Finset.{u3} β} {γ : Type.{u7}} {u : Finset.{u7} γ} {f : δ -> γ -> ε} {g : α -> β -> δ} {f₁ : α -> γ -> α'} {f₂ : β -> γ -> β'} {g' : α' -> β' -> ε}, (forall (a : α) (b : β) (c : γ), Eq.{succ u6} ε (f (g a b) c) (g' (f₁ a c) (f₂ b c))) -> (HasSubset.Subset.{u6} (Finset.{u6} ε) (Finset.instHasSubsetFinset.{u6} ε) (Finset.image₂.{u5, u7, u6} δ γ ε (fun (a : ε) (b : ε) => _inst_7 a b) f (Finset.image₂.{u4, u3, u5} α β δ (fun (a : δ) (b : δ) => _inst_5 a b) g s t) u) (Finset.image₂.{u2, u1, u6} α' β' ε (fun (a : ε) (b : ε) => _inst_7 a b) g' (Finset.image₂.{u4, u7, u2} α γ α' (fun (a : α') (b : α') => _inst_1 a b) f₁ s u) (Finset.image₂.{u3, u7, u1} β γ β' (fun (a : β') (b : β') => _inst_2 a b) f₂ t u)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_distrib_subset_right Finset.image₂_distrib_subset_rightₓ'. -/
/-- The other direction does not hold because of the `u`-`u` cross terms on the RHS. -/
theorem image₂_distrib_subset_right {γ : Type _} {u : Finset γ} {f : δ → γ → ε} {g : α → β → δ}
    {f₁ : α → γ → α'} {f₂ : β → γ → β'} {g' : α' → β' → ε}
    (h_distrib : ∀ a b c, f (g a b) c = g' (f₁ a c) (f₂ b c)) :
    image₂ f (image₂ g s t) u ⊆ image₂ g' (image₂ f₁ s u) (image₂ f₂ t u) :=
  coe_subset.1 <| by
    push_cast
    exact Set.image2_distrib_subset_right h_distrib
#align finset.image₂_distrib_subset_right Finset.image₂_distrib_subset_right

/- warning: finset.image_image₂_antidistrib -> Finset.image_image₂_antidistrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {β' : Type.{u4}} {γ : Type.{u5}} {δ : Type.{u6}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_2 : DecidableEq.{succ u4} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u6} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Finset.{u6} δ) (Finset.image.{u5, u6} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u3, u5} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u4, u2, u6} β' α' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u3, u4} β β' (fun (a : β') (b : β') => _inst_2 a b) g₁ t) (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g₂ s)))
but is expected to have type
  forall {α : Type.{u4}} {α' : Type.{u1}} {β : Type.{u3}} {β' : Type.{u2}} {γ : Type.{u5}} {δ : Type.{u6}} [_inst_1 : DecidableEq.{succ u1} α'] [_inst_2 : DecidableEq.{succ u2} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u6} δ] {f : α -> β -> γ} {s : Finset.{u4} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}, (forall (a : α) (b : β), Eq.{succ u6} δ (g (f a b)) (f' (g₁ b) (g₂ a))) -> (Eq.{succ u6} (Finset.{u6} δ) (Finset.image.{u5, u6} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u4, u3, u5} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u1, u6} β' α' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u3, u2} β β' (fun (a : β') (b : β') => _inst_2 a b) g₁ t) (Finset.image.{u4, u1} α α' (fun (a : α') (b : α') => _inst_1 a b) g₂ s)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_antidistrib Finset.image_image₂_antidistribₓ'. -/
theorem image_image₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (image₂ f s t).image g = image₂ f' (t.image g₁) (s.image g₂) :=
  by
  rw [image₂_swap f]
  exact image_image₂_distrib fun _ _ => h_antidistrib _ _
#align finset.image_image₂_antidistrib Finset.image_image₂_antidistrib

/- warning: finset.image_image₂_antidistrib_left -> Finset.image_image₂_antidistrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u3, u1, u5} β' α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g' t) s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {β' : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u1} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' (g' b) a)) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u3, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u1, u3, u5} β' α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' (Finset.image.{u2, u1} β β' (fun (a : β') (b : β') => _inst_2 a b) g' t) s))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_antidistrib_left Finset.image_image₂_antidistrib_leftₓ'. -/
/-- Symmetric statement to `finset.image₂_image_left_anticomm`. -/
theorem image_image₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (image₂ f s t).image g = image₂ f' (t.image g') s :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_left h_antidistrib
#align finset.image_image₂_antidistrib_left Finset.image_image₂_antidistrib_left

/- warning: finset.image_image₂_antidistrib_right -> Finset.image_image₂_antidistrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u1} α} {t : Finset.{u3} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u1, u3, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u3, u2, u5} β α' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g' s)))
but is expected to have type
  forall {α : Type.{u3}} {α' : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u1} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {f : α -> β -> γ} {s : Finset.{u3} α} {t : Finset.{u2} β} {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}, (forall (a : α) (b : β), Eq.{succ u5} δ (g (f a b)) (f' b (g' a))) -> (Eq.{succ u5} (Finset.{u5} δ) (Finset.image.{u4, u5} γ δ (fun (a : δ) (b : δ) => _inst_5 a b) g (Finset.image₂.{u3, u2, u4} α β γ (fun (a : γ) (b : γ) => _inst_3 a b) f s t)) (Finset.image₂.{u2, u1, u5} β α' δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t (Finset.image.{u3, u1} α α' (fun (a : α') (b : α') => _inst_1 a b) g' s)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_antidistrib_right Finset.image_image₂_antidistrib_rightₓ'. -/
/-- Symmetric statement to `finset.image_image₂_right_anticomm`. -/
theorem image_image₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (image₂ f s t).image g = image₂ f' t (s.image g') :=
  coe_injective <| by
    push_cast
    exact image_image2_antidistrib_right h_antidistrib
#align finset.image_image₂_antidistrib_right Finset.image_image₂_antidistrib_right

/- warning: finset.image₂_image_left_anticomm -> Finset.image₂_image_left_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {α' : Type.{u2}} {β : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_1 : DecidableEq.{succ u2} α'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {s : Finset.{u1} α} {t : Finset.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u4} (Finset.{u4} γ) (Finset.image₂.{u2, u3, u4} α' β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.image.{u1, u2} α α' (fun (a : α') (b : α') => _inst_1 a b) g s) t) (Finset.image.{u5, u4} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u3, u1, u5} β α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t s)))
but is expected to have type
  forall {α : Type.{u2}} {α' : Type.{u4}} {β : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} [_inst_1 : DecidableEq.{succ u4} α'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u1} δ] {s : Finset.{u2} α} {t : Finset.{u3} β} {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f (g a) b) (g' (f' b a))) -> (Eq.{succ u5} (Finset.{u5} γ) (Finset.image₂.{u4, u3, u5} α' β γ (fun (a : γ) (b : γ) => _inst_3 a b) f (Finset.image.{u2, u4} α α' (fun (a : α') (b : α') => _inst_1 a b) g s) t) (Finset.image.{u1, u5} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u3, u2, u1} β α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t s)))
Case conversion may be inaccurate. Consider using '#align finset.image₂_image_left_anticomm Finset.image₂_image_left_anticommₓ'. -/
/-- Symmetric statement to `finset.image_image₂_antidistrib_left`. -/
theorem image₂_image_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    image₂ f (s.image g) t = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_left fun a b => (h_left_anticomm b a).symm).symm
#align finset.image₂_image_left_anticomm Finset.image₂_image_left_anticomm

/- warning: finset.image_image₂_right_anticomm -> Finset.image_image₂_right_anticomm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u4}} {δ : Type.{u5}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u4} γ] [_inst_5 : DecidableEq.{succ u5} δ] {s : Finset.{u1} α} {t : Finset.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u4} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u4} (Finset.{u4} γ) (Finset.image₂.{u1, u3, u4} α β' γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g t)) (Finset.image.{u5, u4} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u2, u1, u5} β α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t s)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u2}} {β' : Type.{u3}} {γ : Type.{u5}} {δ : Type.{u1}} [_inst_2 : DecidableEq.{succ u3} β'] [_inst_3 : DecidableEq.{succ u5} γ] [_inst_5 : DecidableEq.{succ u1} δ] {s : Finset.{u4} α} {t : Finset.{u2} β} {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}, (forall (a : α) (b : β), Eq.{succ u5} γ (f a (g b)) (g' (f' b a))) -> (Eq.{succ u5} (Finset.{u5} γ) (Finset.image₂.{u4, u3, u5} α β' γ (fun (a : γ) (b : γ) => _inst_3 a b) f s (Finset.image.{u2, u3} β β' (fun (a : β') (b : β') => _inst_2 a b) g t)) (Finset.image.{u1, u5} δ γ (fun (a : γ) (b : γ) => _inst_3 a b) g' (Finset.image₂.{u2, u4, u1} β α δ (fun (a : δ) (b : δ) => _inst_5 a b) f' t s)))
Case conversion may be inaccurate. Consider using '#align finset.image_image₂_right_anticomm Finset.image_image₂_right_anticommₓ'. -/
/-- Symmetric statement to `finset.image_image₂_antidistrib_right`. -/
theorem image_image₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    image₂ f s (t.image g) = (image₂ f' t s).image g' :=
  (image_image₂_antidistrib_right fun a b => (h_right_anticomm b a).symm).symm
#align finset.image_image₂_right_anticomm Finset.image_image₂_right_anticomm

/-- If `a` is a left identity for `f : α → β → β`, then `{a}` is a left identity for
`finset.image₂ f`. -/
theorem image₂_left_identity {f : α → γ → γ} {a : α} (h : ∀ b, f a b = b) (t : Finset γ) :
    image₂ f {a} t = t :=
  coe_injective <| by rw [coe_image₂, coe_singleton, Set.image2_left_identity h]
#align finset.image₂_left_identity Finset.image₂_left_identity

/-- If `b` is a right identity for `f : α → β → α`, then `{b}` is a right identity for
`finset.image₂ f`. -/
theorem image₂_right_identity {f : γ → β → γ} {b : β} (h : ∀ a, f a b = a) (s : Finset γ) :
    image₂ f s {b} = s := by rw [image₂_singleton_right, funext h, image_id']
#align finset.image₂_right_identity Finset.image₂_right_identity

end Finset

