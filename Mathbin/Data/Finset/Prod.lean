/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Oliver Nash

! This file was ported from Lean 3 source module data.finset.prod
! leanprover-community/mathlib commit 2705404e701abc6b3127da906f40bae062a169c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Card

/-!
# Finsets in product types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines finset constructions on the product type `α × β`. Beware not to confuse with the
`finset.prod` operation which computes the multiplicative product.

## Main declarations

* `finset.product`: Turns `s : finset α`, `t : finset β` into their product in `finset (α × β)`.
* `finset.diag`: For `s : finset α`, `s.diag` is the `finset (α × α)` of pairs `(a, a)` with
  `a ∈ s`.
* `finset.off_diag`: For `s : finset α`, `s.off_diag` is the `finset (α × α)` of pairs `(a, b)` with
  `a, b ∈ s` and `a ≠ b`.
-/


open Multiset

variable {α β γ : Type _}

namespace Finset

/-! ### prod -/


section Prod

variable {s s' : Finset α} {t t' : Finset β} {a : α} {b : β}

#print Finset.product /-
/-- `product s t` is the set of pairs `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
protected def product (s : Finset α) (t : Finset β) : Finset (α × β) :=
  ⟨_, s.Nodup.product t.Nodup⟩
#align finset.product Finset.product
-/

-- mathport name: finset.product
infixr:82
  " ×ˢ " =>-- This notation binds more strongly than (pre)images, unions and intersections.
  Finset.product

/- warning: finset.product_val -> Finset.product_val is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, Eq.{succ (max u1 u2)} (Multiset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.val.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) (Multiset.product.{u1, u2} α β (Finset.val.{u1} α s) (Finset.val.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, Eq.{max (succ u2) (succ u1)} (Multiset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.val.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) (Multiset.product.{u2, u1} α β (Finset.val.{u2} α s) (Finset.val.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.product_val Finset.product_valₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_val : (s ×ˢ t).1 = s.1 ×ˢ t.1 :=
  rfl
#align finset.product_val Finset.product_val

/- warning: finset.mem_product -> Finset.mem_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {p : Prod.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p (Finset.product.{u1, u2} α β s t)) (And (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) (Prod.fst.{u1, u2} α β p) s) (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) (Prod.snd.{u1, u2} α β p) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} {p : Prod.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instMembershipFinset.{max u2 u1} (Prod.{u2, u1} α β)) p (Finset.product.{u2, u1} α β s t)) (And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) (Prod.fst.{u2, u1} α β p) s) (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) (Prod.snd.{u2, u1} α β p) t))
Case conversion may be inaccurate. Consider using '#align finset.mem_product Finset.mem_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_product {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  mem_product
#align finset.mem_product Finset.mem_product

/- warning: finset.mk_mem_product -> Finset.mk_mem_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) b t) -> (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Finset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} {a : α} {b : β}, (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) b t) -> (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instMembershipFinset.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (Finset.product.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align finset.mk_mem_product Finset.mk_mem_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_mem_product (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  mem_product.2 ⟨ha, hb⟩
#align finset.mk_mem_product Finset.mk_mem_product

/- warning: finset.coe_product -> Finset.coe_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) ((fun (a : Type.{max u1 u2}) (b : Type.{max u1 u2}) [self : HasLiftT.{succ (max u1 u2), succ (max u1 u2)} a b] => self.0) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (HasLiftT.mk.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (CoeTCₓ.coe.{succ (max u1 u2), succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.Set.hasCoeT.{max u1 u2} (Prod.{u1, u2} α β)))) (Finset.product.{u1, u2} α β s t)) (Set.prod.{u1, u2} α β ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} α) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} α) (Set.{u1} α) (Finset.Set.hasCoeT.{u1} α))) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} β) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} β) (Set.{u2} β) (Finset.Set.hasCoeT.{u2} β))) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.toSet.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) (Set.prod.{u2, u1} α β (Finset.toSet.{u2} α s) (Finset.toSet.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.coe_product Finset.coe_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, norm_cast]
theorem coe_product (s : Finset α) (t : Finset β) : (↑(s ×ˢ t) : Set (α × β)) = s ×ˢ t :=
  Set.ext fun x => Finset.mem_product
#align finset.coe_product Finset.coe_product

/- warning: finset.subset_product_image_fst -> Finset.subset_product_image_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α], HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) (Finset.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α], HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) (Finset.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) s
Case conversion may be inaccurate. Consider using '#align finset.subset_product_image_fst Finset.subset_product_image_fstₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem subset_product_image_fst [DecidableEq α] : (s ×ˢ t).image Prod.fst ⊆ s := fun i => by
  simp (config := { contextual := true }) [mem_image]
#align finset.subset_product_image_fst Finset.subset_product_image_fst

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.subset_product_image_snd /-
theorem subset_product_image_snd [DecidableEq β] : (s ×ˢ t).image Prod.snd ⊆ t := fun i => by
  simp (config := { contextual := true }) [mem_image]
#align finset.subset_product_image_snd Finset.subset_product_image_snd
-/

/- warning: finset.product_image_fst -> Finset.product_image_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α], (Finset.Nonempty.{u2} β t) -> (Eq.{succ u1} (Finset.{u1} α) (Finset.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α], (Finset.Nonempty.{u1} β t) -> (Eq.{succ u2} (Finset.{u2} α) (Finset.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) s)
Case conversion may be inaccurate. Consider using '#align finset.product_image_fst Finset.product_image_fstₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_image_fst [DecidableEq α] (ht : t.Nonempty) : (s ×ˢ t).image Prod.fst = s :=
  by
  ext i
  simp [mem_image, ht.bex]
#align finset.product_image_fst Finset.product_image_fst

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.product_image_snd /-
theorem product_image_snd [DecidableEq β] (ht : s.Nonempty) : (s ×ˢ t).image Prod.snd = t :=
  by
  ext i
  simp [mem_image, ht.bex]
#align finset.product_image_snd Finset.product_image_snd
-/

/- warning: finset.subset_product -> Finset.subset_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] {s : Finset.{max u1 u2} (Prod.{u1, u2} α β)}, HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) s (Finset.product.{u1, u2} α β (Finset.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u1, u2} α β) s) (Finset.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (fun (a : β) (b : β) => _inst_2 a b) (Prod.snd.{u1, u2} α β) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β] {s : Finset.{max u1 u2} (Prod.{u2, u1} α β)}, HasSubset.Subset.{max u2 u1} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instHasSubsetFinset.{max u2 u1} (Prod.{u2, u1} α β)) s (Finset.product.{u2, u1} α β (Finset.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (fun (a : α) (b : α) => _inst_1 a b) (Prod.fst.{u2, u1} α β) s) (Finset.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (fun (a : β) (b : β) => _inst_2 a b) (Prod.snd.{u2, u1} α β) s))
Case conversion may be inaccurate. Consider using '#align finset.subset_product Finset.subset_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem subset_product [DecidableEq α] [DecidableEq β] {s : Finset (α × β)} :
    s ⊆ s.image Prod.fst ×ˢ s.image Prod.snd := fun p hp =>
  mem_product.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩
#align finset.subset_product Finset.subset_product

/- warning: finset.product_subset_product -> Finset.product_subset_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{u2} (Finset.{u2} β) (Finset.hasSubset.{u2} β) t t') -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β} {t' : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s s') -> (HasSubset.Subset.{u1} (Finset.{u1} β) (Finset.instHasSubsetFinset.{u1} β) t t') -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instHasSubsetFinset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t'))
Case conversion may be inaccurate. Consider using '#align finset.product_subset_product Finset.product_subset_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_subset_product (hs : s ⊆ s') (ht : t ⊆ t') : s ×ˢ t ⊆ s' ×ˢ t' := fun ⟨x, y⟩ h =>
  mem_product.2 ⟨hs (mem_product.1 h).1, ht (mem_product.1 h).2⟩
#align finset.product_subset_product Finset.product_subset_product

/- warning: finset.product_subset_product_left -> Finset.product_subset_product_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β}, (HasSubset.Subset.{u1} (Finset.{u1} α) (Finset.hasSubset.{u1} α) s s') -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β}, (HasSubset.Subset.{u2} (Finset.{u2} α) (Finset.instHasSubsetFinset.{u2} α) s s') -> (HasSubset.Subset.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instHasSubsetFinset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t))
Case conversion may be inaccurate. Consider using '#align finset.product_subset_product_left Finset.product_subset_product_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_subset_product_left (hs : s ⊆ s') : s ×ˢ t ⊆ s' ×ˢ t :=
  product_subset_product hs (Subset.refl _)
#align finset.product_subset_product_left Finset.product_subset_product_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.product_subset_product_right /-
theorem product_subset_product_right (ht : t ⊆ t') : s ×ˢ t ⊆ s ×ˢ t' :=
  product_subset_product (Subset.refl _) ht
#align finset.product_subset_product_right Finset.product_subset_product_right
-/

/- warning: finset.map_swap_product -> Finset.map_swap_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.map.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Function.Embedding.mk.{succ (max u2 u1), succ (max u1 u2)} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.swap.{u2, u1} β α) (Prod.swap_injective.{u2, u1} β α)) (Finset.product.{u2, u1} β α t s)) (Finset.product.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.map.{max u2 u1, max u2 u1} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (Function.Embedding.mk.{succ (max u2 u1), succ (max u2 u1)} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (Prod.swap.{u1, u2} β α) (Prod.swap_injective.{u2, u1} β α)) (Finset.product.{u1, u2} β α t s)) (Finset.product.{u2, u1} α β s t)
Case conversion may be inaccurate. Consider using '#align finset.map_swap_product Finset.map_swap_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem map_swap_product (s : Finset α) (t : Finset β) :
    (t ×ˢ s).map ⟨Prod.swap, Prod.swap_injective⟩ = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _
#align finset.map_swap_product Finset.map_swap_product

/- warning: finset.image_swap_product -> Finset.image_swap_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.image.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (Prod.swap.{u2, u1} β α) (Finset.product.{u2, u1} β α t s)) (Finset.product.{u1, u2} α β s t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{max (succ u2) (succ u1)} (Prod.{u1, u2} α β)] (_inst_2 : Finset.{u1} α) (s : Finset.{u2} β), Eq.{max (succ u1) (succ u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => _inst_1 a b) (Prod.swap.{u2, u1} β α) (Finset.product.{u2, u1} β α s _inst_2)) (Finset.product.{u1, u2} α β _inst_2 s)
Case conversion may be inaccurate. Consider using '#align finset.image_swap_product Finset.image_swap_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_swap_product [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    (t ×ˢ s).image Prod.swap = s ×ˢ t :=
  coe_injective <| by
    push_cast
    exact Set.image_swap_prod _ _
#align finset.image_swap_product Finset.image_swap_product

/- warning: finset.product_eq_bUnion -> Finset.product_eq_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.bunionᵢ.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) s (fun (a : α) => Finset.image.{u2, max u1 u2} β (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (b : β) => Prod.mk.{u1, u2} α β a b) t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{max (succ u2) (succ u1)} (Prod.{u1, u2} α β)] (_inst_2 : Finset.{u1} α) (s : Finset.{u2} β), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β _inst_2 s) (Finset.bunionᵢ.{u1, max u2 u1} α (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => _inst_1 a b) _inst_2 (fun (a : α) => Finset.image.{u2, max u2 u1} β (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => _inst_1 a b) (fun (b : β) => Prod.mk.{u1, u2} α β a b) s))
Case conversion may be inaccurate. Consider using '#align finset.product_eq_bUnion Finset.product_eq_bunionᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_eq_bunionᵢ [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    s ×ˢ t = s.bunionᵢ fun a => t.image fun b => (a, b) :=
  ext fun ⟨x, y⟩ => by
    simp only [mem_product, mem_bUnion, mem_image, exists_prop, Prod.mk.inj_iff, and_left_comm,
      exists_and_left, exists_eq_right, exists_eq_left]
#align finset.product_eq_bUnion Finset.product_eq_bunionᵢ

/- warning: finset.product_eq_bUnion_right -> Finset.product_eq_bunionᵢ_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β] (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.bunionᵢ.{u2, max u1 u2} β (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) t (fun (b : β) => Finset.image.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b) (fun (a : α) => Prod.mk.{u1, u2} α β a b) s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : DecidableEq.{max (succ u2) (succ u1)} (Prod.{u1, u2} α β)] (_inst_2 : Finset.{u1} α) (s : Finset.{u2} β), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β _inst_2 s) (Finset.bunionᵢ.{u2, max u2 u1} β (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => _inst_1 a b) s (fun (b : β) => Finset.image.{u1, max u2 u1} α (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => _inst_1 a b) (fun (a : α) => Prod.mk.{u1, u2} α β a b) _inst_2))
Case conversion may be inaccurate. Consider using '#align finset.product_eq_bUnion_right Finset.product_eq_bunionᵢ_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_eq_bunionᵢ_right [DecidableEq α] [DecidableEq β] (s : Finset α) (t : Finset β) :
    s ×ˢ t = t.bunionᵢ fun b => s.image fun a => (a, b) :=
  ext fun ⟨x, y⟩ => by
    simp only [mem_product, mem_bUnion, mem_image, exists_prop, Prod.mk.inj_iff, and_left_comm,
      exists_and_left, exists_eq_right, exists_eq_left]
#align finset.product_eq_bUnion_right Finset.product_eq_bunionᵢ_right

/- warning: finset.product_bUnion -> Finset.product_bunionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} γ] (s : Finset.{u1} α) (t : Finset.{u2} β) (f : (Prod.{u1, u2} α β) -> (Finset.{u3} γ)), Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (fun (a : γ) (b : γ) => _inst_1 a b) (Finset.product.{u1, u2} α β s t) f) (Finset.bunionᵢ.{u1, u3} α γ (fun (a : γ) (b : γ) => _inst_1 a b) s (fun (a : α) => Finset.bunionᵢ.{u2, u3} β γ (fun (a : γ) (b : γ) => _inst_1 a b) t (fun (b : β) => f (Prod.mk.{u1, u2} α β a b))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} [_inst_1 : DecidableEq.{succ u3} γ] (s : Finset.{u2} α) (t : Finset.{u1} β) (f : (Prod.{u2, u1} α β) -> (Finset.{u3} γ)), Eq.{succ u3} (Finset.{u3} γ) (Finset.bunionᵢ.{max u2 u1, u3} (Prod.{u2, u1} α β) γ (fun (a : γ) (b : γ) => _inst_1 a b) (Finset.product.{u2, u1} α β s t) f) (Finset.bunionᵢ.{u2, u3} α γ (fun (a : γ) (b : γ) => _inst_1 a b) s (fun (a : α) => Finset.bunionᵢ.{u1, u3} β γ (fun (a : γ) (b : γ) => _inst_1 a b) t (fun (b : β) => f (Prod.mk.{u2, u1} α β a b))))
Case conversion may be inaccurate. Consider using '#align finset.product_bUnion Finset.product_bunionᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- See also `finset.sup_product_left`. -/
@[simp]
theorem product_bunionᵢ [DecidableEq γ] (s : Finset α) (t : Finset β) (f : α × β → Finset γ) :
    (s ×ˢ t).bunionᵢ f = s.bunionᵢ fun a => t.bunionᵢ fun b => f (a, b) := by
  classical simp_rw [product_eq_bUnion, bUnion_bUnion, image_bUnion]
#align finset.product_bUnion Finset.product_bunionᵢ

/- warning: finset.card_product -> Finset.card_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α s) (Finset.card.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β), Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α s) (Finset.card.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.card_product Finset.card_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem card_product (s : Finset α) (t : Finset β) : card (s ×ˢ t) = card s * card t :=
  Multiset.card_product _ _
#align finset.card_product Finset.card_product

/- warning: finset.filter_product -> Finset.filter_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} (p : α -> Prop) (q : β -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u2} β q], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.filter.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => And (p (Prod.fst.{u1, u2} α β x)) (q (Prod.snd.{u1, u2} α β x))) (fun (a : Prod.{u1, u2} α β) => And.decidable (p (Prod.fst.{u1, u2} α β a)) (q (Prod.snd.{u1, u2} α β a)) (_inst_1 (Prod.fst.{u1, u2} α β a)) (_inst_2 (Prod.snd.{u1, u2} α β a))) (Finset.product.{u1, u2} α β s t)) (Finset.product.{u1, u2} α β (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u2} β q (fun (a : β) => _inst_2 a) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} (p : α -> Prop) (q : β -> Prop) [_inst_1 : DecidablePred.{succ u2} α p] [_inst_2 : DecidablePred.{succ u1} β q], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.filter.{max u2 u1} (Prod.{u2, u1} α β) (fun (x : Prod.{u2, u1} α β) => And (p (Prod.fst.{u2, u1} α β x)) (q (Prod.snd.{u2, u1} α β x))) (fun (a : Prod.{u2, u1} α β) => instDecidableAnd (p (Prod.fst.{u2, u1} α β a)) (q (Prod.snd.{u2, u1} α β a)) (_inst_1 (Prod.fst.{u2, u1} α β a)) (_inst_2 (Prod.snd.{u2, u1} α β a))) (Finset.product.{u2, u1} α β s t)) (Finset.product.{u2, u1} α β (Finset.filter.{u2} α p (fun (a : α) => _inst_1 a) s) (Finset.filter.{u1} β q (fun (a : β) => _inst_2 a) t))
Case conversion may be inaccurate. Consider using '#align finset.filter_product Finset.filter_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem filter_product (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filterₓ fun x : α × β => p x.1 ∧ q x.2) = s.filterₓ p ×ˢ t.filterₓ q :=
  by
  ext ⟨a, b⟩
  simp only [mem_filter, mem_product]
  exact and_and_and_comm (a ∈ s) (b ∈ t) (p a) (q b)
#align finset.filter_product Finset.filter_product

/- warning: finset.filter_product_left -> Finset.filter_product_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u1} α p], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.filter.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => p (Prod.fst.{u1, u2} α β x)) (fun (a : Prod.{u1, u2} α β) => _inst_1 (Prod.fst.{u1, u2} α β a)) (Finset.product.{u1, u2} α β s t)) (Finset.product.{u1, u2} α β (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} (p : α -> Prop) [_inst_1 : DecidablePred.{succ u2} α p], Eq.{max (succ u2) (succ u1)} (Finset.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.filter.{max u2 u1} (Prod.{u2, u1} α β) (fun (x : Prod.{u2, u1} α β) => p (Prod.fst.{u2, u1} α β x)) (fun (a : Prod.{u2, u1} α β) => _inst_1 (Prod.fst.{u2, u1} α β a)) (Finset.product.{u2, u1} α β s t)) (Finset.product.{u2, u1} α β (Finset.filter.{u2} α p (fun (a : α) => _inst_1 a) s) t)
Case conversion may be inaccurate. Consider using '#align finset.filter_product_left Finset.filter_product_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem filter_product_left (p : α → Prop) [DecidablePred p] :
    ((s ×ˢ t).filterₓ fun x : α × β => p x.1) = s.filterₓ p ×ˢ t := by
  simpa using filter_product p fun _ => True
#align finset.filter_product_left Finset.filter_product_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.filter_product_right /-
theorem filter_product_right (q : β → Prop) [DecidablePred q] :
    ((s ×ˢ t).filterₓ fun x : α × β => q x.2) = s ×ˢ t.filterₓ q := by
  simpa using filter_product (fun _ : α => True) q
#align finset.filter_product_right Finset.filter_product_right
-/

/- warning: finset.filter_product_card -> Finset.filter_product_card is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α) (t : Finset.{u2} β) (p : α -> Prop) (q : β -> Prop) [_inst_1 : DecidablePred.{succ u1} α p] [_inst_2 : DecidablePred.{succ u2} β q], Eq.{1} Nat (Finset.card.{max u1 u2} (Prod.{u1, u2} α β) (Finset.filter.{max u1 u2} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => Iff (p (Prod.fst.{u1, u2} α β x)) (q (Prod.snd.{u1, u2} α β x))) (fun (a : Prod.{u1, u2} α β) => Iff.decidable (p (Prod.fst.{u1, u2} α β a)) (q (Prod.snd.{u1, u2} α β a)) (_inst_1 (Prod.fst.{u1, u2} α β a)) (_inst_2 (Prod.snd.{u1, u2} α β a))) (Finset.product.{u1, u2} α β s t))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α (Finset.filter.{u1} α p (fun (a : α) => _inst_1 a) s)) (Finset.card.{u2} β (Finset.filter.{u2} β q (fun (a : β) => _inst_2 a) t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat Nat.hasMul) (Finset.card.{u1} α (Finset.filter.{u1} α (Function.comp.{succ u1, 1, 1} α Prop Prop Not p) (fun (a : α) => Not.decidable (p a) (_inst_1 a)) s)) (Finset.card.{u2} β (Finset.filter.{u2} β (Function.comp.{succ u2, 1, 1} β Prop Prop Not q) (fun (a : β) => Not.decidable (q a) (_inst_2 a)) t))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α) (t : Finset.{u1} β) (p : α -> Prop) (q : β -> Prop) [_inst_1 : DecidablePred.{succ u2} α p] [_inst_2 : DecidablePred.{succ u1} β q], Eq.{1} Nat (Finset.card.{max u2 u1} (Prod.{u2, u1} α β) (Finset.filter.{max u2 u1} (Prod.{u2, u1} α β) (fun (x : Prod.{u2, u1} α β) => Eq.{1} Prop (p (Prod.fst.{u2, u1} α β x)) (q (Prod.snd.{u2, u1} α β x))) (fun (a : Prod.{u2, u1} α β) => instDecidableEqProp (p (Prod.fst.{u2, u1} α β a)) (q (Prod.snd.{u2, u1} α β a)) (instDecidableIff (p (Prod.fst.{u2, u1} α β a)) (q (Prod.snd.{u2, u1} α β a)) (_inst_1 (Prod.fst.{u2, u1} α β a)) (_inst_2 (Prod.snd.{u2, u1} α β a)))) (Finset.product.{u2, u1} α β s t))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α (Finset.filter.{u2} α p (fun (a : α) => _inst_1 a) s)) (Finset.card.{u1} β (Finset.filter.{u1} β q (fun (a : β) => _inst_2 a) t))) (HMul.hMul.{0, 0, 0} Nat Nat Nat (instHMul.{0} Nat instMulNat) (Finset.card.{u2} α (Finset.filter.{u2} α (fun (x._@.Mathlib.Data.Finset.Prod._hyg.1940 : α) => Not (p x._@.Mathlib.Data.Finset.Prod._hyg.1940)) (fun (a : α) => instDecidableNot (p a) (_inst_1 a)) s)) (Finset.card.{u1} β (Finset.filter.{u1} β (fun (x._@.Mathlib.Data.Finset.Prod._hyg.1956 : β) => Not (q x._@.Mathlib.Data.Finset.Prod._hyg.1956)) (fun (a : β) => instDecidableNot (q a) (_inst_2 a)) t))))
Case conversion may be inaccurate. Consider using '#align finset.filter_product_card Finset.filter_product_cardₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem filter_product_card (s : Finset α) (t : Finset β) (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q] :
    ((s ×ˢ t).filterₓ fun x : α × β => p x.1 ↔ q x.2).card =
      (s.filterₓ p).card * (t.filterₓ q).card +
        (s.filterₓ (Not ∘ p)).card * (t.filterₓ (Not ∘ q)).card :=
  by
  classical
    rw [← card_product, ← card_product, ← filter_product, ← filter_product, ← card_union_eq]
    · apply congr_arg
      ext ⟨a, b⟩
      simp only [filter_union_right, mem_filter, mem_product]
      constructor <;> intro h <;> use h.1
      simp only [Function.comp_apply, and_self_iff, h.2, em (q b)]
      cases h.2 <;>
        · try simp at h_1
          simp [h_1]
    · apply Finset.disjoint_filter_filter'
      exact (disjoint_compl_right.inf_left _).inf_right _
#align finset.filter_product_card Finset.filter_product_card

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.empty_product /-
theorem empty_product (t : Finset β) : (∅ : Finset α) ×ˢ t = ∅ :=
  rfl
#align finset.empty_product Finset.empty_product
-/

/- warning: finset.product_empty -> Finset.product_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Finset.{u1} α), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Prod.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Finset.{u2} α), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Prod.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align finset.product_empty Finset.product_emptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_empty (s : Finset α) : s ×ˢ (∅ : Finset β) = ∅ :=
  eq_empty_of_forall_not_mem fun x h => (Finset.mem_product.1 h).2
#align finset.product_empty Finset.product_empty

/- warning: finset.nonempty.product -> Finset.Nonempty.product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{u1} α s) -> (Finset.Nonempty.{u2} β t) -> (Finset.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{u2} α s) -> (Finset.Nonempty.{u1} β t) -> (Finset.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty.product Finset.Nonempty.productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.product (hs : s.Nonempty) (ht : t.Nonempty) : (s ×ˢ t).Nonempty :=
  let ⟨x, hx⟩ := hs
  let ⟨y, hy⟩ := ht
  ⟨(x, y), mem_product.2 ⟨hx, hy⟩⟩
#align finset.nonempty.product Finset.Nonempty.product

/- warning: finset.nonempty.fst -> Finset.Nonempty.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) -> (Finset.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) -> (Finset.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.fst Finset.Nonempty.fstₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.fst (h : (s ×ˢ t).Nonempty) : s.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.1, (mem_product.1 hxy).1⟩
#align finset.nonempty.fst Finset.Nonempty.fst

/- warning: finset.nonempty.snd -> Finset.Nonempty.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, (Finset.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) -> (Finset.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, (Finset.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) -> (Finset.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align finset.nonempty.snd Finset.Nonempty.sndₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.snd (h : (s ×ˢ t).Nonempty) : t.Nonempty :=
  let ⟨xy, hxy⟩ := h
  ⟨xy.2, (mem_product.1 hxy).2⟩
#align finset.nonempty.snd Finset.Nonempty.snd

/- warning: finset.nonempty_product -> Finset.nonempty_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, Iff (Finset.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t)) (And (Finset.Nonempty.{u1} α s) (Finset.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, Iff (Finset.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t)) (And (Finset.Nonempty.{u2} α s) (Finset.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align finset.nonempty_product Finset.nonempty_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem nonempty_product : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.product h.2⟩
#align finset.nonempty_product Finset.nonempty_product

/- warning: finset.product_eq_empty -> Finset.product_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β}, Iff (Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (EmptyCollection.emptyCollection.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasEmptyc.{max u1 u2} (Prod.{u1, u2} α β)))) (Or (Eq.{succ u1} (Finset.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Finset.{u1} α) (Finset.hasEmptyc.{u1} α))) (Eq.{succ u2} (Finset.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Finset.{u2} β) (Finset.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β}, Iff (Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s t) (EmptyCollection.emptyCollection.{max u2 u1} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instEmptyCollectionFinset.{max u2 u1} (Prod.{u2, u1} α β)))) (Or (Eq.{succ u2} (Finset.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Finset.{u2} α) (Finset.instEmptyCollectionFinset.{u2} α))) (Eq.{succ u1} (Finset.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Finset.{u1} β) (Finset.instEmptyCollectionFinset.{u1} β))))
Case conversion may be inaccurate. Consider using '#align finset.product_eq_empty Finset.product_eq_emptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_eq_empty {s : Finset α} {t : Finset β} : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  rw [← not_nonempty_iff_eq_empty, nonempty_product, not_and_or, not_nonempty_iff_eq_empty,
    not_nonempty_iff_eq_empty]
#align finset.product_eq_empty Finset.product_eq_empty

/- warning: finset.singleton_product -> Finset.singleton_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Finset.{u2} β} {a : α}, Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) t) (Finset.map.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Function.Embedding.mk.{succ u2, succ (max u1 u2)} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) (Prod.mk.inj_left.{u1, u2} α β a)) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Finset.{u1} β} {a : α}, Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a) t) (Finset.map.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Function.Embedding.mk.{succ u1, succ (max u1 u2)} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) (Prod.mk.inj_left.{u1, u2} α β a)) t)
Case conversion may be inaccurate. Consider using '#align finset.singleton_product Finset.singleton_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem singleton_product {a : α} : ({a} : Finset α) ×ˢ t = t.map ⟨Prod.mk a, Prod.mk.inj_left _⟩ :=
  by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align finset.singleton_product Finset.singleton_product

/- warning: finset.product_singleton -> Finset.product_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {b : β}, Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Finset.map.{u1, max u1 u2} α (Prod.{u1, u2} α β) (Function.Embedding.mk.{succ u1, succ (max u1 u2)} α (Prod.{u1, u2} α β) (fun (i : α) => Prod.mk.{u1, u2} α β i b) (Prod.mk.inj_right.{u1, u2} α β b)) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {b : β}, Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Finset.map.{u2, max u1 u2} α (Prod.{u2, u1} α β) (Function.Embedding.mk.{succ u2, succ (max u1 u2)} α (Prod.{u2, u1} α β) (fun (i : α) => Prod.mk.{u2, u1} α β i b) (Prod.mk.inj_right.{u1, u2} α β b)) s)
Case conversion may be inaccurate. Consider using '#align finset.product_singleton Finset.product_singletonₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_singleton {b : β} : s ×ˢ {b} = s.map ⟨fun i => (i, b), Prod.mk.inj_right _⟩ :=
  by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align finset.product_singleton Finset.product_singleton

/- warning: finset.singleton_product_singleton -> Finset.singleton_product_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {b : β}, Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) (Singleton.singleton.{u2, u2} β (Finset.{u2} β) (Finset.hasSingleton.{u2} β) b)) (Singleton.singleton.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasSingleton.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {a : α} {b : β}, Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Finset.{u2} α) (Finset.instSingletonFinset.{u2} α) a) (Singleton.singleton.{u1, u1} β (Finset.{u1} β) (Finset.instSingletonFinset.{u1} β) b)) (Singleton.singleton.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instSingletonFinset.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align finset.singleton_product_singleton Finset.singleton_product_singletonₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem singleton_product_singleton {a : α} {b : β} :
    ({a} : Finset α) ×ˢ ({b} : Finset β) = {(a, b)} := by
  simp only [product_singleton, Function.Embedding.coeFn_mk, map_singleton]
#align finset.singleton_product_singleton Finset.singleton_product_singleton

/- warning: finset.union_product -> Finset.union_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s s') t) (Union.union.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasUnion.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Union.union.{u2} (Finset.{u2} α) (Finset.instUnionFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s s') t) (Union.union.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instUnionFinset.{max u2 u1} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t))
Case conversion may be inaccurate. Consider using '#align finset.union_product Finset.union_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem union_product [DecidableEq α] [DecidableEq β] : (s ∪ s') ×ˢ t = s ×ˢ t ∪ s' ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp only [or_and_right, mem_union, mem_product]
#align finset.union_product Finset.union_product

/- warning: finset.product_union -> Finset.product_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (Union.union.{u2} (Finset.{u2} β) (Finset.hasUnion.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) t t')) (Union.union.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasUnion.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} {t' : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s (Union.union.{u1} (Finset.{u1} β) (Finset.instUnionFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) t t')) (Union.union.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instUnionFinset.{max u2 u1} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s t'))
Case conversion may be inaccurate. Consider using '#align finset.product_union Finset.product_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_union [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∪ t') = s ×ˢ t ∪ s ×ˢ t' :=
  by
  ext ⟨x, y⟩
  simp only [and_or_left, mem_union, mem_product]
#align finset.product_union Finset.product_union

/- warning: finset.inter_product -> Finset.inter_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s s') t) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasInter.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s s') t) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instInterFinset.{max u2 u1} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t))
Case conversion may be inaccurate. Consider using '#align finset.inter_product Finset.inter_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inter_product [DecidableEq α] [DecidableEq β] : (s ∩ s') ×ˢ t = s ×ˢ t ∩ s' ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter, mem_product]
#align finset.inter_product Finset.inter_product

/- warning: finset.product_inter -> Finset.product_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) t t')) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasInter.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {t : Finset.{u1} β} {t' : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) t t')) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instInterFinset.{max u2 u1} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s t'))
Case conversion may be inaccurate. Consider using '#align finset.product_inter Finset.product_interₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_inter [DecidableEq α] [DecidableEq β] : s ×ˢ (t ∩ t') = s ×ˢ t ∩ s ×ˢ t' :=
  by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter, mem_product]
#align finset.product_inter Finset.product_inter

/- warning: finset.product_inter_product -> Finset.product_inter_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} [_inst_1 : DecidableEq.{succ u1} α] [_inst_2 : DecidableEq.{succ u2} β], Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.hasInter.{max u1 u2} (Prod.{u1, u2} α β) (fun (a : Prod.{u1, u2} α β) (b : Prod.{u1, u2} α β) => Prod.decidableEq.{u1, u2} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t')) (Finset.product.{u1, u2} α β (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s s') (Inter.inter.{u2} (Finset.{u2} β) (Finset.hasInter.{u2} β (fun (a : β) (b : β) => _inst_2 a b)) t t'))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β} {t' : Finset.{u1} β} [_inst_1 : DecidableEq.{succ u2} α] [_inst_2 : DecidableEq.{succ u1} β], Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Inter.inter.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.instInterFinset.{max u2 u1} (Prod.{u2, u1} α β) (fun (a : Prod.{u2, u1} α β) (b : Prod.{u2, u1} α β) => instDecidableEqProd.{u2, u1} α β (fun (a : α) (b : α) => _inst_1 a b) (fun (a : β) (b : β) => _inst_2 a b) a b)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t')) (Finset.product.{u2, u1} α β (Inter.inter.{u2} (Finset.{u2} α) (Finset.instInterFinset.{u2} α (fun (a : α) (b : α) => _inst_1 a b)) s s') (Inter.inter.{u1} (Finset.{u1} β) (Finset.instInterFinset.{u1} β (fun (a : β) (b : β) => _inst_2 a b)) t t'))
Case conversion may be inaccurate. Consider using '#align finset.product_inter_product Finset.product_inter_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_inter_product [DecidableEq α] [DecidableEq β] :
    s ×ˢ t ∩ s' ×ˢ t' = (s ∩ s') ×ˢ (t ∩ t') :=
  by
  ext ⟨x, y⟩
  simp only [and_assoc', and_left_comm, mem_inter, mem_product]
#align finset.product_inter_product Finset.product_inter_product

/- warning: finset.disjoint_product -> Finset.disjoint_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, Iff (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t')) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s') (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t'))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β}, Iff (Disjoint.{max u2 u1} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t')) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s s') (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t t'))
Case conversion may be inaccurate. Consider using '#align finset.disjoint_product Finset.disjoint_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t') ↔ Disjoint s s' ∨ Disjoint t t' := by
  simp_rw [← disjoint_coe, coe_product, Set.disjoint_prod]
#align finset.disjoint_product Finset.disjoint_product

/- warning: finset.disj_union_product -> Finset.disjUnion_product is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {s' : Finset.{u1} α} {t : Finset.{u2} β} (hs : Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s'), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β (Finset.disjUnion.{u1} α s s' hs) t) (Finset.disjUnion.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t) (Iff.mpr (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s' t)) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s') (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t)) (Finset.disjoint_product.{u1, u2} α β s s' t t) (Or.inl (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s') (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t) hs)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Finset.{u2} α} {s' : Finset.{u2} α} {t : Finset.{u1} β} (hs : Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s s'), Eq.{max (succ u2) (succ u1)} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β (Finset.disjUnion.{u2} α s s' hs) t) (Finset.disjUnion.{max u2 u1} (Prod.{u2, u1} α β) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t) (Iff.mpr (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u2, u1} α β)) (Finset.partialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u2 u1} (Prod.{u2, u1} α β)) (Finset.product.{u2, u1} α β s t) (Finset.product.{u2, u1} α β s' t)) (Or (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s s') (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t t)) (Finset.disjoint_product.{u2, u1} α β s s' t t) (Or.inl (Disjoint.{u2} (Finset.{u2} α) (Finset.partialOrder.{u2} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} α) s s') (Disjoint.{u1} (Finset.{u1} β) (Finset.partialOrder.{u1} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} β) t t) hs)))
Case conversion may be inaccurate. Consider using '#align finset.disj_union_product Finset.disjUnion_productₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem disjUnion_product (hs : Disjoint s s') :
    s.disjUnion s' hs ×ˢ t = (s ×ˢ t).disjUnion (s' ×ˢ t) (disjoint_product.mpr <| Or.inl hs) :=
  eq_of_veq <| Multiset.add_product _ _ _
#align finset.disj_union_product Finset.disjUnion_product

/- warning: finset.product_disj_union -> Finset.product_disjUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} (ht : Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t'), Eq.{succ (max u1 u2)} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (Finset.disjUnion.{u2} β t t' ht)) (Finset.disjUnion.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t') (Iff.mpr (Disjoint.{max u1 u2} (Finset.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.orderBot.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t')) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t')) (Finset.disjoint_product.{u1, u2} α β s s t t') (Or.inr (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s s) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.orderBot.{u2} β) t t') ht)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Finset.{u1} α} {t : Finset.{u2} β} {t' : Finset.{u2} β} (ht : Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t t'), Eq.{max (succ u1) (succ u2)} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s (Finset.disjUnion.{u2} β t t' ht)) (Finset.disjUnion.{max u1 u2} (Prod.{u1, u2} α β) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t') (Iff.mpr (Disjoint.{max u2 u1} (Finset.{max u2 u1} (Prod.{u1, u2} α β)) (Finset.partialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{max u1 u2} (Prod.{u1, u2} α β)) (Finset.product.{u1, u2} α β s t) (Finset.product.{u1, u2} α β s t')) (Or (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s s) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t t')) (Finset.disjoint_product.{u1, u2} α β s s t t') (Or.inr (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s s) (Disjoint.{u2} (Finset.{u2} β) (Finset.partialOrder.{u2} β) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u2} β) t t') ht)))
Case conversion may be inaccurate. Consider using '#align finset.product_disj_union Finset.product_disjUnionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem product_disjUnion (ht : Disjoint t t') :
    s ×ˢ t.disjUnion t' ht = (s ×ˢ t).disjUnion (s ×ˢ t') (disjoint_product.mpr <| Or.inr ht) :=
  eq_of_veq <| Multiset.product_add _ _ _
#align finset.product_disj_union Finset.product_disjUnion

end Prod

section Diag

variable [DecidableEq α] (s t : Finset α)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.diag /-
/-- Given a finite set `s`, the diagonal, `s.diag` is the set of pairs of the form `(a, a)` for
`a ∈ s`. -/
def diag :=
  (s ×ˢ s).filterₓ fun a : α × α => a.fst = a.snd
#align finset.diag Finset.diag
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Finset.offDiag /-
/-- Given a finite set `s`, the off-diagonal, `s.off_diag` is the set of pairs `(a, b)` with `a ≠ b`
for `a, b ∈ s`. -/
def offDiag :=
  (s ×ˢ s).filterₓ fun a : α × α => a.fst ≠ a.snd
#align finset.off_diag Finset.offDiag
-/

variable {s} {x : α × α}

#print Finset.mem_diag /-
@[simp]
theorem mem_diag : x ∈ s.diag ↔ x.1 ∈ s ∧ x.1 = x.2 :=
  by
  simp only [diag, mem_filter, mem_product]
  constructor <;> intro h <;> simp only [h, and_true_iff, eq_self_iff_true, and_self_iff]
  rw [← h.2]
  exact h.1
#align finset.mem_diag Finset.mem_diag
-/

#print Finset.mem_offDiag /-
@[simp]
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  by
  simp only [off_diag, mem_filter, mem_product]
  constructor <;> intro h <;> simp only [h, Ne.def, not_false_iff, and_self_iff]
#align finset.mem_off_diag Finset.mem_offDiag
-/

variable (s)

#print Finset.coe_offDiag /-
@[simp, norm_cast]
theorem coe_offDiag : (s.offDiag : Set (α × α)) = (s : Set α).offDiag :=
  Set.ext fun _ => mem_offDiag
#align finset.coe_off_diag Finset.coe_offDiag
-/

#print Finset.diag_card /-
@[simp]
theorem diag_card : (diag s).card = s.card :=
  by
  suffices diag s = s.image fun a => (a, a) by
    rw [this]
    apply card_image_of_inj_on
    exact fun x1 h1 x2 h2 h3 => (Prod.mk.inj h3).1
  ext ⟨a₁, a₂⟩
  rw [mem_diag]
  constructor <;> intro h <;> rw [Finset.mem_image] at *
  · use a₁, h.1, prod.mk.inj_iff.mpr ⟨rfl, h.2⟩
  · rcases h with ⟨a, h1, h2⟩
    have h := Prod.mk.inj h2
    rw [← h.1, ← h.2]
    use h1
#align finset.diag_card Finset.diag_card
-/

#print Finset.offDiag_card /-
@[simp]
theorem offDiag_card : (offDiag s).card = s.card * s.card - s.card :=
  by
  suffices (diag s).card + (off_diag s).card = s.card * s.card
    by
    nth_rw 3 [← s.diag_card]
    simp only [diag_card] at *
    rw [tsub_eq_of_eq_add_rev]
    rw [this]
  rw [← card_product]
  apply filter_card_add_filter_neg_card_eq_card
#align finset.off_diag_card Finset.offDiag_card
-/

#print Finset.diag_mono /-
@[mono]
theorem diag_mono : Monotone (diag : Finset α → Finset (α × α)) := fun s t h x hx =>
  mem_diag.2 <| And.imp_left (@h _) <| mem_diag.1 hx
#align finset.diag_mono Finset.diag_mono
-/

#print Finset.offDiag_mono /-
@[mono]
theorem offDiag_mono : Monotone (offDiag : Finset α → Finset (α × α)) := fun s t h x hx =>
  mem_offDiag.2 <| And.imp (@h _) (And.imp_left <| @h _) <| mem_offDiag.1 hx
#align finset.off_diag_mono Finset.offDiag_mono
-/

#print Finset.diag_empty /-
@[simp]
theorem diag_empty : (∅ : Finset α).diag = ∅ :=
  rfl
#align finset.diag_empty Finset.diag_empty
-/

#print Finset.offDiag_empty /-
@[simp]
theorem offDiag_empty : (∅ : Finset α).offDiag = ∅ :=
  rfl
#align finset.off_diag_empty Finset.offDiag_empty
-/

/- warning: finset.diag_union_off_diag -> Finset.diag_union_offDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.product.{u1, u1} α α s s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.product.{u1, u1} α α s s)
Case conversion may be inaccurate. Consider using '#align finset.diag_union_off_diag Finset.diag_union_offDiagₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem diag_union_offDiag : s.diag ∪ s.offDiag = s ×ˢ s :=
  filter_union_filter_neg_eq _ _
#align finset.diag_union_off_diag Finset.diag_union_offDiag

/- warning: finset.disjoint_diag_off_diag -> Finset.disjoint_diag_offDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.orderBot.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Disjoint.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.partialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
Case conversion may be inaccurate. Consider using '#align finset.disjoint_diag_off_diag Finset.disjoint_diag_offDiagₓ'. -/
@[simp]
theorem disjoint_diag_offDiag : Disjoint s.diag s.offDiag :=
  disjoint_filter_filter_neg _ _ _
#align finset.disjoint_diag_off_diag Finset.disjoint_diag_offDiag

/- warning: finset.product_sdiff_diag -> Finset.product_sdiff_diag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasSdiff.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.product.{u1, u1} α α s s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instSDiffFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.product.{u1, u1} α α s s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
Case conversion may be inaccurate. Consider using '#align finset.product_sdiff_diag Finset.product_sdiff_diagₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_sdiff_diag : s ×ˢ s \ s.diag = s.offDiag := by
  rw [← diag_union_off_diag, union_comm, union_sdiff_self,
    sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _).symm]
#align finset.product_sdiff_diag Finset.product_sdiff_diag

/- warning: finset.product_sdiff_off_diag -> Finset.product_sdiff_offDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasSdiff.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.product.{u1, u1} α α s s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instSDiffFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.product.{u1, u1} α α s s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s)
Case conversion may be inaccurate. Consider using '#align finset.product_sdiff_off_diag Finset.product_sdiff_offDiagₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem product_sdiff_offDiag : s ×ˢ s \ s.offDiag = s.diag := by
  rw [← diag_union_off_diag, union_sdiff_self, sdiff_eq_self_of_disjoint (disjoint_diag_off_diag _)]
#align finset.product_sdiff_off_diag Finset.product_sdiff_offDiag

/- warning: finset.diag_inter -> Finset.diag_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasInter.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instInterFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
Case conversion may be inaccurate. Consider using '#align finset.diag_inter Finset.diag_interₓ'. -/
theorem diag_inter : (s ∩ t).diag = s.diag ∩ t.diag :=
  ext fun x => by simpa only [mem_diag, mem_inter] using and_and_right _ _ _
#align finset.diag_inter Finset.diag_inter

/- warning: finset.off_diag_inter -> Finset.offDiag_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Inter.inter.{u1} (Finset.{u1} α) (Finset.hasInter.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasInter.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Inter.inter.{u1} (Finset.{u1} α) (Finset.instInterFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Inter.inter.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instInterFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
Case conversion may be inaccurate. Consider using '#align finset.off_diag_inter Finset.offDiag_interₓ'. -/
theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_inter _ _
#align finset.off_diag_inter Finset.offDiag_inter

/- warning: finset.diag_union -> Finset.diag_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (s : Finset.{u1} α) (t : Finset.{u1} α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t))
Case conversion may be inaccurate. Consider using '#align finset.diag_union Finset.diag_unionₓ'. -/
theorem diag_union : (s ∪ t).diag = s.diag ∪ t.diag :=
  by
  ext ⟨i, j⟩
  simp only [mem_diag, mem_union, or_and_right]
#align finset.diag_union Finset.diag_union

variable {s t}

/- warning: finset.off_diag_union -> Finset.offDiag_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.orderBot.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.hasUnion.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (Finset.product.{u1, u1} α α s t)) (Finset.product.{u1, u1} α α t s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} {t : Finset.{u1} α}, (Disjoint.{u1} (Finset.{u1} α) (Finset.partialOrder.{u1} α) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) s t) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Union.union.{u1} (Finset.{u1} α) (Finset.instUnionFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) s t)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) t)) (Finset.product.{u1, u1} α α s t)) (Finset.product.{u1, u1} α α t s)))
Case conversion may be inaccurate. Consider using '#align finset.off_diag_union Finset.offDiag_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s :=
  coe_injective <| by
    push_cast
    exact Set.offDiag_union (disjoint_coe.2 h)
#align finset.off_diag_union Finset.offDiag_union

variable (a : α)

#print Finset.offDiag_singleton /-
@[simp]
theorem offDiag_singleton : ({a} : Finset α).offDiag = ∅ := by simp [← Finset.card_eq_zero]
#align finset.off_diag_singleton Finset.offDiag_singleton
-/

#print Finset.diag_singleton /-
theorem diag_singleton : ({a} : Finset α).diag = {(a, a)} := by
  rw [← product_sdiff_off_diag, off_diag_singleton, sdiff_empty, singleton_product_singleton]
#align finset.diag_singleton Finset.diag_singleton
-/

/- warning: finset.diag_insert -> Finset.diag_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (a : α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Insert.insert.{u1, u1} (Prod.{u1, u1} α α) (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasInsert.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Prod.mk.{u1, u1} α α a a) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (a : α), Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Insert.insert.{u1, u1} (Prod.{u1, u1} α α) (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instInsertFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Prod.mk.{u1, u1} α α a a) (Finset.diag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s))
Case conversion may be inaccurate. Consider using '#align finset.diag_insert Finset.diag_insertₓ'. -/
theorem diag_insert : (insert a s).diag = insert (a, a) s.diag := by
  rw [insert_eq, insert_eq, diag_union, diag_singleton]
#align finset.diag_insert Finset.diag_insert

/- warning: finset.off_diag_insert -> Finset.offDiag_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (a : α), (Not (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.hasInsert.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.hasUnion.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => Prod.decidableEq.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.product.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a) s)) (Finset.product.{u1, u1} α α s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] {s : Finset.{u1} α} (a : α), (Not (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s)) -> (Eq.{succ u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) (Insert.insert.{u1, u1} α (Finset.{u1} α) (Finset.instInsertFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b)) a s)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Union.union.{u1} (Finset.{u1} (Prod.{u1, u1} α α)) (Finset.instUnionFinset.{u1} (Prod.{u1, u1} α α) (fun (a : Prod.{u1, u1} α α) (b : Prod.{u1, u1} α α) => instDecidableEqProd.{u1, u1} α α (fun (a : α) (b : α) => _inst_1 a b) (fun (a : α) (b : α) => _inst_1 a b) a b)) (Finset.offDiag.{u1} α (fun (a : α) (b : α) => _inst_1 a b) s) (Finset.product.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a) s)) (Finset.product.{u1, u1} α α s (Singleton.singleton.{u1, u1} α (Finset.{u1} α) (Finset.instSingletonFinset.{u1} α) a))))
Case conversion may be inaccurate. Consider using '#align finset.off_diag_insert Finset.offDiag_insertₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem offDiag_insert (has : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} := by
  rw [insert_eq, union_comm, off_diag_union (disjoint_singleton_right.2 has), off_diag_singleton,
    union_empty, union_right_comm]
#align finset.off_diag_insert Finset.offDiag_insert

end Diag

end Finset

