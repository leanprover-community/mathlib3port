/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot

! This file was ported from Lean 3 source module data.set.prod
! leanprover-community/mathlib commit e001509c11c4d0f549d91d89da95b4a0b43c714f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Sets in product and pi types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the product of sets in `α × β` and in `Π i, α i` along with the diagonal of a
type.

## Main declarations

* `set.prod`: Binary product of sets. For `s : set α`, `t : set β`, we have
  `s.prod t : set (α × β)`.
* `set.diagonal`: Diagonal of a type. `set.diagonal α = {(x, x) | x : α}`.
* `set.off_diag`: Off-diagonal. `s ×ˢ s` without the diagonal.
* `set.pi`: Arbitrary product of sets.
-/


open Function

namespace Set

/-! ### Cartesian binary product of sets -/


section Prod

variable {α β γ δ : Type _} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

#print Set.prod /-
/-- The cartesian product `prod s t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
def prod (s : Set α) (t : Set β) : Set (α × β) :=
  { p | p.1 ∈ s ∧ p.2 ∈ t }
#align set.prod Set.prod
-/

-- mathport name: set.prod
infixr:82
  " ×ˢ " =>-- This notation binds more strongly than (pre)images, unions and intersections.
  Set.prod

/- warning: set.prod_eq -> Set.prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s) (Set.preimage.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instInterSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.preimage.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s) (Set.preimage.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) t))
Case conversion may be inaccurate. Consider using '#align set.prod_eq Set.prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq (s : Set α) (t : Set β) : s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t :=
  rfl
#align set.prod_eq Set.prod_eq

/- warning: set.mem_prod_eq -> Set.mem_prod_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {p : Prod.{u1, u2} α β}, Eq.{1} Prop (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p (Set.prod.{u1, u2} α β s t)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Prod.fst.{u1, u2} α β p) s) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (Prod.snd.{u1, u2} α β p) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {p : Prod.{u2, u1} α β}, Eq.{1} Prop (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) p (Set.prod.{u2, u1} α β s t)) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Prod.fst.{u2, u1} α β p) s) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (Prod.snd.{u2, u1} α β p) t))
Case conversion may be inaccurate. Consider using '#align set.mem_prod_eq Set.mem_prod_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mem_prod_eq {p : α × β} : (p ∈ s ×ˢ t) = (p.1 ∈ s ∧ p.2 ∈ t) :=
  rfl
#align set.mem_prod_eq Set.mem_prod_eq

/- warning: set.mem_prod -> Set.mem_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {p : Prod.{u1, u2} α β}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) p (Set.prod.{u1, u2} α β s t)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (Prod.fst.{u1, u2} α β p) s) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (Prod.snd.{u1, u2} α β p) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {p : Prod.{u2, u1} α β}, Iff (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) p (Set.prod.{u2, u1} α β s t)) (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (Prod.fst.{u2, u1} α β p) s) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (Prod.snd.{u2, u1} α β p) t))
Case conversion may be inaccurate. Consider using '#align set.mem_prod Set.mem_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mem_prod {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Iff.rfl
#align set.mem_prod Set.mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_mk_mem_set_prod_eq /-
@[simp]
theorem prod_mk_mem_set_prod_eq : ((a, b) ∈ s ×ˢ t) = (a ∈ s ∧ b ∈ t) :=
  rfl
#align set.prod_mk_mem_set_prod_eq Set.prod_mk_mem_set_prod_eq
-/

/- warning: set.mk_mem_prod -> Set.mk_mem_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α} {b : β}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) -> (Membership.mem.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.mk_mem_prod Set.mk_mem_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_mem_prod (ha : a ∈ s) (hb : b ∈ t) : (a, b) ∈ s ×ˢ t :=
  ⟨ha, hb⟩
#align set.mk_mem_prod Set.mk_mem_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.decidableMemProd /-
instance decidableMemProd [hs : DecidablePred (· ∈ s)] [ht : DecidablePred (· ∈ t)] :
    DecidablePred (· ∈ s ×ˢ t) := fun _ => And.decidable
#align set.decidable_mem_prod Set.decidableMemProd
-/

/- warning: set.prod_mono -> Set.prod_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s₁ t₁) (Set.prod.{u1, u2} α β s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) t₁ t₂) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s₁ t₁) (Set.prod.{u2, u1} α β s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.prod_mono Set.prod_monoₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ ×ˢ t₁ ⊆ s₂ ×ˢ t₂ := fun x ⟨h₁, h₂⟩ =>
  ⟨hs h₁, ht h₂⟩
#align set.prod_mono Set.prod_mono

/- warning: set.prod_mono_left -> Set.prod_mono_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s₁ t) (Set.prod.{u1, u2} α β s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) s₁ s₂) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s₁ t) (Set.prod.{u2, u1} α β s₂ t))
Case conversion may be inaccurate. Consider using '#align set.prod_mono_left Set.prod_mono_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_mono_left (hs : s₁ ⊆ s₂) : s₁ ×ˢ t ⊆ s₂ ×ˢ t :=
  prod_mono hs Subset.rfl
#align set.prod_mono_left Set.prod_mono_left

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_mono_right /-
theorem prod_mono_right (ht : t₁ ⊆ t₂) : s ×ˢ t₁ ⊆ s ×ˢ t₂ :=
  prod_mono Subset.rfl ht
#align set.prod_mono_right Set.prod_mono_right
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_self_subset_prod_self /-
@[simp]
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ ⊆ s₂ ×ˢ s₂ ↔ s₁ ⊆ s₂ :=
  ⟨fun h x hx => (h (mk_mem_prod hx hx)).1, fun h x hx => ⟨h hx.1, h hx.2⟩⟩
#align set.prod_self_subset_prod_self Set.prod_self_subset_prod_self
-/

/- warning: set.prod_self_ssubset_prod_self -> Set.prod_self_ssubset_prod_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSsubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s₁ s₁) (Set.prod.{u1, u1} α α s₂ s₂)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s₁ s₂)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSSubsetSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s₁ s₁) (Set.prod.{u1, u1} α α s₂ s₂)) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align set.prod_self_ssubset_prod_self Set.prod_self_ssubset_prod_selfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
  and_congr prod_self_subset_prod_self <| not_congr prod_self_subset_prod_self
#align set.prod_self_ssubset_prod_self Set.prod_self_ssubset_prod_self

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_subset_iff /-
theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t ⊆ P ↔ ∀ x ∈ s, ∀ y ∈ t, (x, y) ∈ P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩
#align set.prod_subset_iff Set.prod_subset_iff
-/

/- warning: set.forall_prod_set -> Set.forall_prod_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {p : (Prod.{u1, u2} α β) -> Prop}, Iff (forall (x : Prod.{u1, u2} α β), (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) x (Set.prod.{u1, u2} α β s t)) -> (p x)) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (p (Prod.mk.{u1, u2} α β x y))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {p : (Prod.{u2, u1} α β) -> Prop}, Iff (forall (x : Prod.{u2, u1} α β), (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) x (Set.prod.{u2, u1} α β s t)) -> (p x)) (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) -> (p (Prod.mk.{u2, u1} α β x y))))
Case conversion may be inaccurate. Consider using '#align set.forall_prod_set Set.forall_prod_setₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem forall_prod_set {p : α × β → Prop} : (∀ x ∈ s ×ˢ t, p x) ↔ ∀ x ∈ s, ∀ y ∈ t, p (x, y) :=
  prod_subset_iff
#align set.forall_prod_set Set.forall_prod_set

/- warning: set.exists_prod_set -> Set.exists_prod_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {p : (Prod.{u1, u2} α β) -> Prop}, Iff (Exists.{succ (max u1 u2)} (Prod.{u1, u2} α β) (fun (x : Prod.{u1, u2} α β) => Exists.{0} (Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) x (Set.prod.{u1, u2} α β s t)) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasMem.{max u1 u2} (Prod.{u1, u2} α β)) x (Set.prod.{u1, u2} α β s t)) => p x))) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Exists.{succ u2} β (fun (y : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) => p (Prod.mk.{u1, u2} α β x y))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {p : (Prod.{u2, u1} α β) -> Prop}, Iff (Exists.{succ (max u2 u1)} (Prod.{u2, u1} α β) (fun (x : Prod.{u2, u1} α β) => And (Membership.mem.{max u2 u1, max u1 u2} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instMembershipSet.{max u2 u1} (Prod.{u2, u1} α β)) x (Set.prod.{u2, u1} α β s t)) (p x))) (Exists.{succ u2} α (fun (x : α) => And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) (Exists.{succ u1} β (fun (y : β) => And (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) (p (Prod.mk.{u2, u1} α β x y))))))
Case conversion may be inaccurate. Consider using '#align set.exists_prod_set Set.exists_prod_setₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem exists_prod_set {p : α × β → Prop} : (∃ x ∈ s ×ˢ t, p x) ↔ ∃ x ∈ s, ∃ y ∈ t, p (x, y) := by
  simp [and_assoc']
#align set.exists_prod_set Set.exists_prod_set

/- warning: set.prod_empty -> Set.prod_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasEmptyc.{max u1 u2} (Prod.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instEmptyCollectionSet.{max u2 u1} (Prod.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align set.prod_empty Set.prod_emptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact and_false_iff _
#align set.prod_empty Set.prod_empty

/- warning: set.empty_prod -> Set.empty_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasEmptyc.{max u1 u2} (Prod.{u1, u2} α β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α)) t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instEmptyCollectionSet.{max u2 u1} (Prod.{u2, u1} α β)))
Case conversion may be inaccurate. Consider using '#align set.empty_prod Set.empty_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact false_and_iff _
#align set.empty_prod Set.empty_prod

/- warning: set.univ_prod_univ -> Set.univ_prod_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Set.univ.{u1} α) (Set.univ.{u2} β)) (Set.univ.{max u1 u2} (Prod.{u1, u2} α β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Set.univ.{u2} α) (Set.univ.{u1} β)) (Set.univ.{max u2 u1} (Prod.{u2, u1} α β))
Case conversion may be inaccurate. Consider using '#align set.univ_prod_univ Set.univ_prod_univₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ :=
  by
  ext
  exact true_and_iff _
#align set.univ_prod_univ Set.univ_prod_univ

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.univ_prod /-
theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]
#align set.univ_prod Set.univ_prod
-/

/- warning: set.prod_univ -> Set.prod_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Set.univ.{u2} β)) (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Set.univ.{u1} β)) (Set.preimage.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s)
Case conversion may be inaccurate. Consider using '#align set.prod_univ Set.prod_univₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]
#align set.prod_univ Set.prod_univ

/- warning: set.singleton_prod -> Set.singleton_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {t : Set.{u2} β} {a : α}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) t) (Set.image.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {t : Set.{u1} β} {a : α}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) t) (Set.image.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) t)
Case conversion may be inaccurate. Consider using '#align set.singleton_prod Set.singleton_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t :=
  by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align set.singleton_prod Set.singleton_prod

/- warning: set.prod_singleton -> Set.prod_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {b : β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (Set.image.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : α) => Prod.mk.{u1, u2} α β a b) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {b : β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (Set.image.{u2, max u1 u2} α (Prod.{u2, u1} α β) (fun (a : α) => Prod.mk.{u2, u1} α β a b) s)
Case conversion may be inaccurate. Consider using '#align set.prod_singleton Set.prod_singletonₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s :=
  by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]
#align set.prod_singleton Set.prod_singleton

/- warning: set.singleton_prod_singleton -> Set.singleton_prod_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} {b : β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b)) (Singleton.singleton.{max u1 u2, max u1 u2} (Prod.{u1, u2} α β) (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSingleton.{max u1 u2} (Prod.{u1, u2} α β)) (Prod.mk.{u1, u2} α β a b))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {a : α} {b : β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) a) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b)) (Singleton.singleton.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instSingletonSet.{max u2 u1} (Prod.{u2, u1} α β)) (Prod.mk.{u2, u1} α β a b))
Case conversion may be inaccurate. Consider using '#align set.singleton_prod_singleton Set.singleton_prod_singletonₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by simp
#align set.singleton_prod_singleton Set.singleton_prod_singleton

/- warning: set.union_prod -> Set.union_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s₁ t) (Set.prod.{u1, u2} α β s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet_1.{u2} α) s₁ s₂) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s₁ t) (Set.prod.{u2, u1} α β s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_prod Set.union_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem union_prod : (s₁ ∪ s₂) ×ˢ t = s₁ ×ˢ t ∪ s₂ ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp [or_and_right]
#align set.union_prod Set.union_prod

/- warning: set.prod_union -> Set.prod_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t₁) (Set.prod.{u1, u2} α β s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet_1.{u1} β) t₁ t₂)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t₁) (Set.prod.{u2, u1} α β s t₂))
Case conversion may be inaccurate. Consider using '#align set.prod_union Set.prod_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_union : s ×ˢ (t₁ ∪ t₂) = s ×ˢ t₁ ∪ s ×ˢ t₂ :=
  by
  ext ⟨x, y⟩
  simp [and_or_left]
#align set.prod_union Set.prod_union

/- warning: set.inter_prod -> Set.inter_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s₁ t) (Set.prod.{u1, u2} α β s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instInterSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s₁ t) (Set.prod.{u2, u1} α β s₂ t))
Case conversion may be inaccurate. Consider using '#align set.inter_prod Set.inter_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem inter_prod : (s₁ ∩ s₂) ×ˢ t = s₁ ×ˢ t ∩ s₂ ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]
#align set.inter_prod Set.inter_prod

/- warning: set.prod_inter -> Set.prod_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t₁) (Set.prod.{u1, u2} α β s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instInterSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t₁) (Set.prod.{u2, u1} α β s t₂))
Case conversion may be inaccurate. Consider using '#align set.prod_inter Set.prod_interₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_inter : s ×ˢ (t₁ ∩ t₂) = s ×ˢ t₁ ∩ s ×ˢ t₂ :=
  by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]
#align set.prod_inter Set.prod_inter

/- warning: set.prod_inter_prod -> Set.prod_inter_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasInter.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s₁ t₁) (Set.prod.{u1, u2} α β s₂ t₂)) (Set.prod.{u1, u2} α β (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instInterSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s₁ t₁) (Set.prod.{u2, u1} α β s₂ t₂)) (Set.prod.{u2, u1} α β (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet_1.{u2} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet_1.{u1} β) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.prod_inter_prod Set.prod_inter_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_inter_prod : s₁ ×ˢ t₁ ∩ s₂ ×ˢ t₂ = (s₁ ∩ s₂) ×ˢ (t₁ ∩ t₂) :=
  by
  ext ⟨x, y⟩
  simp [and_assoc', and_left_comm]
#align set.prod_inter_prod Set.prod_inter_prod

/- warning: set.disjoint_prod -> Set.disjoint_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Iff (Disjoint.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Prod.{u1, u2} α β))))))) (GeneralizedBooleanAlgebra.toOrderBot.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Prod.{u1, u2} α β)))) (Set.prod.{u1, u2} α β s₁ t₁) (Set.prod.{u1, u2} α β s₂ t₂)) (Or (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₁ s₂) (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))) t₁ t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Iff (Disjoint.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (BiheytingAlgebra.toCoheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (BooleanAlgebra.toBiheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instBooleanAlgebraSet.{max u1 u2} (Prod.{u1, u2} α β)))))))) (BoundedOrder.toOrderBot.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Preorder.toLE.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (PartialOrder.toPreorder.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (BiheytingAlgebra.toCoheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (BooleanAlgebra.toBiheytingAlgebra.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instBooleanAlgebraSet.{max u1 u2} (Prod.{u1, u2} α β)))))))))) (BooleanAlgebra.toBoundedOrder.{max u1 u2} (Set.{max u2 u1} (Prod.{u1, u2} α β)) (Set.instBooleanAlgebraSet.{max u1 u2} (Prod.{u1, u2} α β)))) (Set.prod.{u1, u2} α β s₁ t₁) (Set.prod.{u1, u2} α β s₂ t₂)) (Or (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s₁ s₂) (Disjoint.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} β) (Preorder.toLE.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β))) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.disjoint_prod Set.disjoint_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_left, mem_prod, not_and_or, Prod.forall, and_imp, ← @forall_or_right α, ←
    @forall_or_left β, ← @forall_or_right (_ ∈ s₁), ← @forall_or_left (_ ∈ t₁)]
#align set.disjoint_prod Set.disjoint_prod

/- warning: set.insert_prod -> Set.insert_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.image.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) t) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β (Insert.insert.{u2, u2} α (Set.{u2} α) (Set.instInsertSet.{u2} α) a s) t) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.image.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) t) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.insert_prod Set.insert_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t ∪ s ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) [image, iff_def, or_imp, Imp.swap]
#align set.insert_prod Set.insert_prod

/- warning: set.prod_insert -> Set.prod_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {b : β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (Insert.insert.{u2, u2} β (Set.{u2} β) (Set.hasInsert.{u2} β) b t)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.image.{u1, max u1 u2} α (Prod.{u1, u2} α β) (fun (a : α) => Prod.mk.{u1, u2} α β a b) s) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {b : β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (Insert.insert.{u1, u1} β (Set.{u1} β) (Set.instInsertSet.{u1} β) b t)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.image.{u2, max u1 u2} α (Prod.{u2, u1} α β) (fun (a : α) => Prod.mk.{u2, u1} α β a b) s) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.prod_insert Set.prod_insertₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s ∪ s ×ˢ t :=
  by
  ext ⟨x, y⟩
  simp (config := { contextual := true }) [image, iff_def, or_imp, Imp.swap]
#align set.prod_insert Set.prod_insert

/- warning: set.prod_preimage_eq -> Set.prod_preimage_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {s : Set.{u1} α} {t : Set.{u2} β} {f : γ -> α} {g : δ -> β}, Eq.{succ (max u3 u4)} (Set.{max u3 u4} (Prod.{u3, u4} γ δ)) (Set.prod.{u3, u4} γ δ (Set.preimage.{u3, u1} γ α f s) (Set.preimage.{u4, u2} δ β g t)) (Set.preimage.{max u3 u4, max u1 u2} (Prod.{u3, u4} γ δ) (Prod.{u1, u2} α β) (fun (p : Prod.{u3, u4} γ δ) => Prod.mk.{u1, u2} α β (f (Prod.fst.{u3, u4} γ δ p)) (g (Prod.snd.{u3, u4} γ δ p))) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} {s : Set.{u2} α} {t : Set.{u1} β} {f : γ -> α} {g : δ -> β}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} γ δ)) (Set.prod.{u4, u3} γ δ (Set.preimage.{u4, u2} γ α f s) (Set.preimage.{u3, u1} δ β g t)) (Set.preimage.{max u4 u3, max u1 u2} (Prod.{u4, u3} γ δ) (Prod.{u2, u1} α β) (fun (p : Prod.{u4, u3} γ δ) => Prod.mk.{u2, u1} α β (f (Prod.fst.{u4, u3} γ δ p)) (g (Prod.snd.{u4, u3} γ δ p))) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.prod_preimage_eq Set.prod_preimage_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_eq Set.prod_preimage_eq

/- warning: set.prod_preimage_left -> Set.prod_preimage_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {f : γ -> α}, Eq.{succ (max u3 u2)} (Set.{max u3 u2} (Prod.{u3, u2} γ β)) (Set.prod.{u3, u2} γ β (Set.preimage.{u3, u1} γ α f s) t) (Set.preimage.{max u3 u2, max u1 u2} (Prod.{u3, u2} γ β) (Prod.{u1, u2} α β) (fun (p : Prod.{u3, u2} γ β) => Prod.mk.{u1, u2} α β (f (Prod.fst.{u3, u2} γ β p)) (Prod.snd.{u3, u2} γ β p)) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {f : γ -> α}, Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (Prod.{u2, u3} γ β)) (Set.prod.{u2, u3} γ β (Set.preimage.{u2, u1} γ α f s) t) (Set.preimage.{max u3 u2, max u3 u1} (Prod.{u2, u3} γ β) (Prod.{u1, u3} α β) (fun (p : Prod.{u2, u3} γ β) => Prod.mk.{u1, u3} α β (f (Prod.fst.{u2, u3} γ β p)) (Prod.snd.{u2, u3} γ β p)) (Set.prod.{u1, u3} α β s t))
Case conversion may be inaccurate. Consider using '#align set.prod_preimage_left Set.prod_preimage_leftₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_preimage_left {f : γ → α} :
    (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_left Set.prod_preimage_left

/- warning: set.prod_preimage_right -> Set.prod_preimage_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {g : δ -> β}, Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Prod.{u1, u3} α δ)) (Set.prod.{u1, u3} α δ s (Set.preimage.{u3, u2} δ β g t)) (Set.preimage.{max u1 u3, max u1 u2} (Prod.{u1, u3} α δ) (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u3} α δ) => Prod.mk.{u1, u2} α β (Prod.fst.{u1, u3} α δ p) (g (Prod.snd.{u1, u3} α δ p))) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {δ : Type.{u2}} {s : Set.{u3} α} {t : Set.{u1} β} {g : δ -> β}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Prod.{u3, u2} α δ)) (Set.prod.{u3, u2} α δ s (Set.preimage.{u2, u1} δ β g t)) (Set.preimage.{max u3 u2, max u1 u3} (Prod.{u3, u2} α δ) (Prod.{u3, u1} α β) (fun (p : Prod.{u3, u2} α δ) => Prod.mk.{u3, u1} α β (Prod.fst.{u3, u2} α δ p) (g (Prod.snd.{u3, u2} α δ p))) (Set.prod.{u3, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.prod_preimage_right Set.prod_preimage_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_preimage_right {g : δ → β} :
    s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl
#align set.prod_preimage_right Set.prod_preimage_right

/- warning: set.preimage_prod_map_prod -> Set.preimage_prod_map_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} (f : α -> β) (g : γ -> δ) (s : Set.{u2} β) (t : Set.{u4} δ), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Prod.{u1, u3} α γ)) (Set.preimage.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.map.{u1, u2, u3, u4} α β γ δ f g) (Set.prod.{u2, u4} β δ s t)) (Set.prod.{u1, u3} α γ (Set.preimage.{u1, u2} α β f s) (Set.preimage.{u3, u4} γ δ g t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u4}} {γ : Type.{u1}} {δ : Type.{u3}} (f : α -> β) (g : γ -> δ) (s : Set.{u4} β) (t : Set.{u3} δ), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α γ)) (Set.preimage.{max u1 u2, max u3 u4} (Prod.{u2, u1} α γ) (Prod.{u4, u3} β δ) (Prod.map.{u2, u4, u1, u3} α β γ δ f g) (Set.prod.{u4, u3} β δ s t)) (Set.prod.{u2, u1} α γ (Set.preimage.{u2, u4} α β f s) (Set.preimage.{u1, u3} γ δ g t))
Case conversion may be inaccurate. Consider using '#align set.preimage_prod_map_prod Set.preimage_prod_map_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem preimage_prod_map_prod (f : α → β) (g : γ → δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl
#align set.preimage_prod_map_prod Set.preimage_prod_map_prod

/- warning: set.mk_preimage_prod -> Set.mk_preimage_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} (f : γ -> α) (g : γ -> β), Eq.{succ u3} (Set.{u3} γ) (Set.preimage.{u3, max u1 u2} γ (Prod.{u1, u2} α β) (fun (x : γ) => Prod.mk.{u1, u2} α β (f x) (g x)) (Set.prod.{u1, u2} α β s t)) (Inter.inter.{u3} (Set.{u3} γ) (Set.hasInter.{u3} γ) (Set.preimage.{u3, u1} γ α f s) (Set.preimage.{u3, u2} γ β g t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} (f : γ -> α) (g : γ -> β), Eq.{succ u3} (Set.{u3} γ) (Set.preimage.{u3, max u2 u1} γ (Prod.{u1, u2} α β) (fun (x : γ) => Prod.mk.{u1, u2} α β (f x) (g x)) (Set.prod.{u1, u2} α β s t)) (Inter.inter.{u3} (Set.{u3} γ) (Set.instInterSet_1.{u3} γ) (Set.preimage.{u3, u1} γ α f s) (Set.preimage.{u3, u2} γ β g t))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod Set.mk_preimage_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_preimage_prod (f : γ → α) (g : γ → β) :
    (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s ∩ g ⁻¹' t :=
  rfl
#align set.mk_preimage_prod Set.mk_preimage_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.mk_preimage_prod_left /-
@[simp]
theorem mk_preimage_prod_left (hb : b ∈ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s :=
  by
  ext a
  simp [hb]
#align set.mk_preimage_prod_left Set.mk_preimage_prod_left
-/

/- warning: set.mk_preimage_prod_right -> Set.mk_preimage_prod_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) (Set.prod.{u1, u2} α β s t)) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) (Set.prod.{u2, u1} α β s t)) t)
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod_right Set.mk_preimage_prod_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mk_preimage_prod_right (ha : a ∈ s) : Prod.mk a ⁻¹' s ×ˢ t = t :=
  by
  ext b
  simp [ha]
#align set.mk_preimage_prod_right Set.mk_preimage_prod_right

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.mk_preimage_prod_left_eq_empty /-
@[simp]
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ :=
  by
  ext a
  simp [hb]
#align set.mk_preimage_prod_left_eq_empty Set.mk_preimage_prod_left_eq_empty
-/

/- warning: set.mk_preimage_prod_right_eq_empty -> Set.mk_preimage_prod_right_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) (Set.prod.{u1, u2} α β s t)) (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α}, (Not (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s)) -> (Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) (Set.prod.{u2, u1} α β s t)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β)))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod_right_eq_empty Set.mk_preimage_prod_right_eq_emptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ :=
  by
  ext b
  simp [ha]
#align set.mk_preimage_prod_right_eq_empty Set.mk_preimage_prod_right_eq_empty

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.mk_preimage_prod_left_eq_if /-
theorem mk_preimage_prod_left_eq_if [DecidablePred (· ∈ t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b ∈ t then s else ∅ := by split_ifs <;> simp [h]
#align set.mk_preimage_prod_left_eq_if Set.mk_preimage_prod_left_eq_if
-/

/- warning: set.mk_preimage_prod_right_eq_if -> Set.mk_preimage_prod_right_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α} [_inst_1 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)], Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) (Set.prod.{u1, u2} α β s t)) (ite.{succ u2} (Set.{u2} β) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α} [_inst_1 : DecidablePred.{succ u2} α (fun (_x : α) => Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) _x s)], Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) (Set.prod.{u2, u1} α β s t)) (ite.{succ u1} (Set.{u1} β) (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (_inst_1 a) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β)))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod_right_eq_if Set.mk_preimage_prod_right_eq_ifₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_preimage_prod_right_eq_if [DecidablePred (· ∈ s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a ∈ s then t else ∅ := by split_ifs <;> simp [h]
#align set.mk_preimage_prod_right_eq_if Set.mk_preimage_prod_right_eq_if

/- warning: set.mk_preimage_prod_left_fn_eq_if -> Set.mk_preimage_prod_left_fn_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {b : β} [_inst_1 : DecidablePred.{succ u2} β (fun (_x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) _x t)] (f : γ -> α), Eq.{succ u3} (Set.{u3} γ) (Set.preimage.{u3, max u1 u2} γ (Prod.{u1, u2} α β) (fun (a : γ) => Prod.mk.{u1, u2} α β (f a) b) (Set.prod.{u1, u2} α β s t)) (ite.{succ u3} (Set.{u3} γ) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) (_inst_1 b) (Set.preimage.{u3, u1} γ α f s) (EmptyCollection.emptyCollection.{u3} (Set.{u3} γ) (Set.hasEmptyc.{u3} γ)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {s : Set.{u1} α} {t : Set.{u3} β} {b : β} [_inst_1 : DecidablePred.{succ u3} β (fun (_x : β) => Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) _x t)] (f : γ -> α), Eq.{succ u2} (Set.{u2} γ) (Set.preimage.{u2, max u3 u1} γ (Prod.{u1, u3} α β) (fun (a : γ) => Prod.mk.{u1, u3} α β (f a) b) (Set.prod.{u1, u3} α β s t)) (ite.{succ u2} (Set.{u2} γ) (Membership.mem.{u3, u3} β (Set.{u3} β) (Set.instMembershipSet.{u3} β) b t) (_inst_1 b) (Set.preimage.{u2, u1} γ α f s) (EmptyCollection.emptyCollection.{u2} (Set.{u2} γ) (Set.instEmptyCollectionSet.{u2} γ)))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod_left_fn_eq_if Set.mk_preimage_prod_left_fn_eq_ifₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· ∈ t)] (f : γ → α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b ∈ t then f ⁻¹' s else ∅ := by
  rw [← mk_preimage_prod_left_eq_if, prod_preimage_left, preimage_preimage]
#align set.mk_preimage_prod_left_fn_eq_if Set.mk_preimage_prod_left_fn_eq_if

/- warning: set.mk_preimage_prod_right_fn_eq_if -> Set.mk_preimage_prod_right_fn_eq_if is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α} [_inst_1 : DecidablePred.{succ u1} α (fun (_x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) _x s)] (g : δ -> β), Eq.{succ u3} (Set.{u3} δ) (Set.preimage.{u3, max u1 u2} δ (Prod.{u1, u2} α β) (fun (b : δ) => Prod.mk.{u1, u2} α β a (g b)) (Set.prod.{u1, u2} α β s t)) (ite.{succ u3} (Set.{u3} δ) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (_inst_1 a) (Set.preimage.{u3, u2} δ β g t) (EmptyCollection.emptyCollection.{u3} (Set.{u3} δ) (Set.hasEmptyc.{u3} δ)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {δ : Type.{u2}} {s : Set.{u3} α} {t : Set.{u1} β} {a : α} [_inst_1 : DecidablePred.{succ u3} α (fun (_x : α) => Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) _x s)] (g : δ -> β), Eq.{succ u2} (Set.{u2} δ) (Set.preimage.{u2, max u1 u3} δ (Prod.{u3, u1} α β) (fun (b : δ) => Prod.mk.{u3, u1} α β a (g b)) (Set.prod.{u3, u1} α β s t)) (ite.{succ u2} (Set.{u2} δ) (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) a s) (_inst_1 a) (Set.preimage.{u2, u1} δ β g t) (EmptyCollection.emptyCollection.{u2} (Set.{u2} δ) (Set.instEmptyCollectionSet.{u2} δ)))
Case conversion may be inaccurate. Consider using '#align set.mk_preimage_prod_right_fn_eq_if Set.mk_preimage_prod_right_fn_eq_ifₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· ∈ s)] (g : δ → β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a ∈ s then g ⁻¹' t else ∅ := by
  rw [← mk_preimage_prod_right_eq_if, prod_preimage_right, preimage_preimage]
#align set.mk_preimage_prod_right_fn_eq_if Set.mk_preimage_prod_right_fn_eq_if

/- warning: set.preimage_swap_prod -> Set.preimage_swap_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u2 u1)} (Set.{max u2 u1} (Prod.{u2, u1} β α)) (Set.preimage.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.swap.{u2, u1} β α) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u2, u1} β α t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (Prod.{u1, u2} β α)) (Set.preimage.{max u2 u1, max u2 u1} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (Prod.swap.{u1, u2} β α) (Set.prod.{u2, u1} α β s t)) (Set.prod.{u1, u2} β α t s)
Case conversion may be inaccurate. Consider using '#align set.preimage_swap_prod Set.preimage_swap_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s :=
  by
  ext ⟨x, y⟩
  simp [and_comm']
#align set.preimage_swap_prod Set.preimage_swap_prod

/- warning: set.image_swap_prod -> Set.image_swap_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ (max u2 u1)} (Set.{max u2 u1} (Prod.{u2, u1} β α)) (Set.image.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.swap.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) (Set.prod.{u2, u1} β α t s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u1, u2} β α)) (Set.image.{max u1 u2, max u1 u2} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (Prod.swap.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) (Set.prod.{u1, u2} β α t s)
Case conversion may be inaccurate. Consider using '#align set.image_swap_prod Set.image_swap_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap, preimage_swap_prod]
#align set.image_swap_prod Set.image_swap_prod

/- warning: set.prod_image_image_eq -> Set.prod_image_image_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {s : Set.{u1} α} {t : Set.{u2} β} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{succ (max u3 u4)} (Set.{max u3 u4} (Prod.{u3, u4} γ δ)) (Set.prod.{u3, u4} γ δ (Set.image.{u1, u3} α γ m₁ s) (Set.image.{u2, u4} β δ m₂ t)) (Set.image.{max u1 u2, max u3 u4} (Prod.{u1, u2} α β) (Prod.{u3, u4} γ δ) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} γ δ (m₁ (Prod.fst.{u1, u2} α β p)) (m₂ (Prod.snd.{u1, u2} α β p))) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} {s : Set.{u2} α} {t : Set.{u1} β} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} γ δ)) (Set.prod.{u4, u3} γ δ (Set.image.{u2, u4} α γ m₁ s) (Set.image.{u1, u3} β δ m₂ t)) (Set.image.{max u2 u1, max u3 u4} (Prod.{u2, u1} α β) (Prod.{u4, u3} γ δ) (fun (p : Prod.{u2, u1} α β) => Prod.mk.{u4, u3} γ δ (m₁ (Prod.fst.{u2, u1} α β p)) (m₂ (Prod.snd.{u2, u1} α β p))) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.prod_image_image_eq Set.prod_image_image_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
  ext <| by
    simp [-exists_and_right, exists_and_distrib_right.symm, and_left_comm, and_assoc, and_comm]
#align set.prod_image_image_eq Set.prod_image_image_eq

/- warning: set.prod_range_range_eq -> Set.prod_range_range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{succ (max u3 u4)} (Set.{max u3 u4} (Prod.{u3, u4} γ δ)) (Set.prod.{u3, u4} γ δ (Set.range.{u3, succ u1} γ α m₁) (Set.range.{u4, succ u2} δ β m₂)) (Set.range.{max u3 u4, max (succ u1) (succ u2)} (Prod.{u3, u4} γ δ) (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u4} γ δ (m₁ (Prod.fst.{u1, u2} α β p)) (m₂ (Prod.snd.{u1, u2} α β p))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u4}} {δ : Type.{u3}} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} γ δ)) (Set.prod.{u4, u3} γ δ (Set.range.{u4, succ u2} γ α m₁) (Set.range.{u3, succ u1} δ β m₂)) (Set.range.{max u3 u4, max (succ u2) (succ u1)} (Prod.{u4, u3} γ δ) (Prod.{u2, u1} α β) (fun (p : Prod.{u2, u1} α β) => Prod.mk.{u4, u3} γ δ (m₁ (Prod.fst.{u2, u1} α β p)) (m₂ (Prod.snd.{u2, u1} α β p))))
Case conversion may be inaccurate. Consider using '#align set.prod_range_range_eq Set.prod_range_range_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_range_range_eq {m₁ : α → γ} {m₂ : β → δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
  ext <| by simp [range]
#align set.prod_range_range_eq Set.prod_range_range_eq

/- warning: set.range_prod_map -> Set.range_prod_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{succ (max u3 u4)} (Set.{max u3 u4} (Prod.{u3, u4} γ δ)) (Set.range.{max u3 u4, max (succ u1) (succ u2)} (Prod.{u3, u4} γ δ) (Prod.{u1, u2} α β) (Prod.map.{u1, u3, u2, u4} α γ β δ m₁ m₂)) (Set.prod.{u3, u4} γ δ (Set.range.{u3, succ u1} γ α m₁) (Set.range.{u4, succ u2} δ β m₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} {m₁ : α -> γ} {m₂ : β -> δ}, Eq.{max (succ u4) (succ u3)} (Set.{max u3 u4} (Prod.{u4, u3} γ δ)) (Set.range.{max u3 u4, max (succ u2) (succ u1)} (Prod.{u4, u3} γ δ) (Prod.{u1, u2} α β) (Prod.map.{u1, u4, u2, u3} α γ β δ m₁ m₂)) (Set.prod.{u4, u3} γ δ (Set.range.{u4, succ u1} γ α m₁) (Set.range.{u3, succ u2} δ β m₂))
Case conversion may be inaccurate. Consider using '#align set.range_prod_map Set.range_prod_mapₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem range_prod_map {m₁ : α → γ} {m₂ : β → δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm
#align set.range_prod_map Set.range_prod_map

/- warning: set.prod_range_univ_eq -> Set.prod_range_univ_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {m₁ : α -> γ}, Eq.{succ (max u3 u2)} (Set.{max u3 u2} (Prod.{u3, u2} γ β)) (Set.prod.{u3, u2} γ β (Set.range.{u3, succ u1} γ α m₁) (Set.univ.{u2} β)) (Set.range.{max u3 u2, max (succ u1) (succ u2)} (Prod.{u3, u2} γ β) (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u3, u2} γ β (m₁ (Prod.fst.{u1, u2} α β p)) (Prod.snd.{u1, u2} α β p)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} {m₁ : α -> γ}, Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (Prod.{u2, u3} γ β)) (Set.prod.{u2, u3} γ β (Set.range.{u2, succ u1} γ α m₁) (Set.univ.{u3} β)) (Set.range.{max u3 u2, max (succ u1) (succ u3)} (Prod.{u2, u3} γ β) (Prod.{u1, u3} α β) (fun (p : Prod.{u1, u3} α β) => Prod.mk.{u2, u3} γ β (m₁ (Prod.fst.{u1, u3} α β p)) (Prod.snd.{u1, u3} α β p)))
Case conversion may be inaccurate. Consider using '#align set.prod_range_univ_eq Set.prod_range_univ_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_range_univ_eq {m₁ : α → γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
  ext <| by simp [range]
#align set.prod_range_univ_eq Set.prod_range_univ_eq

/- warning: set.prod_univ_range_eq -> Set.prod_univ_range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {δ : Type.{u3}} {m₂ : β -> δ}, Eq.{succ (max u1 u3)} (Set.{max u1 u3} (Prod.{u1, u3} α δ)) (Set.prod.{u1, u3} α δ (Set.univ.{u1} α) (Set.range.{u3, succ u2} δ β m₂)) (Set.range.{max u1 u3, max (succ u1) (succ u2)} (Prod.{u1, u3} α δ) (Prod.{u1, u2} α β) (fun (p : Prod.{u1, u2} α β) => Prod.mk.{u1, u3} α δ (Prod.fst.{u1, u2} α β p) (m₂ (Prod.snd.{u1, u2} α β p))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {δ : Type.{u2}} {m₂ : β -> δ}, Eq.{max (succ u3) (succ u2)} (Set.{max u2 u3} (Prod.{u3, u2} α δ)) (Set.prod.{u3, u2} α δ (Set.univ.{u3} α) (Set.range.{u2, succ u1} δ β m₂)) (Set.range.{max u2 u3, max (succ u3) (succ u1)} (Prod.{u3, u2} α δ) (Prod.{u3, u1} α β) (fun (p : Prod.{u3, u1} α β) => Prod.mk.{u3, u2} α δ (Prod.fst.{u3, u1} α β p) (m₂ (Prod.snd.{u3, u1} α β p))))
Case conversion may be inaccurate. Consider using '#align set.prod_univ_range_eq Set.prod_univ_range_eqₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_univ_range_eq {m₂ : β → δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
  ext <| by simp [range]
#align set.prod_univ_range_eq Set.prod_univ_range_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.range_pair_subset /-
theorem range_pair_subset (f : α → β) (g : α → γ) :
    (range fun x => (f x, g x)) ⊆ range f ×ˢ range g :=
  by
  have : (fun x => (f x, g x)) = Prod.map f g ∘ fun x => (x, x) := funext fun x => rfl
  rw [this, ← range_prod_map]
  apply range_comp_subset_range
#align set.range_pair_subset Set.range_pair_subset
-/

/- warning: set.nonempty.prod -> Set.Nonempty.prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.prod Set.Nonempty.prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.prod : s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩
#align set.nonempty.prod Set.Nonempty.prod

/- warning: set.nonempty.fst -> Set.Nonempty.fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) -> (Set.Nonempty.{u2} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.fst Set.Nonempty.fstₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.fst : (s ×ˢ t).Nonempty → s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
#align set.nonempty.fst Set.Nonempty.fst

/- warning: set.nonempty.snd -> Set.Nonempty.snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Set.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) -> (Set.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align set.nonempty.snd Set.Nonempty.sndₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Nonempty.snd : (s ×ˢ t).Nonempty → t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩
#align set.nonempty.snd Set.Nonempty.snd

/- warning: set.prod_nonempty_iff -> Set.prod_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) (And (Set.Nonempty.{u1} α s) (Set.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) (And (Set.Nonempty.{u2} α s) (Set.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align set.prod_nonempty_iff Set.prod_nonempty_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.Prod h.2⟩
#align set.prod_nonempty_iff Set.prod_nonempty_iff

/- warning: set.prod_eq_empty_iff -> Set.prod_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β}, Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasEmptyc.{max u1 u2} (Prod.{u1, u2} α β)))) (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β}, Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instEmptyCollectionSet.{max u2 u1} (Prod.{u2, u1} α β)))) (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{succ u1} (Set.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))))
Case conversion may be inaccurate. Consider using '#align set.prod_eq_empty_iff Set.prod_eq_empty_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]
#align set.prod_eq_empty_iff Set.prod_eq_empty_iff

/- warning: set.prod_sub_preimage_iff -> Set.prod_sub_preimage_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} {t : Set.{u2} β} {W : Set.{u3} γ} {f : (Prod.{u1, u2} α β) -> γ}, Iff (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.preimage.{max u1 u2, u3} (Prod.{u1, u2} α β) γ f W)) (forall (a : α) (b : β), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Membership.Mem.{u3, u3} γ (Set.{u3} γ) (Set.hasMem.{u3} γ) (f (Prod.mk.{u1, u2} α β a b)) W))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {γ : Type.{u3}} {s : Set.{u2} α} {t : Set.{u1} β} {W : Set.{u3} γ} {f : (Prod.{u2, u1} α β) -> γ}, Iff (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.preimage.{max u2 u1, u3} (Prod.{u2, u1} α β) γ f W)) (forall (a : α) (b : β), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) -> (Membership.mem.{u3, u3} γ (Set.{u3} γ) (Set.instMembershipSet.{u3} γ) (f (Prod.mk.{u2, u1} α β a b)) W))
Case conversion may be inaccurate. Consider using '#align set.prod_sub_preimage_iff Set.prod_sub_preimage_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_sub_preimage_iff {W : Set γ} {f : α × β → γ} :
    s ×ˢ t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W := by simp [subset_def]
#align set.prod_sub_preimage_iff Set.prod_sub_preimage_iff

/- warning: set.image_prod_mk_subset_prod -> Set.image_prod_mk_subset_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {f : α -> β} {g : α -> γ} {s : Set.{u1} α}, HasSubset.Subset.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.hasSubset.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.image.{u1, max u2 u3} α (Prod.{u2, u3} β γ) (fun (x : α) => Prod.mk.{u2, u3} β γ (f x) (g x)) s) (Set.prod.{u2, u3} β γ (Set.image.{u1, u2} α β f s) (Set.image.{u1, u3} α γ g s))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} {f : α -> β} {g : α -> γ} {s : Set.{u3} α}, HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (Prod.{u1, u2} β γ)) (Set.instHasSubsetSet_1.{max u1 u2} (Prod.{u1, u2} β γ)) (Set.image.{u3, max u2 u1} α (Prod.{u1, u2} β γ) (fun (x : α) => Prod.mk.{u1, u2} β γ (f x) (g x)) s) (Set.prod.{u1, u2} β γ (Set.image.{u3, u1} α β f s) (Set.image.{u3, u2} α γ g s))
Case conversion may be inaccurate. Consider using '#align set.image_prod_mk_subset_prod Set.image_prod_mk_subset_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_prod_mk_subset_prod {f : α → β} {g : α → γ} {s : Set α} :
    (fun x => (f x, g x)) '' s ⊆ (f '' s) ×ˢ (g '' s) :=
  by
  rintro _ ⟨x, hx, rfl⟩
  exact mk_mem_prod (mem_image_of_mem f hx) (mem_image_of_mem g hx)
#align set.image_prod_mk_subset_prod Set.image_prod_mk_subset_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.image_prod_mk_subset_prod_left /-
theorem image_prod_mk_subset_prod_left (hb : b ∈ t) : (fun a => (a, b)) '' s ⊆ s ×ˢ t :=
  by
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨ha, hb⟩
#align set.image_prod_mk_subset_prod_left Set.image_prod_mk_subset_prod_left
-/

/- warning: set.image_prod_mk_subset_prod_right -> Set.image_prod_mk_subset_prod_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {t : Set.{u2} β} {a : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.image.{u2, max u1 u2} β (Prod.{u1, u2} α β) (Prod.mk.{u1, u2} α β a) t) (Set.prod.{u1, u2} α β s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {t : Set.{u1} β} {a : α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.image.{u1, max u1 u2} β (Prod.{u2, u1} α β) (Prod.mk.{u2, u1} α β a) t) (Set.prod.{u2, u1} α β s t))
Case conversion may be inaccurate. Consider using '#align set.image_prod_mk_subset_prod_right Set.image_prod_mk_subset_prod_rightₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_prod_mk_subset_prod_right (ha : a ∈ s) : Prod.mk a '' t ⊆ s ×ˢ t :=
  by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨ha, hb⟩
#align set.image_prod_mk_subset_prod_right Set.image_prod_mk_subset_prod_right

/- warning: set.prod_subset_preimage_fst -> Set.prod_subset_preimage_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.preimage.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.preimage.{max u2 u1, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) s)
Case conversion may be inaccurate. Consider using '#align set.prod_subset_preimage_fst Set.prod_subset_preimage_fstₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.fst ⁻¹' s :=
  inter_subset_left _ _
#align set.prod_subset_preimage_fst Set.prod_subset_preimage_fst

/- warning: set.fst_image_prod_subset -> Set.fst_image_prod_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.image.{max u1 u2, u1} (Prod.{u1, u2} α β) α (Prod.fst.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet_1.{u2} α) (Set.image.{max u1 u2, u2} (Prod.{u2, u1} α β) α (Prod.fst.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) s
Case conversion may be inaccurate. Consider using '#align set.fst_image_prod_subset Set.fst_image_prod_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t ⊆ s :=
  image_subset_iff.2 <| prod_subset_preimage_fst s t
#align set.fst_image_prod_subset Set.fst_image_prod_subset

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.fst_image_prod /-
theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩
#align set.fst_image_prod Set.fst_image_prod
-/

/- warning: set.prod_subset_preimage_snd -> Set.prod_subset_preimage_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasSubset.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.preimage.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instHasSubsetSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.preimage.{max u2 u1, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) t)
Case conversion may be inaccurate. Consider using '#align set.prod_subset_preimage_snd Set.prod_subset_preimage_sndₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t ⊆ Prod.snd ⁻¹' t :=
  inter_subset_right _ _
#align set.prod_subset_preimage_snd Set.prod_subset_preimage_snd

/- warning: set.snd_image_prod_subset -> Set.snd_image_prod_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (s : Set.{u1} α) (t : Set.{u2} β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) t
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (s : Set.{u2} α) (t : Set.{u1} β), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet_1.{u1} β) (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) t
Case conversion may be inaccurate. Consider using '#align set.snd_image_prod_subset Set.snd_image_prod_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t ⊆ t :=
  image_subset_iff.2 <| prod_subset_preimage_snd s t
#align set.snd_image_prod_subset Set.snd_image_prod_subset

/- warning: set.snd_image_prod -> Set.snd_image_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (forall (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{max u1 u2, u2} (Prod.{u1, u2} α β) β (Prod.snd.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (forall (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{max u1 u2, u1} (Prod.{u2, u1} α β) β (Prod.snd.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) t)
Case conversion may be inaccurate. Consider using '#align set.snd_image_prod Set.snd_image_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩
#align set.snd_image_prod Set.snd_image_prod

/- warning: set.prod_diff_prod -> Set.prod_diff_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {t : Set.{u2} β} {t₁ : Set.{u2} β}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (BooleanAlgebra.toHasSdiff.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.booleanAlgebra.{max u1 u2} (Prod.{u1, u2} α β))) (Set.prod.{u1, u2} α β s t) (Set.prod.{u1, u2} α β s₁ t₁)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.hasUnion.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) t t₁)) (Set.prod.{u1, u2} α β (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s₁) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {t : Set.{u1} β} {t₁ : Set.{u1} β}, Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (SDiff.sdiff.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instSDiffSet.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.prod.{u2, u1} α β s₁ t₁)) (Union.union.{max u1 u2} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.instUnionSet_1.{max u2 u1} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) t t₁)) (Set.prod.{u2, u1} α β (SDiff.sdiff.{u2} (Set.{u2} α) (Set.instSDiffSet.{u2} α) s s₁) t))
Case conversion may be inaccurate. Consider using '#align set.prod_diff_prod Set.prod_diff_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_diff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) ∪ (s \ s₁) ×ˢ t :=
  by
  ext x
  by_cases h₁ : x.1 ∈ s₁ <;> by_cases h₂ : x.2 ∈ t₁ <;> simp [*]
#align set.prod_diff_prod Set.prod_diff_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_subset_prod_iff /-
/-- A product set is included in a product set if and only factors are included, or a factor of the
first set is empty. -/
theorem prod_subset_prod_iff : s ×ˢ t ⊆ s₁ ×ˢ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ :=
  by
  cases' (s ×ˢ t).eq_empty_or_nonempty with h h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.nonempty ∧ t.nonempty := by rwa [prod_nonempty_iff] at h
  refine' ⟨fun H => Or.inl ⟨_, _⟩, _⟩
  · have := image_subset (Prod.fst : α × β → α) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
  · have := image_subset (Prod.snd : α × β → β) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
  · intro H
    simp only [st.1.ne_empty, st.2.ne_empty, or_false_iff] at H
    exact prod_mono H.1 H.2
#align set.prod_subset_prod_iff Set.prod_subset_prod_iff
-/

/- warning: set.prod_eq_prod_iff_of_nonempty -> Set.prod_eq_prod_iff_of_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {t : Set.{u2} β} {t₁ : Set.{u2} β}, (Set.Nonempty.{max u1 u2} (Prod.{u1, u2} α β) (Set.prod.{u1, u2} α β s t)) -> (Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.prod.{u1, u2} α β s₁ t₁)) (And (Eq.{succ u1} (Set.{u1} α) s s₁) (Eq.{succ u2} (Set.{u2} β) t t₁)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {t : Set.{u1} β} {t₁ : Set.{u1} β}, (Set.Nonempty.{max u2 u1} (Prod.{u2, u1} α β) (Set.prod.{u2, u1} α β s t)) -> (Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.prod.{u2, u1} α β s₁ t₁)) (And (Eq.{succ u2} (Set.{u2} α) s s₁) (Eq.{succ u1} (Set.{u1} β) t t₁)))
Case conversion may be inaccurate. Consider using '#align set.prod_eq_prod_iff_of_nonempty Set.prod_eq_prod_iff_of_nonemptyₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← HEq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2, ← fst_image_prod s₁ h₁.2, HEq, eq_self_iff_true, true_and_iff, ←
      snd_image_prod h.1 t, ← snd_image_prod h₁.1 t₁, HEq]
  · rintro ⟨rfl, rfl⟩
    rfl
#align set.prod_eq_prod_iff_of_nonempty Set.prod_eq_prod_iff_of_nonempty

/- warning: set.prod_eq_prod_iff -> Set.prod_eq_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {s : Set.{u1} α} {s₁ : Set.{u1} α} {t : Set.{u2} β} {t₁ : Set.{u2} β}, Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (Prod.{u1, u2} α β)) (Set.prod.{u1, u2} α β s t) (Set.prod.{u1, u2} α β s₁ t₁)) (Or (And (Eq.{succ u1} (Set.{u1} α) s s₁) (Eq.{succ u2} (Set.{u2} β) t t₁)) (And (Or (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β)))) (Or (Eq.{succ u1} (Set.{u1} α) s₁ (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u2} (Set.{u2} β) t₁ (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {s : Set.{u2} α} {s₁ : Set.{u2} α} {t : Set.{u1} β} {t₁ : Set.{u1} β}, Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u1 u2} (Prod.{u2, u1} α β)) (Set.prod.{u2, u1} α β s t) (Set.prod.{u2, u1} α β s₁ t₁)) (Or (And (Eq.{succ u2} (Set.{u2} α) s s₁) (Eq.{succ u1} (Set.{u1} β) t t₁)) (And (Or (Eq.{succ u2} (Set.{u2} α) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{succ u1} (Set.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β)))) (Or (Eq.{succ u2} (Set.{u2} α) s₁ (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Eq.{succ u1} (Set.{u1} β) t₁ (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))))))
Case conversion may be inaccurate. Consider using '#align set.prod_eq_prod_iff Set.prod_eq_prod_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem prod_eq_prod_iff :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) :=
  by
  symm
  cases' eq_empty_or_nonempty (s ×ˢ t) with h h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and_iff,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty, Ne.def, prod_eq_empty_iff] at h
  simp_rw [h, false_and_iff, or_false_iff]
#align set.prod_eq_prod_iff Set.prod_eq_prod_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.prod_eq_iff_eq /-
@[simp]
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ :=
  by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, eq_self_iff_true, and_true_iff, or_iff_left_iff_imp,
    or_false_iff]
  rintro ⟨rfl, rfl⟩
  rfl
#align set.prod_eq_iff_eq Set.prod_eq_iff_eq
-/

section Mono

variable [Preorder α] {f : α → Set β} {g : α → Set γ}

/- warning: monotone.set_prod -> Monotone.set_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u3} γ)}, (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) f) -> (Monotone.{u1, u3} α (Set.{u3} γ) _inst_1 (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (SemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (Lattice.toSemilatticeInf.{u3} (Set.{u3} γ) (GeneralizedCoheytingAlgebra.toLattice.{u3} (Set.{u3} γ) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))))))) g) -> (Monotone.{u1, max u2 u3} α (Set.{max u2 u3} (Prod.{u2, u3} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Lattice.toSemilatticeInf.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.booleanAlgebra.{max u2 u3} (Prod.{u2, u3} β γ)))))))) (fun (x : α) => Set.prod.{u2, u3} β γ (f x) (g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u1} γ)}, (Monotone.{u3, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)))))))) f) -> (Monotone.{u3, u1} α (Set.{u1} γ) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (Lattice.toSemilatticeInf.{u1} (Set.{u1} γ) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} γ) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} γ) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} γ) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} γ) (Set.instBooleanAlgebraSet.{u1} γ)))))))) g) -> (Monotone.{u3, max u1 u2} α (Set.{max u1 u2} (Prod.{u2, u1} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Lattice.toSemilatticeInf.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BiheytingAlgebra.toCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BooleanAlgebra.toBiheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Set.instBooleanAlgebraSet.{max u2 u1} (Prod.{u2, u1} β γ))))))))) (fun (x : α) => Set.prod.{u2, u1} β γ (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.set_prod Monotone.set_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Monotone.set_prod (hf : Monotone f) (hg : Monotone g) : Monotone fun x => f x ×ˢ g x :=
  fun a b h => prod_mono (hf h) (hg h)
#align monotone.set_prod Monotone.set_prod

/- warning: antitone.set_prod -> Antitone.set_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u3} γ)}, (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) f) -> (Antitone.{u1, u3} α (Set.{u3} γ) _inst_1 (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (SemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (Lattice.toSemilatticeInf.{u3} (Set.{u3} γ) (GeneralizedCoheytingAlgebra.toLattice.{u3} (Set.{u3} γ) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))))))) g) -> (Antitone.{u1, max u2 u3} α (Set.{max u2 u3} (Prod.{u2, u3} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Lattice.toSemilatticeInf.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.booleanAlgebra.{max u2 u3} (Prod.{u2, u3} β γ)))))))) (fun (x : α) => Set.prod.{u2, u3} β γ (f x) (g x)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : Preorder.{u3} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u1} γ)}, (Antitone.{u3, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)))))))) f) -> (Antitone.{u3, u1} α (Set.{u1} γ) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (Lattice.toSemilatticeInf.{u1} (Set.{u1} γ) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} γ) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} γ) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} γ) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} γ) (Set.instBooleanAlgebraSet.{u1} γ)))))))) g) -> (Antitone.{u3, max u1 u2} α (Set.{max u1 u2} (Prod.{u2, u1} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Lattice.toSemilatticeInf.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BiheytingAlgebra.toCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BooleanAlgebra.toBiheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Set.instBooleanAlgebraSet.{max u2 u1} (Prod.{u2, u1} β γ))))))))) (fun (x : α) => Set.prod.{u2, u1} β γ (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.set_prod Antitone.set_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem Antitone.set_prod (hf : Antitone f) (hg : Antitone g) : Antitone fun x => f x ×ˢ g x :=
  fun a b h => prod_mono (hf h) (hg h)
#align antitone.set_prod Antitone.set_prod

/- warning: monotone_on.set_prod -> MonotoneOn.set_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u3} γ)}, (MonotoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) f s) -> (MonotoneOn.{u1, u3} α (Set.{u3} γ) _inst_1 (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (SemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (Lattice.toSemilatticeInf.{u3} (Set.{u3} γ) (GeneralizedCoheytingAlgebra.toLattice.{u3} (Set.{u3} γ) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))))))) g s) -> (MonotoneOn.{u1, max u2 u3} α (Set.{max u2 u3} (Prod.{u2, u3} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Lattice.toSemilatticeInf.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.booleanAlgebra.{max u2 u3} (Prod.{u2, u3} β γ)))))))) (fun (x : α) => Set.prod.{u2, u3} β γ (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Set.{u3} α} [_inst_1 : Preorder.{u3} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u1} γ)}, (MonotoneOn.{u3, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)))))))) f s) -> (MonotoneOn.{u3, u1} α (Set.{u1} γ) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (Lattice.toSemilatticeInf.{u1} (Set.{u1} γ) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} γ) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} γ) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} γ) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} γ) (Set.instBooleanAlgebraSet.{u1} γ)))))))) g s) -> (MonotoneOn.{u3, max u1 u2} α (Set.{max u1 u2} (Prod.{u2, u1} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Lattice.toSemilatticeInf.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BiheytingAlgebra.toCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BooleanAlgebra.toBiheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Set.instBooleanAlgebraSet.{max u2 u1} (Prod.{u2, u1} β γ))))))))) (fun (x : α) => Set.prod.{u2, u1} β γ (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.set_prod MonotoneOn.set_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem MonotoneOn.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x ×ˢ g x) s := fun a ha b hb h => prod_mono (hf ha hb h) (hg ha hb h)
#align monotone_on.set_prod MonotoneOn.set_prod

/- warning: antitone_on.set_prod -> AntitoneOn.set_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {s : Set.{u1} α} [_inst_1 : Preorder.{u1} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u3} γ)}, (AntitoneOn.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) f s) -> (AntitoneOn.{u1, u3} α (Set.{u3} γ) _inst_1 (PartialOrder.toPreorder.{u3} (Set.{u3} γ) (SemilatticeInf.toPartialOrder.{u3} (Set.{u3} γ) (Lattice.toSemilatticeInf.{u3} (Set.{u3} γ) (GeneralizedCoheytingAlgebra.toLattice.{u3} (Set.{u3} γ) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u3} (Set.{u3} γ) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ))))))) g s) -> (AntitoneOn.{u1, max u2 u3} α (Set.{max u2 u3} (Prod.{u2, u3} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Lattice.toSemilatticeInf.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u2 u3} (Set.{max u2 u3} (Prod.{u2, u3} β γ)) (Set.booleanAlgebra.{max u2 u3} (Prod.{u2, u3} β γ)))))))) (fun (x : α) => Set.prod.{u2, u3} β γ (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} {s : Set.{u3} α} [_inst_1 : Preorder.{u3} α] {f : α -> (Set.{u2} β)} {g : α -> (Set.{u1} γ)}, (AntitoneOn.{u3, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} β) (Set.instBooleanAlgebraSet.{u2} β)))))))) f s) -> (AntitoneOn.{u3, u1} α (Set.{u1} γ) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} γ) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} γ) (Lattice.toSemilatticeInf.{u1} (Set.{u1} γ) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} γ) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} γ) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} γ) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} γ) (Set.instBooleanAlgebraSet.{u1} γ)))))))) g s) -> (AntitoneOn.{u3, max u1 u2} α (Set.{max u1 u2} (Prod.{u2, u1} β γ)) _inst_1 (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (SemilatticeInf.toPartialOrder.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Lattice.toSemilatticeInf.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (GeneralizedCoheytingAlgebra.toLattice.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BiheytingAlgebra.toCoheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (BooleanAlgebra.toBiheytingAlgebra.{max u2 u1} (Set.{max u1 u2} (Prod.{u2, u1} β γ)) (Set.instBooleanAlgebraSet.{max u2 u1} (Prod.{u2, u1} β γ))))))))) (fun (x : α) => Set.prod.{u2, u1} β γ (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.set_prod AntitoneOn.set_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem AntitoneOn.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x ×ˢ g x) s := fun a ha b hb h => prod_mono (hf ha hb h) (hg ha hb h)
#align antitone_on.set_prod AntitoneOn.set_prod

end Mono

end Prod

/-! ### Diagonal

In this section we prove some lemmas about the diagonal set `{p | p.1 = p.2}` and the diagonal map
`λ x, (x, x)`.
-/


section Diagonal

variable {α : Type _} {s t : Set α}

#print Set.diagonal /-
/-- `diagonal α` is the set of `α × α` consisting of all pairs of the form `(a, a)`. -/
def diagonal (α : Type _) : Set (α × α) :=
  { p | p.1 = p.2 }
#align set.diagonal Set.diagonal
-/

#print Set.mem_diagonal /-
theorem mem_diagonal (x : α) : (x, x) ∈ diagonal α := by simp [diagonal]
#align set.mem_diagonal Set.mem_diagonal
-/

#print Set.mem_diagonal_iff /-
@[simp]
theorem mem_diagonal_iff {x : α × α} : x ∈ diagonal α ↔ x.1 = x.2 :=
  Iff.rfl
#align set.mem_diagonal_iff Set.mem_diagonal_iff
-/

#print Set.decidableMemDiagonal /-
instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x ∈ diagonal α) :=
  h x.1 x.2
#align set.decidable_mem_diagonal Set.decidableMemDiagonal
-/

#print Set.preimage_coe_coe_diagonal /-
theorem preimage_coe_coe_diagonal (s : Set α) : Prod.map coe coe ⁻¹' diagonal α = diagonal s :=
  by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]
#align set.preimage_coe_coe_diagonal Set.preimage_coe_coe_diagonal
-/

#print Set.range_diag /-
@[simp]
theorem range_diag : (range fun x => (x, x)) = diagonal α :=
  by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]
#align set.range_diag Set.range_diag
-/

/- warning: set.prod_subset_compl_diagonal_iff_disjoint -> Set.prod_subset_compl_diagonal_iff_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasSubset.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s t) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α))) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instHasSubsetSet_1.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s t) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α))) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t)
Case conversion may be inaccurate. Consider using '#align set.prod_subset_compl_diagonal_iff_disjoint Set.prod_subset_compl_diagonal_iff_disjointₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t ⊆ diagonal αᶜ ↔ Disjoint s t :=
  subset_compl_comm.trans <| by
    simp_rw [← range_diag, range_subset_iff, disjoint_left, mem_compl_iff, prod_mk_mem_set_prod_eq,
      not_and]
#align set.prod_subset_compl_diagonal_iff_disjoint Set.prod_subset_compl_diagonal_iff_disjoint

/- warning: set.diag_preimage_prod -> Set.diag_preimage_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α (Prod.{u1, u1} α α) (fun (x : α) => Prod.mk.{u1, u1} α α x x) (Set.prod.{u1, u1} α α s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u1} α (Prod.{u1, u1} α α) (fun (x : α) => Prod.mk.{u1, u1} α α x x) (Set.prod.{u1, u1} α α s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet_1.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diag_preimage_prod Set.diag_preimage_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem diag_preimage_prod (s t : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ t = s ∩ t :=
  rfl
#align set.diag_preimage_prod Set.diag_preimage_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.diag_preimage_prod_self /-
theorem diag_preimage_prod_self (s : Set α) : (fun x => (x, x)) ⁻¹' s ×ˢ s = s :=
  inter_self s
#align set.diag_preimage_prod_self Set.diag_preimage_prod_self
-/

end Diagonal

section OffDiag

variable {α : Type _} {s t : Set α} {x : α × α} {a : α}

#print Set.offDiag /-
/-- The off-diagonal of a set `s` is the set of pairs `(a, b)` with `a, b ∈ s` and `a ≠ b`. -/
def offDiag (s : Set α) : Set (α × α) :=
  { x | x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 }
#align set.off_diag Set.offDiag
-/

#print Set.mem_offDiag /-
@[simp]
theorem mem_offDiag : x ∈ s.offDiag ↔ x.1 ∈ s ∧ x.2 ∈ s ∧ x.1 ≠ x.2 :=
  Iff.rfl
#align set.mem_off_diag Set.mem_offDiag
-/

/- warning: set.off_diag_mono -> Set.offDiag_mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α)))))))) (Set.offDiag.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α))))))))) (Set.offDiag.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.off_diag_mono Set.offDiag_monoₓ'. -/
theorem offDiag_mono : Monotone (offDiag : Set α → Set (α × α)) := fun s t h x =>
  And.imp (@h _) <| And.imp_left <| @h _
#align set.off_diag_mono Set.offDiag_mono

#print Set.offDiag_nonempty /-
@[simp]
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [off_diag, Set.Nonempty, Set.Nontrivial]
#align set.off_diag_nonempty Set.offDiag_nonempty
-/

#print Set.offDiag_eq_empty /-
@[simp]
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty, ← not_nontrivial_iff, off_diag_nonempty.not]
#align set.off_diag_eq_empty Set.offDiag_eq_empty
-/

alias off_diag_nonempty ↔ _ nontrivial.off_diag_nonempty

alias off_diag_nonempty ↔ _ subsingleton.off_diag_eq_empty

variable (s t)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.offDiag_subset_prod /-
theorem offDiag_subset_prod : s.offDiag ⊆ s ×ˢ s := fun x hx => ⟨hx.1, hx.2.1⟩
#align set.off_diag_subset_prod Set.offDiag_subset_prod
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.offDiag_eq_sep_prod /-
theorem offDiag_eq_sep_prod : s.offDiag = { x ∈ s ×ˢ s | x.1 ≠ x.2 } :=
  ext fun _ => and_assoc.symm
#align set.off_diag_eq_sep_prod Set.offDiag_eq_sep_prod
-/

#print Set.offDiag_empty /-
@[simp]
theorem offDiag_empty : (∅ : Set α).offDiag = ∅ := by simp
#align set.off_diag_empty Set.offDiag_empty
-/

#print Set.offDiag_singleton /-
@[simp]
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp
#align set.off_diag_singleton Set.offDiag_singleton
-/

/- warning: set.off_diag_univ -> Set.offDiag_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Set.univ.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Set.univ.{u1} α)) (HasCompl.compl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α))) (Set.diagonal.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.off_diag_univ Set.offDiag_univₓ'. -/
@[simp]
theorem offDiag_univ : (univ : Set α).offDiag = diagonal αᶜ :=
  ext <| by simp
#align set.off_diag_univ Set.offDiag_univ

/- warning: set.prod_sdiff_diagonal -> Set.prod_sdiff_diagonal is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α))) (Set.prod.{u1, u1} α α s s) (Set.diagonal.{u1} α)) (Set.offDiag.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (SDiff.sdiff.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instSDiffSet.{u1} (Prod.{u1, u1} α α)) (Set.prod.{u1, u1} α α s s) (Set.diagonal.{u1} α)) (Set.offDiag.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.prod_sdiff_diagonal Set.prod_sdiff_diagonalₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp]
theorem prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag :=
  ext fun _ => and_assoc
#align set.prod_sdiff_diagonal Set.prod_sdiff_diagonal

/- warning: set.disjoint_diagonal_off_diag -> Set.disjoint_diagonal_offDiag is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.booleanAlgebra.{u1} (Prod.{u1, u1} α α)))) (Set.diagonal.{u1} α) (Set.offDiag.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Preorder.toLE.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (PartialOrder.toPreorder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instBooleanAlgebraSet.{u1} (Prod.{u1, u1} α α)))) (Set.diagonal.{u1} α) (Set.offDiag.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.disjoint_diagonal_off_diag Set.disjoint_diagonal_offDiagₓ'. -/
@[simp]
theorem disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag :=
  disjoint_left.mpr fun x hd ho => ho.2.2 hd
#align set.disjoint_diagonal_off_diag Set.disjoint_diagonal_offDiag

/- warning: set.off_diag_inter -> Set.offDiag_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasInter.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.offDiag.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet_1.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instInterSet_1.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.offDiag.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.off_diag_inter Set.offDiag_interₓ'. -/
theorem offDiag_inter : (s ∩ t).offDiag = s.offDiag ∩ t.offDiag :=
  ext fun x => by
    simp only [mem_off_diag, mem_inter_iff]
    tauto
#align set.off_diag_inter Set.offDiag_inter

variable {s t}

/- warning: set.off_diag_union -> Set.offDiag_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasUnion.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasUnion.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasUnion.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.offDiag.{u1} α t)) (Set.prod.{u1, u1} α α s t)) (Set.prod.{u1, u1} α α t s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet_1.{u1} α) s t)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instUnionSet_1.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instUnionSet_1.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instUnionSet_1.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.offDiag.{u1} α t)) (Set.prod.{u1, u1} α α s t)) (Set.prod.{u1, u1} α α t s)))
Case conversion may be inaccurate. Consider using '#align set.off_diag_union Set.offDiag_unionₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem offDiag_union (h : Disjoint s t) :
    (s ∪ t).offDiag = s.offDiag ∪ t.offDiag ∪ s ×ˢ t ∪ t ×ˢ s :=
  by
  rw [off_diag_eq_sep_prod, union_prod, prod_union, prod_union, union_comm _ (t ×ˢ t), union_assoc,
    union_left_comm (s ×ˢ t), ← union_assoc, sep_union, sep_union, ← off_diag_eq_sep_prod, ←
    off_diag_eq_sep_prod, sep_eq_self_iff_mem_true.2, ← union_assoc]
  simp only [mem_union, mem_prod, Ne.def, Prod.forall]
  rintro i j (⟨hi, hj⟩ | ⟨hi, hj⟩) rfl <;> exact h.le_bot ⟨‹_›, ‹_›⟩
#align set.off_diag_union Set.offDiag_union

/- warning: set.off_diag_insert -> Set.offDiag_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasUnion.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.hasUnion.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.prod.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s)) (Set.prod.{u1, u1} α α s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instUnionSet_1.{u1} (Prod.{u1, u1} α α)) (Union.union.{u1} (Set.{u1} (Prod.{u1, u1} α α)) (Set.instUnionSet_1.{u1} (Prod.{u1, u1} α α)) (Set.offDiag.{u1} α s) (Set.prod.{u1, u1} α α (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s)) (Set.prod.{u1, u1} α α s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))))
Case conversion may be inaccurate. Consider using '#align set.off_diag_insert Set.offDiag_insertₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag ∪ {a} ×ˢ s ∪ s ×ˢ {a} :=
  by
  rw [insert_eq, union_comm, off_diag_union, off_diag_singleton, union_empty, union_right_comm]
  rw [disjoint_left]
  rintro b hb (rfl : b = a)
  exact ha hb
#align set.off_diag_insert Set.offDiag_insert

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type _} {α β : ι → Type _} {s s₁ s₂ : Set ι} {t t₁ t₂ : ∀ i, Set (α i)} {i : ι}

#print Set.pi /-
/-- Given an index set `ι` and a family of sets `t : Π i, set (α i)`, `pi s t`
is the set of dependent functions `f : Πa, π a` such that `f a` belongs to `t a`
whenever `a ∈ s`. -/
def pi (s : Set ι) (t : ∀ i, Set (α i)) : Set (∀ i, α i) :=
  { f | ∀ i ∈ s, f i ∈ t i }
#align set.pi Set.pi
-/

/- warning: set.mem_pi -> Set.mem_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {f : forall (i : ι), α i}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) f (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) (f i) (t i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {f : forall (i : ι), α i}, Iff (Membership.mem.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) f (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) (f i) (t i)))
Case conversion may be inaccurate. Consider using '#align set.mem_pi Set.mem_piₓ'. -/
@[simp]
theorem mem_pi {f : ∀ i, α i} : f ∈ s.pi t ↔ ∀ i ∈ s, f i ∈ t i :=
  Iff.rfl
#align set.mem_pi Set.mem_pi

/- warning: set.mem_univ_pi -> Set.mem_univ_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} {f : forall (i : ι), α i}, Iff (Membership.Mem.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasMem.{max u1 u2} (forall (i : ι), α i)) f (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t)) (forall (i : ι), Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) (f i) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} {f : forall (i : ι), α i}, Iff (Membership.mem.{max u2 u1, max u1 u2} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instMembershipSet.{max u2 u1} (forall (i : ι), α i)) f (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t)) (forall (i : ι), Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) (f i) (t i))
Case conversion may be inaccurate. Consider using '#align set.mem_univ_pi Set.mem_univ_piₓ'. -/
@[simp]
theorem mem_univ_pi {f : ∀ i, α i} : f ∈ pi univ t ↔ ∀ i, f i ∈ t i := by simp
#align set.mem_univ_pi Set.mem_univ_pi

#print Set.empty_pi /-
@[simp]
theorem empty_pi (s : ∀ i, Set (α i)) : pi ∅ s = univ :=
  by
  ext
  simp [pi]
#align set.empty_pi Set.empty_pi
-/

/- warning: set.pi_univ -> Set.pi_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.univ.{u2} (α i))) (Set.univ.{max u1 u2} (forall (i : ι), α i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.univ.{u1} (α i))) (Set.univ.{max u2 u1} (forall (i : ι), α i))
Case conversion may be inaccurate. Consider using '#align set.pi_univ Set.pi_univₓ'. -/
@[simp]
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun f i hi => mem_univ _
#align set.pi_univ Set.pi_univ

/- warning: set.pi_mono -> Set.pi_mono is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (HasSubset.Subset.{u2} (Set.{u2} (α i)) (Set.hasSubset.{u2} (α i)) (t₁ i) (t₂ i))) -> (HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t₁) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (HasSubset.Subset.{u1} (Set.{u1} (α i)) (Set.instHasSubsetSet_1.{u1} (α i)) (t₁ i) (t₂ i))) -> (HasSubset.Subset.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t₁) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t₂))
Case conversion may be inaccurate. Consider using '#align set.pi_mono Set.pi_monoₓ'. -/
theorem pi_mono (h : ∀ i ∈ s, t₁ i ⊆ t₂ i) : pi s t₁ ⊆ pi s t₂ := fun x hx i hi => h i hi <| hx i hi
#align set.pi_mono Set.pi_mono

/- warning: set.pi_inter_distrib -> Set.pi_inter_distrib is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {t₁ : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Inter.inter.{u2} (Set.{u2} (α i)) (Set.hasInter.{u2} (α i)) (t i) (t₁ i))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t₁))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {t₁ : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Inter.inter.{u1} (Set.{u1} (α i)) (Set.instInterSet_1.{u1} (α i)) (t i) (t₁ i))) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t₁))
Case conversion may be inaccurate. Consider using '#align set.pi_inter_distrib Set.pi_inter_distribₓ'. -/
theorem pi_inter_distrib : (s.pi fun i => t i ∩ t₁ i) = s.pi t ∩ s.pi t₁ :=
  ext fun x => by simp only [forall_and, mem_pi, mem_inter_iff]
#align set.pi_inter_distrib Set.pi_inter_distrib

/- warning: set.pi_congr -> Set.pi_congr is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, (Eq.{succ u1} (Set.{u1} ι) s₁ s₂) -> (forall (i : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s₁) -> (Eq.{succ u2} (Set.{u2} (α i)) (t₁ i) (t₂ i))) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s₁ t₁) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s₂ t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t₁ : forall (i : ι), Set.{u1} (α i)} {t₂ : forall (i : ι), Set.{u1} (α i)}, (Eq.{succ u2} (Set.{u2} ι) s₁ s₂) -> (forall (i : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s₁) -> (Eq.{succ u1} (Set.{u1} (α i)) (t₁ i) (t₂ i))) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s₁ t₁) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.pi_congr Set.pi_congrₓ'. -/
theorem pi_congr (h : s₁ = s₂) (h' : ∀ i ∈ s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ :=
  h ▸ ext fun x => forall₂_congr fun i hi => h' i hi ▸ Iff.rfl
#align set.pi_congr Set.pi_congr

/- warning: set.pi_eq_empty -> Set.pi_eq_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Eq.{succ u2} (Set.{u2} (α i)) (t i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))) -> (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasEmptyc.{max u1 u2} (forall (i : ι), α i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Eq.{succ u1} (Set.{u1} (α i)) (t i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))) -> (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instEmptyCollectionSet.{max u2 u1} (forall (i : ι), α i))))
Case conversion may be inaccurate. Consider using '#align set.pi_eq_empty Set.pi_eq_emptyₓ'. -/
theorem pi_eq_empty (hs : i ∈ s) (ht : t i = ∅) : s.pi t = ∅ :=
  by
  ext f
  simp only [mem_empty_iff_false, not_forall, iff_false_iff, mem_pi, not_imp]
  exact ⟨i, hs, by simp [ht]⟩
#align set.pi_eq_empty Set.pi_eq_empty

#print Set.univ_pi_eq_empty /-
theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht
#align set.univ_pi_eq_empty Set.univ_pi_eq_empty
-/

/- warning: set.pi_nonempty_iff -> Set.pi_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) (forall (i : ι), Exists.{succ u2} (α i) (fun (x : α i) => (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Membership.Mem.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasMem.{u2} (α i)) x (t i))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) (forall (i : ι), Exists.{succ u1} (α i) (fun (x : α i) => (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Membership.mem.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instMembershipSet.{u1} (α i)) x (t i))))
Case conversion may be inaccurate. Consider using '#align set.pi_nonempty_iff Set.pi_nonempty_iffₓ'. -/
theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ ∀ i, ∃ x, i ∈ s → x ∈ t i := by
  simp [Classical.skolem, Set.Nonempty]
#align set.pi_nonempty_iff Set.pi_nonempty_iff

/- warning: set.univ_pi_nonempty_iff -> Set.univ_pi_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t)) (forall (i : ι), Set.Nonempty.{u2} (α i) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t)) (forall (i : ι), Set.Nonempty.{u1} (α i) (t i))
Case conversion may be inaccurate. Consider using '#align set.univ_pi_nonempty_iff Set.univ_pi_nonempty_iffₓ'. -/
theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ ∀ i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]
#align set.univ_pi_nonempty_iff Set.univ_pi_nonempty_iff

/- warning: set.pi_eq_empty_iff -> Set.pi_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasEmptyc.{max u1 u2} (forall (i : ι), α i)))) (Exists.{succ u1} ι (fun (i : ι) => Or (IsEmpty.{succ u2} (α i)) (And (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (Eq.{succ u2} (Set.{u2} (α i)) (t i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instEmptyCollectionSet.{max u2 u1} (forall (i : ι), α i)))) (Exists.{succ u2} ι (fun (i : ι) => Or (IsEmpty.{succ u1} (α i)) (And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Eq.{succ u1} (Set.{u1} (α i)) (t i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))))))
Case conversion may be inaccurate. Consider using '#align set.pi_eq_empty_iff Set.pi_eq_empty_iffₓ'. -/
theorem pi_eq_empty_iff : s.pi t = ∅ ↔ ∃ i, IsEmpty (α i) ∨ i ∈ s ∧ t i = ∅ :=
  by
  rw [← not_nonempty_iff_eq_empty, pi_nonempty_iff]
  push_neg
  refine' exists_congr fun i => _
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_not_mem]
#align set.pi_eq_empty_iff Set.pi_eq_empty_iff

/- warning: set.univ_pi_eq_empty_iff -> Set.univ_pi_eq_empty_iff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)}, Iff (Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasEmptyc.{max u1 u2} (forall (i : ι), α i)))) (Exists.{succ u1} ι (fun (i : ι) => Eq.{succ u2} (Set.{u2} (α i)) (t i) (EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)}, Iff (Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instEmptyCollectionSet.{max u2 u1} (forall (i : ι), α i)))) (Exists.{succ u2} ι (fun (i : ι) => Eq.{succ u1} (Set.{u1} (α i)) (t i) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))))
Case conversion may be inaccurate. Consider using '#align set.univ_pi_eq_empty_iff Set.univ_pi_eq_empty_iffₓ'. -/
@[simp]
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ ∃ i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]
#align set.univ_pi_eq_empty_iff Set.univ_pi_eq_empty_iff

/- warning: set.univ_pi_empty -> Set.univ_pi_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [h : Nonempty.{succ u1} ι], Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => EmptyCollection.emptyCollection.{u2} (Set.{u2} (α i)) (Set.hasEmptyc.{u2} (α i)))) (EmptyCollection.emptyCollection.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasEmptyc.{max u1 u2} (forall (i : ι), α i)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [h : Nonempty.{succ u2} ι], Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => EmptyCollection.emptyCollection.{u1} (Set.{u1} (α i)) (Set.instEmptyCollectionSet.{u1} (α i)))) (EmptyCollection.emptyCollection.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instEmptyCollectionSet.{max u2 u1} (forall (i : ι), α i)))
Case conversion may be inaccurate. Consider using '#align set.univ_pi_empty Set.univ_pi_emptyₓ'. -/
@[simp]
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun i => ∅ : ∀ i, Set (α i)) = ∅ :=
  univ_pi_eq_empty_iff.2 <| h.elim fun x => ⟨x, rfl⟩
#align set.univ_pi_empty Set.univ_pi_empty

/- warning: set.disjoint_univ_pi -> Set.disjoint_univ_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, Iff (Disjoint.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i))))))) (GeneralizedBooleanAlgebra.toOrderBot.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.booleanAlgebra.{max u1 u2} (forall (i : ι), α i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t₁) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t₂)) (Exists.{succ u1} ι (fun (i : ι) => Disjoint.{u2} (Set.{u2} (α i)) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} (α i)) (Lattice.toSemilatticeInf.{u2} (Set.{u2} (α i)) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} (α i)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} (α i)) (Set.booleanAlgebra.{u2} (α i))))))) (GeneralizedBooleanAlgebra.toOrderBot.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} (α i)) (Set.booleanAlgebra.{u2} (α i)))) (t₁ i) (t₂ i)))
but is expected to have type
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t₁ : forall (i : ι), Set.{u2} (α i)} {t₂ : forall (i : ι), Set.{u2} (α i)}, Iff (Disjoint.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BiheytingAlgebra.toCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toBiheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i)))))))) (BoundedOrder.toOrderBot.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Preorder.toLE.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (PartialOrder.toPreorder.{max u2 u1} (Set.{max u1 u2} (forall (i : ι), α i)) (SemilatticeInf.toPartialOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Lattice.toSemilatticeInf.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (GeneralizedCoheytingAlgebra.toLattice.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BiheytingAlgebra.toCoheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (BooleanAlgebra.toBiheytingAlgebra.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i)))))))))) (BooleanAlgebra.toBoundedOrder.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.instBooleanAlgebraSet.{max u1 u2} (forall (i : ι), α i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t₁) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t₂)) (Exists.{succ u1} ι (fun (i : ι) => Disjoint.{u2} (Set.{u2} (α i)) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} (α i)) (Lattice.toSemilatticeInf.{u2} (Set.{u2} (α i)) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} (α i)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} (α i)) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} (α i)) (Set.instBooleanAlgebraSet.{u2} (α i)))))))) (BoundedOrder.toOrderBot.{u2} (Set.{u2} (α i)) (Preorder.toLE.{u2} (Set.{u2} (α i)) (PartialOrder.toPreorder.{u2} (Set.{u2} (α i)) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} (α i)) (Lattice.toSemilatticeInf.{u2} (Set.{u2} (α i)) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} (α i)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} (α i)) (BiheytingAlgebra.toCoheytingAlgebra.{u2} (Set.{u2} (α i)) (BooleanAlgebra.toBiheytingAlgebra.{u2} (Set.{u2} (α i)) (Set.instBooleanAlgebraSet.{u2} (α i)))))))))) (BooleanAlgebra.toBoundedOrder.{u2} (Set.{u2} (α i)) (Set.instBooleanAlgebraSet.{u2} (α i)))) (t₁ i) (t₂ i)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_univ_pi Set.disjoint_univ_piₓ'. -/
@[simp]
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ ∃ i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]
#align set.disjoint_univ_pi Set.disjoint_univ_pi

/- warning: set.range_dcomp -> Set.range_dcomp is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} (f : forall (i : ι), (α i) -> (β i)), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.range.{max u1 u3, max (succ u1) (succ u2)} (forall (i : ι), β i) (forall (i : ι), α i) (fun (g : forall (i : ι), α i) (i : ι) => f i (g i))) (Set.pi.{u1, u3} ι (fun (i : ι) => β i) (Set.univ.{u1} ι) (fun (i : ι) => Set.range.{u3, succ u2} (β i) (α i) (f i)))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} (f : forall (i : ι), (α i) -> (β i)), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (forall (i : ι), β i)) (Set.range.{max u3 u2, max (succ u3) (succ u1)} (forall (i : ι), β i) (forall (i : ι), α i) (fun (g : forall (i : ι), α i) (i : ι) => f i (g i))) (Set.pi.{u3, u2} ι (fun (i : ι) => β i) (Set.univ.{u3} ι) (fun (i : ι) => Set.range.{u2, succ u1} (β i) (α i) (f i)))
Case conversion may be inaccurate. Consider using '#align set.range_dcomp Set.range_dcompₓ'. -/
@[simp]
theorem range_dcomp (f : ∀ i, α i → β i) :
    (range fun g : ∀ i, α i => fun i => f i (g i)) = pi univ fun i => range (f i) :=
  by
  apply subset.antisymm _ fun x hx => _
  · rintro _ ⟨x, rfl⟩ i -
    exact ⟨x i, rfl⟩
  · choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩
#align set.range_dcomp Set.range_dcomp

/- warning: set.insert_pi -> Set.insert_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (i : ι) (s : Set.{u1} ι) (t : forall (i : ι), Set.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Insert.insert.{u1, u1} ι (Set.{u1} ι) (Set.hasInsert.{u1} ι) i s) t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.preimage.{max u1 u2, u2} (forall (i : ι), α i) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) (t i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (i : ι) (s : Set.{u2} ι) (t : forall (i : ι), Set.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Insert.insert.{u2, u2} ι (Set.{u2} ι) (Set.instInsertSet.{u2} ι) i s) t) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.preimage.{max u2 u1, u1} (forall (i : ι), α i) (α i) (Function.eval.{succ u2, succ u1} ι α i) (t i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t))
Case conversion may be inaccurate. Consider using '#align set.insert_pi Set.insert_piₓ'. -/
@[simp]
theorem insert_pi (i : ι) (s : Set ι) (t : ∀ i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i ∩ pi s t :=
  by
  ext
  simp [pi, or_imp, forall_and]
#align set.insert_pi Set.insert_pi

#print Set.singleton_pi /-
@[simp]
theorem singleton_pi (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = eval i ⁻¹' t i :=
  by
  ext
  simp [pi]
#align set.singleton_pi Set.singleton_pi
-/

#print Set.singleton_pi' /-
theorem singleton_pi' (i : ι) (t : ∀ i, Set (α i)) : pi {i} t = { x | x i ∈ t i } :=
  singleton_pi i t
#align set.singleton_pi' Set.singleton_pi'
-/

/- warning: set.univ_pi_singleton -> Set.univ_pi_singleton is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (f : forall (i : ι), α i), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => Singleton.singleton.{u2, u2} (α i) (Set.{u2} (α i)) (Set.hasSingleton.{u2} (α i)) (f i))) (Singleton.singleton.{max u1 u2, max u1 u2} (forall (i : ι), α i) (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSingleton.{max u1 u2} (forall (i : ι), α i)) f)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (f : forall (i : ι), α i), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => Singleton.singleton.{u1, u1} (α i) (Set.{u1} (α i)) (Set.instSingletonSet.{u1} (α i)) (f i))) (Singleton.singleton.{max u2 u1, max u2 u1} (forall (i : ι), α i) (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instSingletonSet.{max u2 u1} (forall (i : ι), α i)) f)
Case conversion may be inaccurate. Consider using '#align set.univ_pi_singleton Set.univ_pi_singletonₓ'. -/
theorem univ_pi_singleton (f : ∀ i, α i) : (pi univ fun i => {f i}) = ({f} : Set (∀ i, α i)) :=
  ext fun g => by simp [funext_iff]
#align set.univ_pi_singleton Set.univ_pi_singleton

/- warning: set.preimage_pi -> Set.preimage_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} (s : Set.{u1} ι) (t : forall (i : ι), Set.{u3} (β i)) (f : forall (i : ι), (α i) -> (β i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.preimage.{max u1 u2, max u1 u3} (forall (i : ι), α i) (forall (i : ι), β i) (fun (g : forall (i : ι), α i) (i : ι) => f i (g i)) (Set.pi.{u1, u3} ι (fun (i : ι) => β i) s t)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.preimage.{u2, u3} (α i) (β i) (f i) (t i)))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} (s : Set.{u3} ι) (t : forall (i : ι), Set.{u2} (β i)) (f : forall (i : ι), (α i) -> (β i)), Eq.{max (succ u3) (succ u1)} (Set.{max u3 u1} (forall (i : ι), α i)) (Set.preimage.{max u3 u1, max u3 u2} (forall (i : ι), α i) (forall (i : ι), β i) (fun (g : forall (i : ι), α i) (i : ι) => f i (g i)) (Set.pi.{u3, u2} ι (fun (i : ι) => β i) s t)) (Set.pi.{u3, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.preimage.{u1, u2} (α i) (β i) (f i) (t i)))
Case conversion may be inaccurate. Consider using '#align set.preimage_pi Set.preimage_piₓ'. -/
theorem preimage_pi (s : Set ι) (t : ∀ i, Set (β i)) (f : ∀ i, α i → β i) :
    (fun (g : ∀ i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl
#align set.preimage_pi Set.preimage_pi

/- warning: set.pi_if -> Set.pi_if is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {p : ι -> Prop} [h : DecidablePred.{succ u1} ι p] (s : Set.{u1} ι) (t₁ : forall (i : ι), Set.{u2} (α i)) (t₂ : forall (i : ι), Set.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => ite.{succ u2} (Set.{u2} (α i)) (p i) (h i) (t₁ i) (t₂ i))) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Sep.sep.{u1, u1} ι (Set.{u1} ι) (Set.hasSep.{u1} ι) (fun (i : ι) => p i) s) t₁) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Sep.sep.{u1, u1} ι (Set.{u1} ι) (Set.hasSep.{u1} ι) (fun (i : ι) => Not (p i)) s) t₂))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {p : ι -> Prop} [h : DecidablePred.{succ u2} ι p] (s : Set.{u2} ι) (t₁ : forall (i : ι), Set.{u1} (α i)) (t₂ : forall (i : ι), Set.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => ite.{succ u1} (Set.{u1} (α i)) (p i) (h i) (t₁ i) (t₂ i))) (Inter.inter.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (setOf.{u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (p i))) t₁) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (setOf.{u2} ι (fun (i : ι) => And (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (Not (p i)))) t₂))
Case conversion may be inaccurate. Consider using '#align set.pi_if Set.pi_ifₓ'. -/
theorem pi_if {p : ι → Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : ∀ i, Set (α i)) :
    (pi s fun i => if p i then t₁ i else t₂ i) =
      pi ({ i ∈ s | p i }) t₁ ∩ pi ({ i ∈ s | ¬p i }) t₂ :=
  by
  ext f
  refine' ⟨fun h => _, _⟩
  ·
    constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all
#align set.pi_if Set.pi_if

/- warning: set.union_pi -> Set.union_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s₁ : Set.{u1} ι} {s₂ : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Union.union.{u1} (Set.{u1} ι) (Set.hasUnion.{u1} ι) s₁ s₂) t) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s₁ t) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s₂ t))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s₁ : Set.{u2} ι} {s₂ : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Union.union.{u2} (Set.{u2} ι) (Set.instUnionSet_1.{u2} ι) s₁ s₂) t) (Inter.inter.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s₁ t) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_pi Set.union_piₓ'. -/
theorem union_pi : (s₁ ∪ s₂).pi t = s₁.pi t ∩ s₂.pi t := by
  simp [pi, or_imp, forall_and, set_of_and]
#align set.union_pi Set.union_pi

/- warning: set.pi_inter_compl -> Set.pi_inter_compl is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} (s : Set.{u1} ι), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Inter.inter.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasInter.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (HasCompl.compl.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι)) s) t)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} (s : Set.{u2} ι), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Inter.inter.{max u1 u2} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instInterSet_1.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (HasCompl.compl.{u2} (Set.{u2} ι) (BooleanAlgebra.toHasCompl.{u2} (Set.{u2} ι) (Set.instBooleanAlgebraSet.{u2} ι)) s) t)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t)
Case conversion may be inaccurate. Consider using '#align set.pi_inter_compl Set.pi_inter_complₓ'. -/
@[simp]
theorem pi_inter_compl (s : Set ι) : pi s t ∩ pi (sᶜ) t = pi univ t := by
  rw [← union_pi, union_compl_self]
#align set.pi_inter_compl Set.pi_inter_compl

/- warning: set.pi_update_of_not_mem -> Set.pi_update_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {s : Set.{u1} ι} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι], (Not (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s)) -> (forall (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u3} (β j))), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.pi.{u1, u3} ι (fun (j : ι) => β j) s (fun (j : ι) => t j (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Set.pi.{u1, u3} ι (fun (i : ι) => β i) s (fun (j : ι) => t j (f j))))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} {s : Set.{u3} ι} {i : ι} [_inst_1 : DecidableEq.{succ u3} ι], (Not (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s)) -> (forall (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u2} (β j))), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (forall (i : ι), β i)) (Set.pi.{u3, u2} ι (fun (j : ι) => β j) s (fun (j : ι) => t j (Function.update.{succ u3, succ u1} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Set.pi.{u3, u2} ι (fun (i : ι) => β i) s (fun (j : ι) => t j (f j))))
Case conversion may be inaccurate. Consider using '#align set.pi_update_of_not_mem Set.pi_update_of_not_memₓ'. -/
theorem pi_update_of_not_mem [DecidableEq ι] (hi : i ∉ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_noteq]
    exact fun h => hi (h ▸ hj)
#align set.pi_update_of_not_mem Set.pi_update_of_not_mem

/- warning: set.pi_update_of_mem -> Set.pi_update_of_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {β : ι -> Type.{u3}} {s : Set.{u1} ι} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι], (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (forall (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u3} (β j))), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.pi.{u1, u3} ι (fun (j : ι) => β j) s (fun (j : ι) => t j (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Inter.inter.{max u1 u3} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.hasInter.{max u1 u3} (forall (i : ι), β i)) (setOf.{max u1 u3} (forall (i : ι), β i) (fun (x : forall (i : ι), β i) => Membership.Mem.{u3, u3} (β i) (Set.{u3} (β i)) (Set.hasMem.{u3} (β i)) (x i) (t i a))) (Set.pi.{u1, u3} ι (fun (i : ι) => β i) (SDiff.sdiff.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι)) s (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι) i)) (fun (j : ι) => t j (f j)))))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} {β : ι -> Type.{u2}} {s : Set.{u3} ι} {i : ι} [_inst_1 : DecidableEq.{succ u3} ι], (Membership.mem.{u3, u3} ι (Set.{u3} ι) (Set.instMembershipSet.{u3} ι) i s) -> (forall (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u2} (β j))), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (forall (i : ι), β i)) (Set.pi.{u3, u2} ι (fun (j : ι) => β j) s (fun (j : ι) => t j (Function.update.{succ u3, succ u1} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Inter.inter.{max u3 u2} (Set.{max u3 u2} (forall (i : ι), β i)) (Set.instInterSet_1.{max u3 u2} (forall (i : ι), β i)) (setOf.{max u3 u2} (forall (i : ι), β i) (fun (x : forall (i : ι), β i) => Membership.mem.{u2, u2} (β i) (Set.{u2} (β i)) (Set.instMembershipSet.{u2} (β i)) (x i) (t i a))) (Set.pi.{u3, u2} ι (fun (i : ι) => β i) (SDiff.sdiff.{u3} (Set.{u3} ι) (Set.instSDiffSet.{u3} ι) s (Singleton.singleton.{u3, u3} ι (Set.{u3} ι) (Set.instSingletonSet.{u3} ι) i)) (fun (j : ι) => t j (f j)))))
Case conversion may be inaccurate. Consider using '#align set.pi_update_of_mem Set.pi_update_of_memₓ'. -/
theorem pi_update_of_mem [DecidableEq ι] (hi : i ∈ s) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} ∪ s \ {i}).pi fun j => t j (update f i a j) := by
      rw [union_diff_self, union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i ∈ t i a } ∩ (s \ {i}).pi fun j => t j (f j) :=
      by
      rw [union_pi, singleton_pi', update_same, pi_update_of_not_mem]
      simp
    
#align set.pi_update_of_mem Set.pi_update_of_mem

/- warning: set.univ_pi_update -> Set.univ_pi_update is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] {β : ι -> Type.{u3}} (i : ι) (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u3} (β j))), Eq.{succ (max u1 u3)} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.pi.{u1, u3} ι (fun (j : ι) => β j) (Set.univ.{u1} ι) (fun (j : ι) => t j (Function.update.{succ u1, succ u2} ι α (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Inter.inter.{max u1 u3} (Set.{max u1 u3} (forall (i : ι), β i)) (Set.hasInter.{max u1 u3} (forall (i : ι), β i)) (setOf.{max u1 u3} (forall (i : ι), β i) (fun (x : forall (i : ι), β i) => Membership.Mem.{u3, u3} (β i) (Set.{u3} (β i)) (Set.hasMem.{u3} (β i)) (x i) (t i a))) (Set.pi.{u1, u3} ι (fun (i : ι) => β i) (HasCompl.compl.{u1} (Set.{u1} ι) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} ι) (Set.booleanAlgebra.{u1} ι)) (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι) i)) (fun (j : ι) => t j (f j))))
but is expected to have type
  forall {ι : Type.{u3}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u3} ι] {β : ι -> Type.{u2}} (i : ι) (f : forall (j : ι), α j) (a : α i) (t : forall (j : ι), (α j) -> (Set.{u2} (β j))), Eq.{max (succ u3) (succ u2)} (Set.{max u3 u2} (forall (i : ι), β i)) (Set.pi.{u3, u2} ι (fun (j : ι) => β j) (Set.univ.{u3} ι) (fun (j : ι) => t j (Function.update.{succ u3, succ u1} ι (fun (a : ι) => α a) (fun (a : ι) (b : ι) => _inst_1 a b) f i a j))) (Inter.inter.{max u2 u3} (Set.{max u2 u3} (forall (i : ι), β i)) (Set.instInterSet_1.{max u3 u2} (forall (i : ι), β i)) (setOf.{max u2 u3} (forall (i : ι), β i) (fun (x : forall (i : ι), β i) => Membership.mem.{u2, u2} (β i) (Set.{u2} (β i)) (Set.instMembershipSet.{u2} (β i)) (x i) (t i a))) (Set.pi.{u3, u2} ι (fun (i : ι) => β i) (HasCompl.compl.{u3} (Set.{u3} ι) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} ι) (Set.instBooleanAlgebraSet.{u3} ι)) (Singleton.singleton.{u3, u3} ι (Set.{u3} ι) (Set.instSingletonSet.{u3} ι) i)) (fun (j : ι) => t j (f j))))
Case conversion may be inaccurate. Consider using '#align set.univ_pi_update Set.univ_pi_updateₓ'. -/
theorem univ_pi_update [DecidableEq ι] {β : ∀ i, Type _} (i : ι) (f : ∀ j, α j) (a : α i)
    (t : ∀ j, α j → Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i ∈ t i a } ∩ pi ({i}ᶜ) fun j => t j (f j) :=
  by rw [compl_eq_univ_diff, ← pi_update_of_mem (mem_univ _)]
#align set.univ_pi_update Set.univ_pi_update

/- warning: set.univ_pi_update_univ -> Set.univ_pi_update_univ is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} ι] (i : ι) (s : Set.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (j : ι) => α j) (Set.univ.{u1} ι) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => Set.{u2} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (j : ι) => Set.univ.{u2} (α j)) i s)) (Set.preimage.{max u1 u2, u2} (forall (i : ι), α i) (α i) (Function.eval.{succ u1, succ u2} ι (fun (i : ι) => α i) i) s)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} [_inst_1 : DecidableEq.{succ u2} ι] (i : ι) (s : Set.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (j : ι) => α j) (Set.univ.{u2} ι) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => Set.{u1} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (j : ι) => Set.univ.{u1} (α j)) i s)) (Set.preimage.{max u2 u1, u1} (forall (i : ι), α i) (α i) (Function.eval.{succ u2, succ u1} ι α i) s)
Case conversion may be inaccurate. Consider using '#align set.univ_pi_update_univ Set.univ_pi_update_univₓ'. -/
theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t, pi_univ, inter_univ, preimage]
#align set.univ_pi_update_univ Set.univ_pi_update_univ

/- warning: set.eval_image_pi_subset -> Set.eval_image_pi_subset is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (HasSubset.Subset.{u2} (Set.{u2} (α i)) (Set.hasSubset.{u2} (α i)) (Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (x : ι) => α x) i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (HasSubset.Subset.{u1} (Set.{u1} (α i)) (Set.instHasSubsetSet_1.{u1} (α i)) (Set.image.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι (fun (x : ι) => α x) i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.eval_image_pi_subset Set.eval_image_pi_subsetₓ'. -/
theorem eval_image_pi_subset (hs : i ∈ s) : eval i '' s.pi t ⊆ t i :=
  image_subset_iff.2 fun f hf => hf i hs
#align set.eval_image_pi_subset Set.eval_image_pi_subset

#print Set.eval_image_univ_pi_subset /-
theorem eval_image_univ_pi_subset : eval i '' pi univ t ⊆ t i :=
  eval_image_pi_subset (mem_univ i)
#align set.eval_image_univ_pi_subset Set.eval_image_univ_pi_subset
-/

/- warning: set.subset_eval_image_pi -> Set.subset_eval_image_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)}, (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) -> (forall (i : ι), HasSubset.Subset.{u2} (Set.{u2} (α i)) (Set.hasSubset.{u2} (α i)) (t i) (Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι α i) (Set.pi.{u1, u2} ι (fun (x : ι) => α x) s t)))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)}, (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) -> (forall (i : ι), HasSubset.Subset.{u1} (Set.{u1} (α i)) (Set.instHasSubsetSet_1.{u1} (α i)) (t i) (Set.image.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) (Set.pi.{u2, u1} ι (fun (x : ι) => α x) s t)))
Case conversion may be inaccurate. Consider using '#align set.subset_eval_image_pi Set.subset_eval_image_piₓ'. -/
theorem subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i ⊆ eval i '' s.pi t := by
  classical
    obtain ⟨f, hf⟩ := ht
    refine' fun y hy => ⟨update f i y, fun j hj => _, update_same _ _ _⟩
    obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]
#align set.subset_eval_image_pi Set.subset_eval_image_pi

/- warning: set.eval_image_pi -> Set.eval_image_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun (x : ι) => α x) i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.image.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι (fun (x : ι) => α x) i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.eval_image_pi Set.eval_image_piₓ'. -/
theorem eval_image_pi (hs : i ∈ s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)
#align set.eval_image_pi Set.eval_image_pi

/- warning: set.eval_image_univ_pi -> Set.eval_image_univ_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} {i : ι}, (Set.Nonempty.{max u1 u2} (forall (i : ι), α i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t)) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.image.{max u1 u2, u2} (forall (i : ι), α i) (α i) (fun (f : forall (i : ι), α i) => f i) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} {i : ι}, (Set.Nonempty.{max u2 u1} (forall (i : ι), α i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t)) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.image.{max u2 u1, u1} (forall (i : ι), α i) (α i) (fun (f : forall (i : ι), α i) => f i) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.eval_image_univ_pi Set.eval_image_univ_piₓ'. -/
@[simp]
theorem eval_image_univ_pi (ht : (pi univ t).Nonempty) :
    (fun f : ∀ i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht
#align set.eval_image_univ_pi Set.eval_image_univ_pi

#print Set.pi_subset_pi_iff /-
theorem pi_subset_pi_iff : pi s t₁ ⊆ pi s t₂ ↔ (∀ i ∈ s, t₁ i ⊆ t₂ i) ∨ pi s t₁ = ∅ :=
  by
  refine'
    ⟨fun h => or_iff_not_imp_right.2 _, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne.def, ← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_subset (fun f : ∀ i, α i => f i) h
#align set.pi_subset_pi_iff Set.pi_subset_pi_iff
-/

#print Set.univ_pi_subset_univ_pi_iff /-
theorem univ_pi_subset_univ_pi_iff : pi univ t₁ ⊆ pi univ t₂ ↔ (∀ i, t₁ i ⊆ t₂ i) ∨ ∃ i, t₁ i = ∅ :=
  by simp [pi_subset_pi_iff]
#align set.univ_pi_subset_univ_pi_iff Set.univ_pi_subset_univ_pi_iff
-/

/- warning: set.eval_preimage -> Set.eval_preimage is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι] {s : Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (x : ι), α x)) (Set.preimage.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun {i : ι} => α i) i) s) (Set.pi.{u1, u2} ι (fun (x : ι) => α x) (Set.univ.{u1} ι) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => Set.{u2} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => Set.univ.{u2} (α i)) i s))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {i : ι} [_inst_1 : DecidableEq.{succ u2} ι] {s : Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (x : ι), α x)) (Set.preimage.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) s) (Set.pi.{u2, u1} ι α (Set.univ.{u2} ι) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => Set.{u1} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => Set.univ.{u1} (α i)) i s))
Case conversion may be inaccurate. Consider using '#align set.eval_preimage Set.eval_preimageₓ'. -/
theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun i => univ) i s) :=
  by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' ∈ y]
#align set.eval_preimage Set.eval_preimage

/- warning: set.eval_preimage' -> Set.eval_preimage' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι] {s : Set.{u2} (α i)}, Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (x : ι), α x)) (Set.preimage.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι (fun {i : ι} => α i) i) s) (Set.pi.{u1, u2} ι (fun (x : ι) => α x) (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.hasSingleton.{u1} ι) i) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => Set.{u2} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => Set.univ.{u2} (α i)) i s))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {i : ι} [_inst_1 : DecidableEq.{succ u2} ι] {s : Set.{u1} (α i)}, Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (x : ι), α x)) (Set.preimage.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) s) (Set.pi.{u2, u1} ι α (Singleton.singleton.{u2, u2} ι (Set.{u2} ι) (Set.instSingletonSet.{u2} ι) i) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => Set.{u1} (α i)) (fun (a : ι) (b : ι) => _inst_1 a b) (fun (i : ι) => Set.univ.{u1} (α i)) i s))
Case conversion may be inaccurate. Consider using '#align set.eval_preimage' Set.eval_preimage'ₓ'. -/
theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun i => univ) i s) :=
  by
  ext
  simp
#align set.eval_preimage' Set.eval_preimage'

/- warning: set.update_preimage_pi -> Set.update_preimage_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {s : Set.{u1} ι} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι] {f : forall (i : ι), α i}, (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) -> (forall (j : ι), (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) j s) -> (Ne.{succ u1} ι j i) -> (Membership.Mem.{u2, u2} (α j) (Set.{u2} (α j)) (Set.hasMem.{u2} (α j)) (f j) (t j))) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.preimage.{u2, max u1 u2} (α i) (forall (a : ι), α a) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) f i) (Set.pi.{u1, u2} ι (fun (a : ι) => α a) s t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {s : Set.{u2} ι} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} [_inst_1 : DecidableEq.{succ u2} ι] {f : forall (i : ι), α i}, (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) -> (forall (j : ι), (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) j s) -> (Ne.{succ u2} ι j i) -> (Membership.mem.{u1, u1} (α j) (Set.{u1} (α j)) (Set.instMembershipSet.{u1} (α j)) (f j) (t j))) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.preimage.{u1, max u2 u1} (α i) (forall (a : ι), α a) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) f i) (Set.pi.{u2, u1} ι (fun (a : ι) => α a) s t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.update_preimage_pi Set.update_preimage_piₓ'. -/
theorem update_preimage_pi [DecidableEq ι] {f : ∀ i, α i} (hi : i ∈ s)
    (hf : ∀ j ∈ s, j ≠ i → f j ∈ t j) : update f i ⁻¹' s.pi t = t i :=
  by
  ext x
  refine' ⟨fun h => _, fun hx j hj => _⟩
  · convert h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_noteq h]
      exact hf j hj h
#align set.update_preimage_pi Set.update_preimage_pi

/- warning: set.update_preimage_univ_pi -> Set.update_preimage_univ_pi is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} {t : forall (i : ι), Set.{u2} (α i)} {i : ι} [_inst_1 : DecidableEq.{succ u1} ι] {f : forall (i : ι), α i}, (forall (j : ι), (Ne.{succ u1} ι j i) -> (Membership.Mem.{u2, u2} (α j) (Set.{u2} (α j)) (Set.hasMem.{u2} (α j)) (f j) (t j))) -> (Eq.{succ u2} (Set.{u2} (α i)) (Set.preimage.{u2, max u1 u2} (α i) (forall (a : ι), α a) (Function.update.{succ u1, succ u2} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) f i) (Set.pi.{u1, u2} ι (fun (a : ι) => α a) (Set.univ.{u1} ι) t)) (t i))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} {t : forall (i : ι), Set.{u1} (α i)} {i : ι} [_inst_1 : DecidableEq.{succ u2} ι] {f : forall (i : ι), α i}, (forall (j : ι), (Ne.{succ u2} ι j i) -> (Membership.mem.{u1, u1} (α j) (Set.{u1} (α j)) (Set.instMembershipSet.{u1} (α j)) (f j) (t j))) -> (Eq.{succ u1} (Set.{u1} (α i)) (Set.preimage.{u1, max u2 u1} (α i) (forall (a : ι), α a) (Function.update.{succ u2, succ u1} ι (fun (i : ι) => α i) (fun (a : ι) (b : ι) => _inst_1 a b) f i) (Set.pi.{u2, u1} ι (fun (a : ι) => α a) (Set.univ.{u2} ι) t)) (t i))
Case conversion may be inaccurate. Consider using '#align set.update_preimage_univ_pi Set.update_preimage_univ_piₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j «expr ≠ » i) -/
theorem update_preimage_univ_pi [DecidableEq ι] {f : ∀ i, α i} (hf : ∀ (j) (_ : j ≠ i), f j ∈ t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j
#align set.update_preimage_univ_pi Set.update_preimage_univ_pi

/- warning: set.subset_pi_eval_image -> Set.subset_pi_eval_image is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) (u : Set.{max u1 u2} (forall (i : ι), α i)), HasSubset.Subset.{max u1 u2} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.hasSubset.{max u1 u2} (forall (i : ι), α i)) u (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.image.{max u1 u2, u2} (forall (x : ι), α x) (α i) (Function.eval.{succ u1, succ u2} ι α i) u))
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) (u : Set.{max u2 u1} (forall (i : ι), α i)), HasSubset.Subset.{max u2 u1} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.instHasSubsetSet_1.{max u2 u1} (forall (i : ι), α i)) u (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s (fun (i : ι) => Set.image.{max u2 u1, u1} (forall (x : ι), α x) (α i) (Function.eval.{succ u2, succ u1} ι α i) u))
Case conversion may be inaccurate. Consider using '#align set.subset_pi_eval_image Set.subset_pi_eval_imageₓ'. -/
theorem subset_pi_eval_image (s : Set ι) (u : Set (∀ i, α i)) : u ⊆ pi s fun i => eval i '' u :=
  fun f hf i hi => ⟨f, hf, rfl⟩
#align set.subset_pi_eval_image Set.subset_pi_eval_image

/- warning: set.univ_pi_ite -> Set.univ_pi_ite is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {α : ι -> Type.{u2}} (s : Set.{u1} ι) [_inst_1 : DecidablePred.{succ u1} ι (fun (_x : ι) => Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) _x s)] (t : forall (i : ι), Set.{u2} (α i)), Eq.{succ (max u1 u2)} (Set.{max u1 u2} (forall (i : ι), α i)) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) (Set.univ.{u1} ι) (fun (i : ι) => ite.{succ u2} (Set.{u2} (α i)) (Membership.Mem.{u1, u1} ι (Set.{u1} ι) (Set.hasMem.{u1} ι) i s) (_inst_1 i) (t i) (Set.univ.{u2} (α i)))) (Set.pi.{u1, u2} ι (fun (i : ι) => α i) s t)
but is expected to have type
  forall {ι : Type.{u2}} {α : ι -> Type.{u1}} (s : Set.{u2} ι) [_inst_1 : DecidablePred.{succ u2} ι (fun (_x : ι) => Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) _x s)] (t : forall (i : ι), Set.{u1} (α i)), Eq.{max (succ u2) (succ u1)} (Set.{max u2 u1} (forall (i : ι), α i)) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) (Set.univ.{u2} ι) (fun (i : ι) => ite.{succ u1} (Set.{u1} (α i)) (Membership.mem.{u2, u2} ι (Set.{u2} ι) (Set.instMembershipSet.{u2} ι) i s) (_inst_1 i) (t i) (Set.univ.{u1} (α i)))) (Set.pi.{u2, u1} ι (fun (i : ι) => α i) s t)
Case conversion may be inaccurate. Consider using '#align set.univ_pi_ite Set.univ_pi_iteₓ'. -/
theorem univ_pi_ite (s : Set ι) [DecidablePred (· ∈ s)] (t : ∀ i, Set (α i)) :
    (pi univ fun i => if i ∈ s then t i else univ) = s.pi t :=
  by
  ext
  simp_rw [mem_univ_pi]
  refine' forall_congr' fun i => _
  split_ifs <;> simp [h]
#align set.univ_pi_ite Set.univ_pi_ite

end Pi

end Set

