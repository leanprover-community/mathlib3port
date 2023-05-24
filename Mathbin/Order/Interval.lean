/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.interval
! leanprover-community/mathlib commit 38df578a6450a8c5142b3727e3ae894c2300cae0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.Basic
import Mathbin.Data.Set.Lattice
import Mathbin.Data.SetLike.Basic

/-!
# Order intervals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines (nonempty) closed intervals in an order (see `set.Icc`). This is a prototype for
interval arithmetic.

## Main declarations

* `nonempty_interval`: Nonempty intervals. Pairs where the second element is greater than the first.
* `interval`: Intervals. Either `∅` or a nonempty interval.
-/


open Function OrderDual Set

variable {α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

#print NonemptyInterval /-
/-- The nonempty closed intervals in an order.

We define intervals by the pair of endpoints `fst`, `snd`. To convert intervals to the set of
elements between these endpoints, use the coercion `nonempty_interval α → set α`. -/
@[ext]
structure NonemptyInterval (α : Type _) [LE α] extends α × α where
  fst_le_snd : fst ≤ snd
#align nonempty_interval NonemptyInterval
-/

namespace NonemptyInterval

section LE

variable [LE α] {s t : NonemptyInterval α}

#print NonemptyInterval.toProd_injective /-
theorem toProd_injective : Injective (toProd : NonemptyInterval α → α × α) := fun s t =>
  (ext_iff _ _).2
#align nonempty_interval.to_prod_injective NonemptyInterval.toProd_injective
-/

#print NonemptyInterval.toDualProd /-
/-- The injection that induces the order on intervals. -/
def toDualProd : NonemptyInterval α → αᵒᵈ × α :=
  toProd
#align nonempty_interval.to_dual_prod NonemptyInterval.toDualProd
-/

#print NonemptyInterval.toDualProd_apply /-
@[simp]
theorem toDualProd_apply (s : NonemptyInterval α) : s.toDualProd = (toDual s.fst, s.snd) :=
  Prod.mk.eta.symm
#align nonempty_interval.to_dual_prod_apply NonemptyInterval.toDualProd_apply
-/

#print NonemptyInterval.toDualProd_injective /-
theorem toDualProd_injective : Injective (toDualProd : NonemptyInterval α → αᵒᵈ × α) :=
  toProd_injective
#align nonempty_interval.to_dual_prod_injective NonemptyInterval.toDualProd_injective
-/

instance [IsEmpty α] : IsEmpty (NonemptyInterval α) :=
  ⟨fun s => isEmptyElim s.fst⟩

instance [Subsingleton α] : Subsingleton (NonemptyInterval α) :=
  toDualProd_injective.Subsingleton

instance : LE (NonemptyInterval α) :=
  ⟨fun s t => t.fst ≤ s.fst ∧ s.snd ≤ t.snd⟩

#print NonemptyInterval.le_def /-
theorem le_def : s ≤ t ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd :=
  Iff.rfl
#align nonempty_interval.le_def NonemptyInterval.le_def
-/

#print NonemptyInterval.toDualProdHom /-
/-- `to_dual_prod` as an order embedding. -/
@[simps]
def toDualProdHom : NonemptyInterval α ↪o αᵒᵈ × α
    where
  toFun := toDualProd
  inj' := toDualProd_injective
  map_rel_iff' _ _ := Iff.rfl
#align nonempty_interval.to_dual_prod_hom NonemptyInterval.toDualProdHom
-/

#print NonemptyInterval.dual /-
/-- Turn an interval into an interval in the dual order. -/
def dual : NonemptyInterval α ≃ NonemptyInterval αᵒᵈ
    where
  toFun s := ⟨s.toProd.symm, s.fst_le_snd⟩
  invFun s := ⟨s.toProd.symm, s.fst_le_snd⟩
  left_inv s := ext _ _ <| Prod.swap_swap _
  right_inv s := ext _ _ <| Prod.swap_swap _
#align nonempty_interval.dual NonemptyInterval.dual
-/

#print NonemptyInterval.fst_dual /-
@[simp]
theorem fst_dual (s : NonemptyInterval α) : s.dual.fst = toDual s.snd :=
  rfl
#align nonempty_interval.fst_dual NonemptyInterval.fst_dual
-/

#print NonemptyInterval.snd_dual /-
@[simp]
theorem snd_dual (s : NonemptyInterval α) : s.dual.snd = toDual s.fst :=
  rfl
#align nonempty_interval.snd_dual NonemptyInterval.snd_dual
-/

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {s : NonemptyInterval α} {x : α × α}
  {a : α}

instance : Preorder (NonemptyInterval α) :=
  Preorder.lift toDualProd

instance : CoeTC (NonemptyInterval α) (Set α) :=
  ⟨fun s => Icc s.fst s.snd⟩

instance (priority := 100) : Membership α (NonemptyInterval α) :=
  ⟨fun a s => a ∈ (s : Set α)⟩

/- warning: nonempty_interval.mem_mk -> NonemptyInterval.mem_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {x : Prod.{u1, u1} α α} {a : α} {hx : LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)}, Iff (Membership.Mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.hasMem.{u1} α _inst_1) a (NonemptyInterval.mk.{u1} α (Preorder.toHasLe.{u1} α _inst_1) x hx)) (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (Prod.fst.{u1, u1} α α x) a) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a (Prod.snd.{u1, u1} α α x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {x : Prod.{u1, u1} α α} {a : α} {hx : LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x)}, Iff (Membership.mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instMembershipNonemptyIntervalToLE.{u1} α _inst_1) a (NonemptyInterval.mk.{u1} α (Preorder.toLE.{u1} α _inst_1) x hx)) (And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u1} α α x) a) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (Prod.snd.{u1, u1} α α x)))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.mem_mk NonemptyInterval.mem_mkₓ'. -/
@[simp]
theorem mem_mk {hx : x.1 ≤ x.2} : a ∈ mk x hx ↔ x.1 ≤ a ∧ a ≤ x.2 :=
  Iff.rfl
#align nonempty_interval.mem_mk NonemptyInterval.mem_mk

/- warning: nonempty_interval.mem_def -> NonemptyInterval.mem_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)} {a : α}, Iff (Membership.Mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.hasMem.{u1} α _inst_1) a s) (And (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α _inst_1) s)) a) (LE.le.{u1} α (Preorder.toHasLe.{u1} α _inst_1) a (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α _inst_1) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)} {a : α}, Iff (Membership.mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instMembershipNonemptyIntervalToLE.{u1} α _inst_1) a s) (And (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α _inst_1) s)) a) (LE.le.{u1} α (Preorder.toLE.{u1} α _inst_1) a (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.mem_def NonemptyInterval.mem_defₓ'. -/
theorem mem_def : a ∈ s ↔ s.fst ≤ a ∧ a ≤ s.snd :=
  Iff.rfl
#align nonempty_interval.mem_def NonemptyInterval.mem_def

/- warning: nonempty_interval.coe_nonempty -> NonemptyInterval.coe_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)), Set.Nonempty.{u1} α ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α _inst_1))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)), Set.Nonempty.{u1} α (Set.Icc.{u1} α _inst_1 (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α _inst_1) s)) (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_nonempty NonemptyInterval.coe_nonemptyₓ'. -/
@[simp]
theorem coe_nonempty (s : NonemptyInterval α) : (s : Set α).Nonempty :=
  nonempty_Icc.2 s.fst_le_snd
#align nonempty_interval.coe_nonempty NonemptyInterval.coe_nonempty

/- warning: nonempty_interval.pure -> NonemptyInterval.pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], α -> (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], α -> (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.pure NonemptyInterval.pureₓ'. -/
/-- `{a}` as an interval. -/
@[simps]
def pure (a : α) : NonemptyInterval α :=
  ⟨⟨a, a⟩, le_rfl⟩
#align nonempty_interval.pure NonemptyInterval.pure

#print NonemptyInterval.mem_pure_self /-
theorem mem_pure_self (a : α) : a ∈ pure a :=
  ⟨le_rfl, le_rfl⟩
#align nonempty_interval.mem_pure_self NonemptyInterval.mem_pure_self
-/

/- warning: nonempty_interval.pure_injective -> NonemptyInterval.pure_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Function.Injective.{succ u1, succ u1} α (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.pure.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Function.Injective.{succ u1, succ u1} α (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.pure.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.pure_injective NonemptyInterval.pure_injectiveₓ'. -/
theorem pure_injective : Injective (pure : α → NonemptyInterval α) := fun s t =>
  congr_arg <| Prod.fst ∘ toProd
#align nonempty_interval.pure_injective NonemptyInterval.pure_injective

/- warning: nonempty_interval.dual_pure -> NonemptyInterval.dual_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.pure.{u1} α _inst_1 a)) (NonemptyInterval.pure.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (NonemptyInterval.pure.{u1} α _inst_1 a)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (fun (_x : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.pure.{u1} α _inst_1 a)) (NonemptyInterval.pure.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u1} α) a) (OrderDual.preorder.{u1} α _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.dual_pure NonemptyInterval.dual_pureₓ'. -/
@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align nonempty_interval.dual_pure NonemptyInterval.dual_pure

instance [Inhabited α] : Inhabited (NonemptyInterval α) :=
  ⟨pure default⟩

instance : ∀ [Nonempty α], Nonempty (NonemptyInterval α) :=
  Nonempty.map pure

instance [Nontrivial α] : Nontrivial (NonemptyInterval α) :=
  pure_injective.Nontrivial

/- warning: nonempty_interval.map -> NonemptyInterval.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) -> (NonemptyInterval.{u2} β (Preorder.toLE.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.map NonemptyInterval.mapₓ'. -/
/-- Pushforward of nonempty intervals. -/
@[simps]
def map (f : α →o β) (a : NonemptyInterval α) : NonemptyInterval β :=
  ⟨a.toProd.map f f, f.mono a.fst_le_snd⟩
#align nonempty_interval.map NonemptyInterval.map

/- warning: nonempty_interval.map_pure -> NonemptyInterval.map_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.map.{u1, u2} α β _inst_1 _inst_2 f (NonemptyInterval.pure.{u1} α _inst_1 a)) (NonemptyInterval.pure.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : OrderHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : OrderHom.{u2, u1} α β _inst_1 _inst_2) (a : α), Eq.{succ u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.map.{u2, u1} α β _inst_1 _inst_2 f (NonemptyInterval.pure.{u2} α _inst_1 a)) (NonemptyInterval.pure.{u1} β _inst_2 (OrderHom.toFun.{u2, u1} α β _inst_1 _inst_2 f a))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.map_pure NonemptyInterval.map_pureₓ'. -/
@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align nonempty_interval.map_pure NonemptyInterval.map_pure

/- warning: nonempty_interval.map_map -> NonemptyInterval.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (g : OrderHom.{u2, u3} β γ _inst_2 _inst_3) (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (a : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)), Eq.{succ u3} (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.map.{u2, u3} β γ _inst_2 _inst_3 g (NonemptyInterval.map.{u1, u2} α β _inst_1 _inst_2 f a)) (NonemptyInterval.map.{u1, u3} α γ _inst_1 _inst_3 (OrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f) a)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u2} γ] (g : OrderHom.{u3, u2} β γ _inst_2 _inst_3) (f : OrderHom.{u1, u3} α β _inst_1 _inst_2) (a : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)), Eq.{succ u2} (NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (NonemptyInterval.map.{u3, u2} β γ _inst_2 _inst_3 g (NonemptyInterval.map.{u1, u3} α β _inst_1 _inst_2 f a)) (NonemptyInterval.map.{u1, u2} α γ _inst_1 _inst_3 (OrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f) a)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.map_map NonemptyInterval.map_mapₓ'. -/
@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (a : NonemptyInterval α) :
    (a.map f).map g = a.map (g.comp f) :=
  rfl
#align nonempty_interval.map_map NonemptyInterval.map_map

/- warning: nonempty_interval.dual_map -> NonemptyInterval.dual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (a : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)), Eq.{succ u2} (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (fun (_x : Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) => (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) -> (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (Equiv.hasCoeToFun.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (NonemptyInterval.dual.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.map.{u1, u2} α β _inst_1 _inst_2 f a)) (NonemptyInterval.map.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) => (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (OrderHom.dual.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : OrderHom.{u2, u1} α β _inst_1 _inst_2) (a : NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2))) (NonemptyInterval.map.{u2, u1} α β _inst_1 _inst_2 f a)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (fun (_x : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (NonemptyInterval.dual.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.map.{u2, u1} α β _inst_1 _inst_2 f a)) (NonemptyInterval.map.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u2, u1} α β _inst_1 _inst_2) (OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2))) (OrderHom.{u2, u1} α β _inst_1 _inst_2) (fun (_x : OrderHom.{u2, u1} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderHom.{u2, u1} α β _inst_1 _inst_2) => OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u2, u1} α β _inst_1 _inst_2) (OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2))) (OrderHom.dual.{u2, u1} α β _inst_1 _inst_2) f) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (NonemptyInterval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1)))) (NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (fun (_x : NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)) => NonemptyInterval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (NonemptyInterval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (NonemptyInterval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1)))) (NonemptyInterval.dual.{u2} α (Preorder.toLE.{u2} α _inst_1)) a))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.dual_map NonemptyInterval.dual_mapₓ'. -/
@[simp]
theorem dual_map (f : α →o β) (a : NonemptyInterval α) : (a.map f).dual = a.dual.map f.dual :=
  rfl
#align nonempty_interval.dual_map NonemptyInterval.dual_map

/- warning: nonempty_interval.map₂ -> NonemptyInterval.map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (f : α -> β -> γ), (forall (b : β), Monotone.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) -> (forall (a : α), Monotone.{u2, u3} β γ _inst_2 _inst_3 (f a)) -> (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) -> (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (f : α -> β -> γ), (forall (b : β), Monotone.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) -> (forall (a : α), Monotone.{u2, u3} β γ _inst_2 _inst_3 (f a)) -> (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) -> (NonemptyInterval.{u2} β (Preorder.toLE.{u2} β _inst_2)) -> (NonemptyInterval.{u3} γ (Preorder.toLE.{u3} γ _inst_3))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.map₂ NonemptyInterval.map₂ₓ'. -/
/-- Binary pushforward of nonempty intervals. -/
@[simps]
def map₂ (f : α → β → γ) (h₀ : ∀ b, Monotone fun a => f a b) (h₁ : ∀ a, Monotone (f a)) :
    NonemptyInterval α → NonemptyInterval β → NonemptyInterval γ := fun s t =>
  ⟨(f s.fst t.fst, f s.snd t.snd), (h₀ _ s.fst_le_snd).trans <| h₁ _ t.fst_le_snd⟩
#align nonempty_interval.map₂ NonemptyInterval.map₂

/- warning: nonempty_interval.map₂_pure -> NonemptyInterval.map₂_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (f : α -> β -> γ) (h₀ : forall (b : β), Monotone.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) (h₁ : forall (a : α), Monotone.{u2, u3} β γ _inst_2 _inst_3 (f a)) (a : α) (b : β), Eq.{succ u3} (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.map₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f h₀ h₁ (NonemptyInterval.pure.{u1} α _inst_1 a) (NonemptyInterval.pure.{u2} β _inst_2 b)) (NonemptyInterval.pure.{u3} γ _inst_3 (f a b))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : Preorder.{u2} γ] (f : α -> β -> γ) (h₀ : forall (b : β), Monotone.{u3, u2} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) (h₁ : forall (a : α), Monotone.{u1, u2} β γ _inst_2 _inst_3 (f a)) (a : α) (b : β), Eq.{succ u2} (NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (NonemptyInterval.map₂.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 f h₀ h₁ (NonemptyInterval.pure.{u3} α _inst_1 a) (NonemptyInterval.pure.{u1} β _inst_2 b)) (NonemptyInterval.pure.{u2} γ _inst_3 (f a b))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.map₂_pure NonemptyInterval.map₂_pureₓ'. -/
@[simp]
theorem map₂_pure (f : α → β → γ) (h₀ h₁) (a : α) (b : β) :
    map₂ f h₀ h₁ (pure a) (pure b) = pure (f a b) :=
  rfl
#align nonempty_interval.map₂_pure NonemptyInterval.map₂_pure

/- warning: nonempty_interval.dual_map₂ -> NonemptyInterval.dual_map₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (f : α -> β -> γ) (h₀ : forall (b : β), Monotone.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) (h₁ : forall (a : α), Monotone.{u2, u3} β γ _inst_2 _inst_3 (f a)) (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (t : NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)), Eq.{succ u3} (NonemptyInterval.{u3} (OrderDual.{u3} γ) (OrderDual.hasLe.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3))) (coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.{u3} (OrderDual.{u3} γ) (OrderDual.hasLe.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)))) (fun (_x : Equiv.{succ u3, succ u3} (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.{u3} (OrderDual.{u3} γ) (OrderDual.hasLe.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)))) => (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) -> (NonemptyInterval.{u3} (OrderDual.{u3} γ) (OrderDual.hasLe.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)))) (Equiv.hasCoeToFun.{succ u3, succ u3} (NonemptyInterval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.{u3} (OrderDual.{u3} γ) (OrderDual.hasLe.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)))) (NonemptyInterval.dual.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (NonemptyInterval.map₂.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f h₀ h₁ s t)) (NonemptyInterval.map₂.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2) (OrderDual.preorder.{u3} γ _inst_3) (fun (a : OrderDual.{u1} α) (b : OrderDual.{u2} β) => coeFn.{succ u3, succ u3} (Equiv.{succ u3, succ u3} γ (OrderDual.{u3} γ)) (fun (_x : Equiv.{succ u3, succ u3} γ (OrderDual.{u3} γ)) => γ -> (OrderDual.{u3} γ)) (Equiv.hasCoeToFun.{succ u3, succ u3} γ (OrderDual.{u3} γ)) (OrderDual.toDual.{u3} γ) (f (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) a) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) b))) (fun (_x : OrderDual.{u2} β) => Monotone.dual.{u1, u3} α γ _inst_1 _inst_3 (fun (a : α) => f a (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) _x)) (h₀ (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} β) β) => (OrderDual.{u2} β) -> β) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} β) β) (OrderDual.ofDual.{u2} β) _x))) (fun (_x : OrderDual.{u1} α) => Monotone.dual.{u2, u3} β γ _inst_2 _inst_3 (f (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) _x)) (h₁ (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α) _x))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) s) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (fun (_x : Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) => (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) -> (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (Equiv.hasCoeToFun.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (NonemptyInterval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (NonemptyInterval.dual.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} [_inst_1 : Preorder.{u3} α] [_inst_2 : Preorder.{u1} β] [_inst_3 : Preorder.{u2} γ] (f : α -> β -> γ) (h₀ : forall (b : β), Monotone.{u3, u2} α γ _inst_1 _inst_3 (fun (a : α) => f a b)) (h₁ : forall (a : α), Monotone.{u1, u2} β γ _inst_2 _inst_3 (f a)) (s : NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) (t : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) => NonemptyInterval.{u2} (OrderDual.{u2} γ) (OrderDual.instLEOrderDual.{u2} γ (Preorder.toLE.{u2} γ _inst_3))) (NonemptyInterval.map₂.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 f h₀ h₁ s t)) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (NonemptyInterval.{u2} (OrderDual.{u2} γ) (OrderDual.instLEOrderDual.{u2} γ (Preorder.toLE.{u2} γ _inst_3)))) (NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (fun (_x : NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) => NonemptyInterval.{u2} (OrderDual.{u2} γ) (OrderDual.instLEOrderDual.{u2} γ (Preorder.toLE.{u2} γ _inst_3))) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (NonemptyInterval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (NonemptyInterval.{u2} (OrderDual.{u2} γ) (OrderDual.instLEOrderDual.{u2} γ (Preorder.toLE.{u2} γ _inst_3)))) (NonemptyInterval.dual.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (NonemptyInterval.map₂.{u3, u1, u2} α β γ _inst_1 _inst_2 _inst_3 f h₀ h₁ s t)) (NonemptyInterval.map₂.{u3, u1, u2} (OrderDual.{u3} α) (OrderDual.{u1} β) (OrderDual.{u2} γ) (OrderDual.preorder.{u3} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (OrderDual.preorder.{u2} γ _inst_3) (fun (a : OrderDual.{u3} α) (b : OrderDual.{u1} β) => FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} γ (OrderDual.{u2} γ)) γ (fun (_x : γ) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : γ) => OrderDual.{u2} γ) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} γ (OrderDual.{u2} γ)) (OrderDual.toDual.{u2} γ) (f (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β) b))) (fun (_x : OrderDual.{u1} β) => Monotone.dual.{u3, u2} α γ _inst_1 _inst_3 (fun (a : α) => f a (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β) _x)) (h₀ (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.{u1} β) (fun (_x : OrderDual.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} β) => β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} β) β) (OrderDual.ofDual.{u1} β) _x))) (fun (_x : OrderDual.{u3} α) => Monotone.dual.{u1, u2} β γ _inst_2 _inst_3 (f (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α) _x)) (h₁ (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.{u3} α) (fun (_x : OrderDual.{u3} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u3} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (OrderDual.{u3} α) α) (OrderDual.ofDual.{u3} α) _x))) (FunLike.coe.{succ u3, succ u3, succ u3} (Equiv.{succ u3, succ u3} (NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) (NonemptyInterval.{u3} (OrderDual.{u3} α) (OrderDual.instLEOrderDual.{u3} α (Preorder.toLE.{u3} α _inst_1)))) (NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) (fun (_x : NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) => NonemptyInterval.{u3} (OrderDual.{u3} α) (OrderDual.instLEOrderDual.{u3} α (Preorder.toLE.{u3} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u3, succ u3} (NonemptyInterval.{u3} α (Preorder.toLE.{u3} α _inst_1)) (NonemptyInterval.{u3} (OrderDual.{u3} α) (OrderDual.instLEOrderDual.{u3} α (Preorder.toLE.{u3} α _inst_1)))) (NonemptyInterval.dual.{u3} α (Preorder.toLE.{u3} α _inst_1)) s) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (fun (_x : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (NonemptyInterval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (NonemptyInterval.dual.{u1} β (Preorder.toLE.{u1} β _inst_2)) t))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.dual_map₂ NonemptyInterval.dual_map₂ₓ'. -/
@[simp]
theorem dual_map₂ (f : α → β → γ) (h₀ h₁ s t) :
    (map₂ f h₀ h₁ s t).dual =
      map₂ (fun a b => toDual <| f (ofDual a) <| ofDual b) (fun _ => (h₀ _).dual)
        (fun _ => (h₁ _).dual) s.dual t.dual :=
  rfl
#align nonempty_interval.dual_map₂ NonemptyInterval.dual_map₂

variable [BoundedOrder α]

instance : OrderTop (NonemptyInterval α)
    where
  top := ⟨⟨⊥, ⊤⟩, bot_le⟩
  le_top a := ⟨bot_le, le_top⟩

/- warning: nonempty_interval.dual_top -> NonemptyInterval.dual_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_5 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α _inst_1)], Eq.{succ u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderTop.toHasTop.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.orderTop.{u1} α _inst_1 _inst_5)))) (Top.top.{u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (OrderTop.toHasTop.{u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} (OrderDual.{u1} α) (Preorder.toHasLe.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (NonemptyInterval.orderTop.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.boundedOrder.{u1} α (Preorder.toHasLe.{u1} α _inst_1) _inst_5))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_5 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_5)))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (fun (_x : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (NonemptyInterval.dual.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_5)))) (Top.top.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_5)))) (OrderTop.toTop.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_5)))) (NonemptyInterval.le.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.boundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_5))))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.dual_top NonemptyInterval.dual_topₓ'. -/
@[simp]
theorem dual_top : (⊤ : NonemptyInterval α).dual = ⊤ :=
  rfl
#align nonempty_interval.dual_top NonemptyInterval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : NonemptyInterval α} {x : α × α} {a b : α}

instance : PartialOrder (NonemptyInterval α) :=
  PartialOrder.lift _ toDualProd_injective

/- warning: nonempty_interval.coe_hom -> NonemptyInterval.coeHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], OrderEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.hasLe.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], OrderEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.instLESet.{u1} α)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_hom NonemptyInterval.coeHomₓ'. -/
/-- Consider a nonempty interval `[a, b]` as the set `[a, b]`. -/
def coeHom : NonemptyInterval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff (fun s => Icc s.fst s.snd) fun s t => Icc_subset_Icc_iff s.fst_le_snd
#align nonempty_interval.coe_hom NonemptyInterval.coeHom

instance : SetLike (NonemptyInterval α) α
    where
  coe s := Icc s.fst s.snd
  coe_injective' := coeHom.Injective

/- warning: nonempty_interval.coe_subset_coe -> NonemptyInterval.coe_subset_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) t)) (LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) t)) (LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_subset_coe NonemptyInterval.coe_subset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align nonempty_interval.coe_subset_coe NonemptyInterval.coe_subset_coe

/- warning: nonempty_interval.coe_ssubset_coe -> NonemptyInterval.coe_ssubset_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) t)) (LT.lt.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Preorder.toHasLt.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) t)) (LT.lt.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Preorder.toLT.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.instPreorderNonemptyIntervalToLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_ssubset_coe NonemptyInterval.coe_ssubset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_ssubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align nonempty_interval.coe_ssubset_coe NonemptyInterval.coe_ssubset_coe

/- warning: nonempty_interval.coe_coe_hom -> NonemptyInterval.coe_coeHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Eq.{succ u1} ((fun (_x : RelEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) -> (Set.{u1} α)) (NonemptyInterval.coeHom.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (OrderEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.hasLe.{u1} α)) (fun (_x : RelEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) -> (Set.{u1} α)) (RelEmbedding.hasCoeToFun.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (LE.le.{u1} (Set.{u1} α) (Set.hasLe.{u1} α))) (NonemptyInterval.coeHom.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Eq.{succ u1} (forall (a : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => Set.{u1} α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (OrderEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.instLESet.{u1} α)) (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.869 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => Set.{u1} α) _x) (RelHomClass.toFunLike.{u1, u1, u1} (OrderEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.instLESet.{u1} α)) (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} α) => LE.le.{u1} (Set.{u1} α) (Set.instLESet.{u1} α) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699) (RelEmbedding.instRelHomClassRelEmbedding.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.682 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (x._@.Mathlib.Order.Hom.Basic._hyg.684 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => LE.le.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) x._@.Mathlib.Order.Hom.Basic._hyg.682 x._@.Mathlib.Order.Hom.Basic._hyg.684) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.697 : Set.{u1} α) (x._@.Mathlib.Order.Hom.Basic._hyg.699 : Set.{u1} α) => LE.le.{u1} (Set.{u1} α) (Set.instLESet.{u1} α) x._@.Mathlib.Order.Hom.Basic._hyg.697 x._@.Mathlib.Order.Hom.Basic._hyg.699))) (NonemptyInterval.coeHom.{u1} α _inst_1)) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_coe_hom NonemptyInterval.coe_coeHomₓ'. -/
@[simp]
theorem coe_coeHom : (coeHom : NonemptyInterval α → Set α) = coe :=
  rfl
#align nonempty_interval.coe_coe_hom NonemptyInterval.coe_coeHom

#print NonemptyInterval.coe_pure /-
@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
#align nonempty_interval.coe_pure NonemptyInterval.coe_pure
-/

#print NonemptyInterval.mem_pure /-
@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
#align nonempty_interval.mem_pure NonemptyInterval.mem_pure
-/

/- warning: nonempty_interval.coe_top -> NonemptyInterval.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (OrderTop.toHasTop.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.orderTop.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3)))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3)))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_top NonemptyInterval.coe_topₓ'. -/
@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Set α) = univ :=
  Icc_bot_top
#align nonempty_interval.coe_top NonemptyInterval.coe_top

/- warning: nonempty_interval.coe_dual -> NonemptyInterval.coe_dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} (OrderDual.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (NonemptyInterval.Set.hasCoeT.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (fun (_x : Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) => (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) -> (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (Equiv.hasCoeToFun.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (NonemptyInterval.dual.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (Set.preimage.{u1, u1} (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} (OrderDual.{u1} α)) (SetLike.coe.{u1, u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s) (OrderDual.{u1} α) (NonemptyInterval.setLike.{u1} (OrderDual.{u1} α) (OrderDual.partialOrder.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (NonemptyInterval.dual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (Set.preimage.{u1, u1} (OrderDual.{u1} α) α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.{u1} α) (fun (_x : OrderDual.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_dual NonemptyInterval.coe_dualₓ'. -/
@[simp, norm_cast]
theorem coe_dual (s : NonemptyInterval α) : (s.dual : Set αᵒᵈ) = ofDual ⁻¹' s :=
  dual_Icc
#align nonempty_interval.coe_dual NonemptyInterval.coe_dual

/- warning: nonempty_interval.subset_coe_map -> NonemptyInterval.subset_coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] (f : OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (fun (_x : OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (NonemptyInterval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (NonemptyInterval.Set.hasCoeT.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2)))) (NonemptyInterval.map.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] (f : OrderHom.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) (s : NonemptyInterval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β (OrderHom.toFun.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) f) (SetLike.coe.{u2, u2} (NonemptyInterval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))) α (NonemptyInterval.setLike.{u2} α _inst_1) s)) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) β (NonemptyInterval.setLike.{u1} β _inst_2) (NonemptyInterval.map.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) f s))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.subset_coe_map NonemptyInterval.subset_coe_mapₓ'. -/
theorem subset_coe_map (f : α →o β) (s : NonemptyInterval α) : f '' s ⊆ s.map f :=
  image_subset_iff.2 fun a ha => ⟨f.mono ha.1, f.mono ha.2⟩
#align nonempty_interval.subset_coe_map NonemptyInterval.subset_coe_map

end PartialOrder

section Lattice

variable [Lattice α]

instance : Sup (NonemptyInterval α) :=
  ⟨fun s t => ⟨⟨s.fst ⊓ t.fst, s.snd ⊔ t.snd⟩, inf_le_left.trans <| s.fst_le_snd.trans le_sup_left⟩⟩

instance : SemilatticeSup (NonemptyInterval α) :=
  toDualProd_injective.SemilatticeSup _ fun _ _ => rfl

/- warning: nonempty_interval.fst_sup -> NonemptyInterval.fst_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} α (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.hasSup.{u1} α _inst_1) s t))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) s)) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} α (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.instSupNonemptyIntervalToLEToPreorderToPartialOrderToSemilatticeInf.{u1} α _inst_1) s t))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α _inst_1) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) s)) (Prod.fst.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) t)))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.fst_sup NonemptyInterval.fst_supₓ'. -/
@[simp]
theorem fst_sup (s t : NonemptyInterval α) : (s ⊔ t).fst = s.fst ⊓ t.fst :=
  rfl
#align nonempty_interval.fst_sup NonemptyInterval.fst_sup

/- warning: nonempty_interval.snd_sup -> NonemptyInterval.snd_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} α (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.hasSup.{u1} α _inst_1) s t))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) s)) (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) t)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} α (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.instSupNonemptyIntervalToLEToPreorderToPartialOrderToSemilatticeInf.{u1} α _inst_1) s t))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α _inst_1)) (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) s)) (Prod.snd.{u1, u1} α α (NonemptyInterval.toProd.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) t)))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.snd_sup NonemptyInterval.snd_supₓ'. -/
@[simp]
theorem snd_sup (s t : NonemptyInterval α) : (s ⊔ t).snd = s.snd ⊔ t.snd :=
  rfl
#align nonempty_interval.snd_sup NonemptyInterval.snd_sup

end Lattice

end NonemptyInterval

#print Interval /-
/-- The closed intervals in an order.

We represent intervals either as `⊥` or a nonempty interval given by its endpoints `fst`, `snd`.
To convert intervals to the set of elements between these endpoints, use the coercion
`interval α → set α`. -/
def Interval (α : Type _) [LE α] :=
  WithBot (NonemptyInterval α)deriving Inhabited, LE, OrderBot
#align interval Interval
-/

namespace Interval

section LE

variable [LE α] {s t : Interval α}

instance : CoeTC (NonemptyInterval α) (Interval α) :=
  WithBot.hasCoeT

/- warning: interval.can_lift -> Interval.canLift is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α], CanLift.{succ u1, succ u1} (Interval.{u1} α _inst_1) (NonemptyInterval.{u1} α _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (Interval.hasCoeT.{u1} α _inst_1)))) (fun (r : Interval.{u1} α _inst_1) => Ne.{succ u1} (Interval.{u1} α _inst_1) r (Bot.bot.{u1} (Interval.{u1} α _inst_1) (OrderBot.toHasBot.{u1} (Interval.{u1} α _inst_1) (Interval.hasLe.{u1} α _inst_1) (Interval.orderBot.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α], CanLift.{succ u1, succ u1} (Interval.{u1} α _inst_1) (NonemptyInterval.{u1} α _inst_1) (WithBot.some.{u1} (NonemptyInterval.{u1} α _inst_1)) (fun (r : Interval.{u1} α _inst_1) => Ne.{succ u1} (Interval.{u1} α _inst_1) r (Bot.bot.{u1} (Interval.{u1} α _inst_1) (WithBot.bot.{u1} (NonemptyInterval.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align interval.can_lift Interval.canLiftₓ'. -/
instance canLift : CanLift (Interval α) (NonemptyInterval α) coe fun r => r ≠ ⊥ :=
  WithBot.canLift
#align interval.can_lift Interval.canLift

#print Interval.coe_injective /-
theorem coe_injective : Injective (coe : NonemptyInterval α → Interval α) :=
  WithBot.coe_injective
#align interval.coe_injective Interval.coe_injective
-/

#print Interval.coe_inj /-
@[simp, norm_cast]
theorem coe_inj {s t : NonemptyInterval α} : (s : Interval α) = t ↔ s = t :=
  WithBot.coe_inj
#align interval.coe_inj Interval.coe_inj
-/

/- warning: interval.forall -> Interval.forall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] {p : (Interval.{u1} α _inst_1) -> Prop}, Iff (forall (s : Interval.{u1} α _inst_1), p s) (And (p (Bot.bot.{u1} (Interval.{u1} α _inst_1) (OrderBot.toHasBot.{u1} (Interval.{u1} α _inst_1) (Interval.hasLe.{u1} α _inst_1) (Interval.orderBot.{u1} α _inst_1)))) (forall (s : NonemptyInterval.{u1} α _inst_1), p ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (Interval.hasCoeT.{u1} α _inst_1))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] {p : (Interval.{u1} α _inst_1) -> Prop}, Iff (forall (s : Interval.{u1} α _inst_1), p s) (And (p (Bot.bot.{u1} (Interval.{u1} α _inst_1) (WithBot.bot.{u1} (NonemptyInterval.{u1} α _inst_1)))) (forall (s : NonemptyInterval.{u1} α _inst_1), p (WithBot.some.{u1} (NonemptyInterval.{u1} α _inst_1) s)))
Case conversion may be inaccurate. Consider using '#align interval.forall Interval.forallₓ'. -/
@[protected]
theorem forall {p : Interval α → Prop} : (∀ s, p s) ↔ p ⊥ ∧ ∀ s : NonemptyInterval α, p s :=
  Option.forall
#align interval.forall Interval.forall

/- warning: interval.exists -> Interval.exists is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] {p : (Interval.{u1} α _inst_1) -> Prop}, Iff (Exists.{succ u1} (Interval.{u1} α _inst_1) (fun (s : Interval.{u1} α _inst_1) => p s)) (Or (p (Bot.bot.{u1} (Interval.{u1} α _inst_1) (OrderBot.toHasBot.{u1} (Interval.{u1} α _inst_1) (Interval.hasLe.{u1} α _inst_1) (Interval.orderBot.{u1} α _inst_1)))) (Exists.{succ u1} (NonemptyInterval.{u1} α _inst_1) (fun (s : NonemptyInterval.{u1} α _inst_1) => p ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α _inst_1) (Interval.{u1} α _inst_1) (Interval.hasCoeT.{u1} α _inst_1))) s))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LE.{u1} α] {p : (Interval.{u1} α _inst_1) -> Prop}, Iff (Exists.{succ u1} (Interval.{u1} α _inst_1) (fun (s : Interval.{u1} α _inst_1) => p s)) (Or (p (Bot.bot.{u1} (Interval.{u1} α _inst_1) (WithBot.bot.{u1} (NonemptyInterval.{u1} α _inst_1)))) (Exists.{succ u1} (NonemptyInterval.{u1} α _inst_1) (fun (s : NonemptyInterval.{u1} α _inst_1) => p (WithBot.some.{u1} (NonemptyInterval.{u1} α _inst_1) s))))
Case conversion may be inaccurate. Consider using '#align interval.exists Interval.existsₓ'. -/
@[protected]
theorem exists {p : Interval α → Prop} : (∃ s, p s) ↔ p ⊥ ∨ ∃ s : NonemptyInterval α, p s :=
  Option.exists
#align interval.exists Interval.exists

instance [IsEmpty α] : Unique (Interval α) :=
  Option.unique

#print Interval.dual /-
/-- Turn an interval into an interval in the dual order. -/
def dual : Interval α ≃ Interval αᵒᵈ :=
  NonemptyInterval.dual.optionCongr
#align interval.dual Interval.dual
-/

end LE

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ]

instance : Preorder (Interval α) :=
  WithBot.preorder

/- warning: interval.pure -> Interval.pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], α -> (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], α -> (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align interval.pure Interval.pureₓ'. -/
/-- `{a}` as an interval. -/
def pure (a : α) : Interval α :=
  NonemptyInterval.pure a
#align interval.pure Interval.pure

/- warning: interval.pure_injective -> Interval.pure_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Function.Injective.{succ u1, succ u1} α (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Function.Injective.{succ u1, succ u1} α (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align interval.pure_injective Interval.pure_injectiveₓ'. -/
theorem pure_injective : Injective (pure : α → Interval α) :=
  coe_injective.comp NonemptyInterval.pure_injective
#align interval.pure_injective Interval.pure_injective

/- warning: interval.dual_pure -> Interval.dual_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1 a)) (Interval.pure.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (fun (_x : Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) => α -> (OrderDual.{u1} α)) (Equiv.hasCoeToFun.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Interval.pure.{u1} α _inst_1 a)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (fun (_x : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1 a)) (Interval.pure.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u1} α) a) (OrderDual.preorder.{u1} α _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} α (OrderDual.{u1} α)) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : α) => OrderDual.{u1} α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} α (OrderDual.{u1} α)) (OrderDual.toDual.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align interval.dual_pure Interval.dual_pureₓ'. -/
@[simp]
theorem dual_pure (a : α) : (pure a).dual = pure (toDual a) :=
  rfl
#align interval.dual_pure Interval.dual_pure

/- warning: interval.dual_bot -> Interval.dual_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Eq.{succ u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderBot.toHasBot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.orderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1))))) (Bot.bot.{u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (OrderBot.toHasBot.{u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (Interval.hasLe.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (Interval.orderBot.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (fun (_x : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))))) (Bot.bot.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))))) (WithBot.bot.{u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align interval.dual_bot Interval.dual_botₓ'. -/
@[simp]
theorem dual_bot : (⊥ : Interval α).dual = ⊥ :=
  rfl
#align interval.dual_bot Interval.dual_bot

/- warning: interval.pure_ne_bot -> Interval.pure_ne_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Ne.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1 a) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderBot.toHasBot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.orderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Ne.{succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.pure.{u1} α _inst_1 a) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align interval.pure_ne_bot Interval.pure_ne_botₓ'. -/
@[simp]
theorem pure_ne_bot {a : α} : pure a ≠ ⊥ :=
  WithBot.coe_ne_bot
#align interval.pure_ne_bot Interval.pure_ne_bot

/- warning: interval.bot_ne_pure -> Interval.bot_ne_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Ne.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderBot.toHasBot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.orderBot.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Interval.pure.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {a : α}, Ne.{succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.pure.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align interval.bot_ne_pure Interval.bot_ne_pureₓ'. -/
@[simp]
theorem bot_ne_pure {a : α} : ⊥ ≠ pure a :=
  WithBot.bot_ne_coe
#align interval.bot_ne_pure Interval.bot_ne_pure

instance [Nonempty α] : Nontrivial (Interval α) :=
  Option.nontrivial

/- warning: interval.map -> Interval.map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β], (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) -> (Interval.{u2} β (Preorder.toLE.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align interval.map Interval.mapₓ'. -/
/-- Pushforward of intervals. -/
def map (f : α →o β) : Interval α → Interval β :=
  WithBot.map (NonemptyInterval.map f)
#align interval.map Interval.map

/- warning: interval.map_pure -> Interval.map_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (Interval.map.{u1, u2} α β _inst_1 _inst_2 f (Interval.pure.{u1} α _inst_1 a)) (Interval.pure.{u2} β _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : OrderHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : OrderHom.{u2, u1} α β _inst_1 _inst_2) (a : α), Eq.{succ u1} (Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (Interval.map.{u2, u1} α β _inst_1 _inst_2 f (Interval.pure.{u2} α _inst_1 a)) (Interval.pure.{u1} β _inst_2 (OrderHom.toFun.{u2, u1} α β _inst_1 _inst_2 f a))
Case conversion may be inaccurate. Consider using '#align interval.map_pure Interval.map_pureₓ'. -/
@[simp]
theorem map_pure (f : α →o β) (a : α) : (pure a).map f = pure (f a) :=
  rfl
#align interval.map_pure Interval.map_pure

/- warning: interval.map_map -> Interval.map_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] [_inst_3 : Preorder.{u3} γ] (g : OrderHom.{u2, u3} β γ _inst_2 _inst_3) (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (s : Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)), Eq.{succ u3} (Interval.{u3} γ (Preorder.toHasLe.{u3} γ _inst_3)) (Interval.map.{u2, u3} β γ _inst_2 _inst_3 g (Interval.map.{u1, u2} α β _inst_1 _inst_2 f s)) (Interval.map.{u1, u3} α γ _inst_1 _inst_3 (OrderHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u3} β] [_inst_3 : Preorder.{u2} γ] (g : OrderHom.{u3, u2} β γ _inst_2 _inst_3) (f : OrderHom.{u1, u3} α β _inst_1 _inst_2) (s : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)), Eq.{succ u2} (Interval.{u2} γ (Preorder.toLE.{u2} γ _inst_3)) (Interval.map.{u3, u2} β γ _inst_2 _inst_3 g (Interval.map.{u1, u3} α β _inst_1 _inst_2 f s)) (Interval.map.{u1, u2} α γ _inst_1 _inst_3 (OrderHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f) s)
Case conversion may be inaccurate. Consider using '#align interval.map_map Interval.map_mapₓ'. -/
@[simp]
theorem map_map (g : β →o γ) (f : α →o β) (s : Interval α) : (s.map f).map g = s.map (g.comp f) :=
  Option.map_map _ _ _
#align interval.map_map Interval.map_map

/- warning: interval.dual_map -> Interval.dual_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : Preorder.{u2} β] (f : OrderHom.{u1, u2} α β _inst_1 _inst_2) (s : Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)), Eq.{succ u2} (Interval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2))) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (Interval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (fun (_x : Equiv.{succ u2, succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (Interval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) => (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) -> (Interval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (Equiv.hasCoeToFun.{succ u2, succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (Interval.{u2} (OrderDual.{u2} β) (OrderDual.hasLe.{u2} β (Preorder.toHasLe.{u2} β _inst_2)))) (Interval.dual.{u2} β (Preorder.toHasLe.{u2} β _inst_2)) (Interval.map.{u1, u2} α β _inst_1 _inst_2 f s)) (Interval.map.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) => (OrderHom.{u1, u2} α β _inst_1 _inst_2) -> (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 _inst_2) (OrderHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.preorder.{u2} β _inst_2))) (OrderHom.dual.{u1, u2} α β _inst_1 _inst_2) f) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] [_inst_2 : Preorder.{u1} β] (f : OrderHom.{u2, u1} α β _inst_1 _inst_2) (s : Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)), Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => Interval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2))) (Interval.map.{u2, u1} α β _inst_1 _inst_2 f s)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (Interval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (fun (_x : Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) => Interval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Interval.{u1} β (Preorder.toLE.{u1} β _inst_2)) (Interval.{u1} (OrderDual.{u1} β) (OrderDual.instLEOrderDual.{u1} β (Preorder.toLE.{u1} β _inst_2)))) (Interval.dual.{u1} β (Preorder.toLE.{u1} β _inst_2)) (Interval.map.{u2, u1} α β _inst_1 _inst_2 f s)) (Interval.map.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2) (FunLike.coe.{max (succ u1) (succ u2), max (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u2, u1} α β _inst_1 _inst_2) (OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2))) (OrderHom.{u2, u1} α β _inst_1 _inst_2) (fun (_x : OrderHom.{u2, u1} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderHom.{u2, u1} α β _inst_1 _inst_2) => OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u2, u1} α β _inst_1 _inst_2) (OrderHom.{u2, u1} (OrderDual.{u2} α) (OrderDual.{u1} β) (OrderDual.preorder.{u2} α _inst_1) (OrderDual.preorder.{u1} β _inst_2))) (OrderHom.dual.{u2, u1} α β _inst_1 _inst_2) f) (FunLike.coe.{succ u2, succ u2, succ u2} (Equiv.{succ u2, succ u2} (Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (Interval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1)))) (Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (fun (_x : Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)) => Interval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u2} (Interval.{u2} α (Preorder.toLE.{u2} α _inst_1)) (Interval.{u2} (OrderDual.{u2} α) (OrderDual.instLEOrderDual.{u2} α (Preorder.toLE.{u2} α _inst_1)))) (Interval.dual.{u2} α (Preorder.toLE.{u2} α _inst_1)) s))
Case conversion may be inaccurate. Consider using '#align interval.dual_map Interval.dual_mapₓ'. -/
@[simp]
theorem dual_map (f : α →o β) (s : Interval α) : (s.map f).dual = s.dual.map f.dual :=
  by
  cases s
  · rfl
  · exact WithBot.map_comm rfl _
#align interval.dual_map Interval.dual_map

variable [BoundedOrder α]

instance : BoundedOrder (Interval α) :=
  WithBot.boundedOrder

/- warning: interval.dual_top -> Interval.dual_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_4 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α _inst_1)], Eq.{succ u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (fun (_x : Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) => (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) -> (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Top.top.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderTop.toHasTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.boundedOrder.{u1} α _inst_1 _inst_4))))) (Top.top.{u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (OrderTop.toHasTop.{u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (Interval.hasLe.{u1} (OrderDual.{u1} α) (Preorder.toHasLe.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (BoundedOrder.toOrderTop.{u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1))) (Interval.hasLe.{u1} (OrderDual.{u1} α) (Preorder.toHasLe.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1))) (Interval.boundedOrder.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.boundedOrder.{u1} α (Preorder.toHasLe.{u1} α _inst_1) _inst_4)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_4 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_4))))) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (fun (_x : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1)))) (Interval.dual.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Top.top.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_4))))) (Top.top.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_4))))) (OrderTop.toTop.{u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Top.top.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_4))))) (Interval.instLEInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (NonemptyInterval.le.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α _inst_1))) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} (OrderDual.{u1} α) (OrderDual.preorder.{u1} α _inst_1) (OrderDual.boundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1) _inst_4)))))
Case conversion may be inaccurate. Consider using '#align interval.dual_top Interval.dual_topₓ'. -/
@[simp]
theorem dual_top : (⊤ : Interval α).dual = ⊤ :=
  rfl
#align interval.dual_top Interval.dual_top

end Preorder

section PartialOrder

variable [PartialOrder α] [PartialOrder β] {s t : Interval α} {a b : α}

instance : PartialOrder (Interval α) :=
  WithBot.partialOrder

/- warning: interval.coe_hom -> Interval.coeHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], OrderEmbedding.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.hasLe.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], OrderEmbedding.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.instLESet.{u1} α)
Case conversion may be inaccurate. Consider using '#align interval.coe_hom Interval.coeHomₓ'. -/
/-- Consider a interval `[a, b]` as the set `[a, b]`. -/
def coeHom : Interval α ↪o Set α :=
  OrderEmbedding.ofMapLEIff
    (fun s =>
      match s with
      | ⊥ => ∅
      | some s => s)
    fun s t =>
    match s, t with
    | ⊥, t => iff_of_true bot_le bot_le
    | some s, ⊥ =>
      iff_of_false (fun h => s.coe_nonempty.ne_empty <| le_bot_iff.1 h) (WithBot.not_coe_le_bot _)
    | some s, some t => (@NonemptyInterval.coeHom α _).le_iff_le.trans WithBot.some_le_some.symm
#align interval.coe_hom Interval.coeHom

instance : SetLike (Interval α) α where
  coe := coeHom
  coe_injective' := coeHom.Injective

/- warning: interval.coe_subset_coe -> Interval.coe_subset_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) t)) (LE.le.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) t)) (LE.le.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
Case conversion may be inaccurate. Consider using '#align interval.coe_subset_coe Interval.coe_subset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_subset_coe : (s : Set α) ⊆ t ↔ s ≤ t :=
  (@coeHom α _).le_iff_le
#align interval.coe_subset_coe Interval.coe_subset_coe

/- warning: interval.coe_ssubset_coe -> Interval.coe_sSubset_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) t)) (LT.lt.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Preorder.toHasLt.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.preorder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {t : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) s) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) t)) (LT.lt.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Preorder.toLT.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.instPreorderIntervalToLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s t)
Case conversion may be inaccurate. Consider using '#align interval.coe_ssubset_coe Interval.coe_sSubset_coeₓ'. -/
@[simp, norm_cast]
theorem coe_sSubset_coe : (s : Set α) ⊂ t ↔ s < t :=
  (@coeHom α _).lt_iff_lt
#align interval.coe_ssubset_coe Interval.coe_sSubset_coe

#print Interval.coe_pure /-
@[simp, norm_cast]
theorem coe_pure (a : α) : (pure a : Set α) = {a} :=
  Icc_self _
#align interval.coe_pure Interval.coe_pure
-/

/- warning: interval.coe_coe -> Interval.coe_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) s)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (NonemptyInterval.Set.hasCoeT.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) α (Interval.setLike.{u1} α _inst_1) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (SetLike.coe.{u1, u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (NonemptyInterval.setLike.{u1} α _inst_1) s)
Case conversion may be inaccurate. Consider using '#align interval.coe_coe Interval.coe_coeₓ'. -/
@[simp, norm_cast]
theorem coe_coe (s : NonemptyInterval α) : ((s : Interval α) : Set α) = s :=
  rfl
#align interval.coe_coe Interval.coe_coe

/- warning: interval.coe_bot -> Interval.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (OrderBot.toHasBot.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) (Bot.bot.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (WithBot.bot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align interval.coe_bot Interval.coe_botₓ'. -/
@[simp, norm_cast]
theorem coe_bot : ((⊥ : Interval α) : Set α) = ∅ :=
  rfl
#align interval.coe_bot Interval.coe_bot

/- warning: interval.coe_top -> Interval.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) (Top.top.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (OrderTop.toHasTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (BoundedOrder.toOrderTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.boundedOrder.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3))))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] [_inst_3 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))], Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) (Top.top.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (OrderTop.toTop.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1) _inst_3))))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align interval.coe_top Interval.coe_topₓ'. -/
@[simp, norm_cast]
theorem coe_top [BoundedOrder α] : ((⊤ : Interval α) : Set α) = univ :=
  Icc_bot_top
#align interval.coe_top Interval.coe_top

/- warning: interval.coe_dual -> Interval.coe_dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} (OrderDual.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (Set.{u1} (OrderDual.{u1} α)) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (OrderDual.{u1} α) (Interval.setLike.{u1} (OrderDual.{u1} α) (OrderDual.partialOrder.{u1} α _inst_1))))) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (fun (_x : Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) => (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) -> (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (Equiv.hasCoeToFun.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.hasLe.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (Interval.dual.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (Set.preimage.{u1, u1} (OrderDual.{u1} α) α (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (fun (_x : Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) => (OrderDual.{u1} α) -> α) (Equiv.hasCoeToFun.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] (s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), Eq.{succ u1} (Set.{u1} (OrderDual.{u1} α)) (SetLike.coe.{u1, u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) s) (OrderDual.{u1} α) (Interval.setLike.{u1} (OrderDual.{u1} α) (OrderDual.partialOrder.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (fun (_x : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) => Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} (OrderDual.{u1} α) (OrderDual.instLEOrderDual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) (Interval.dual.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (Set.preimage.{u1, u1} (OrderDual.{u1} α) α (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.{u1} α) (fun (_x : OrderDual.{u1} α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : OrderDual.{u1} α) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} α) α) (OrderDual.ofDual.{u1} α)) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align interval.coe_dual Interval.coe_dualₓ'. -/
@[simp, norm_cast]
theorem coe_dual (s : Interval α) : (s.dual : Set αᵒᵈ) = ofDual ⁻¹' s :=
  by
  cases s
  · rfl
  exact s.coe_dual
#align interval.coe_dual Interval.coe_dual

/- warning: interval.subset_coe_map -> Interval.subset_coe_map is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : PartialOrder.{u1} α] [_inst_2 : PartialOrder.{u2} β] (f : OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) (fun (_x : OrderHom.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2)) f) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)))) s)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Interval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (HasLiftT.mk.{succ u2, succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (CoeTCₓ.coe.{succ u2, succ u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) (Set.{u2} β) (SetLike.Set.hasCoeT.{u2, u2} (Interval.{u2} β (Preorder.toHasLe.{u2} β (PartialOrder.toPreorder.{u2} β _inst_2))) β (Interval.setLike.{u2} β _inst_2)))) (Interval.map.{u1, u2} α β (PartialOrder.toPreorder.{u1} α _inst_1) (PartialOrder.toPreorder.{u2} β _inst_2) f s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : PartialOrder.{u2} α] [_inst_2 : PartialOrder.{u1} β] (f : OrderHom.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2)) (s : Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (Set.image.{u2, u1} α β (OrderHom.toFun.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) f) (SetLike.coe.{u2, u2} (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α _inst_1))) α (Interval.setLike.{u2} α _inst_1) s)) (SetLike.coe.{u1, u1} (Interval.{u1} β (Preorder.toLE.{u1} β (PartialOrder.toPreorder.{u1} β _inst_2))) β (Interval.setLike.{u1} β _inst_2) (Interval.map.{u2, u1} α β (PartialOrder.toPreorder.{u2} α _inst_1) (PartialOrder.toPreorder.{u1} β _inst_2) f s))
Case conversion may be inaccurate. Consider using '#align interval.subset_coe_map Interval.subset_coe_mapₓ'. -/
theorem subset_coe_map (f : α →o β) : ∀ s : Interval α, f '' s ⊆ s.map f
  | ⊥ => by simp
  | (s : NonemptyInterval α) => s.subset_coe_map _
#align interval.subset_coe_map Interval.subset_coe_map

#print Interval.mem_pure /-
@[simp]
theorem mem_pure : b ∈ pure a ↔ b = a := by rw [← SetLike.mem_coe, coe_pure, mem_singleton_iff]
#align interval.mem_pure Interval.mem_pure
-/

#print Interval.mem_pure_self /-
theorem mem_pure_self (a : α) : a ∈ pure a :=
  mem_pure.2 rfl
#align interval.mem_pure_self Interval.mem_pure_self
-/

end PartialOrder

section Lattice

variable [Lattice α]

instance : SemilatticeSup (Interval α) :=
  WithBot.semilatticeSup

section Decidable

variable [@DecidableRel α (· ≤ ·)]

instance : Lattice (Interval α) :=
  {
    Interval.semilatticeSup with
    inf := fun s t =>
      match s, t with
      | ⊥, t => ⊥
      | s, ⊥ => ⊥
      | some s, some t =>
        if h : s.fst ≤ t.snd ∧ t.fst ≤ s.snd then
          some
            ⟨⟨s.fst ⊔ t.fst, s.snd ⊓ t.snd⟩,
              sup_le (le_inf s.fst_le_snd h.1) <| le_inf h.2 t.fst_le_snd⟩
        else ⊥
    inf_le_left := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_left, inf_le_left⟩
        · exact bot_le
    inf_le_right := fun s t =>
      match s, t with
      | ⊥, ⊥ => bot_le
      | ⊥, some t => bot_le
      | some s, ⊥ => bot_le
      | some s, some t => by
        change dite _ _ _ ≤ _
        split_ifs
        · exact WithBot.some_le_some.2 ⟨le_sup_right, inf_le_right⟩
        · exact bot_le
    le_inf := fun s t c =>
      match s, t, c with
      | ⊥, t, c => fun _ _ => bot_le
      | some s, t, c => fun hb hc =>
        by
        lift t to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hb
        lift c to NonemptyInterval α using ne_bot_of_le_ne_bot WithBot.coe_ne_bot hc
        change _ ≤ dite _ _ _
        simp only [WithBot.some_eq_coe, WithBot.coe_le_coe] at hb hc⊢
        rw [dif_pos, WithBot.coe_le_coe]
        exact ⟨sup_le hb.1 hc.1, le_inf hb.2 hc.2⟩
        exact ⟨hb.1.trans <| s.fst_le_snd.trans hc.2, hc.1.trans <| s.fst_le_snd.trans hb.2⟩ }

/- warning: interval.coe_inf -> Interval.coe_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))] (s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) (Inf.inf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (SemilatticeInf.toHasInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Lattice.toSemilatticeInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.lattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b)))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Order.Interval._hyg.4979 : α) (x._@.Mathlib.Order.Interval._hyg.4981 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Interval._hyg.4979 x._@.Mathlib.Order.Interval._hyg.4981)] (s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (Inf.inf.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Lattice.toInf.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.lattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) s) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) t))
Case conversion may be inaccurate. Consider using '#align interval.coe_inf Interval.coe_infₓ'. -/
@[simp, norm_cast]
theorem coe_inf (s t : Interval α) : (↑(s ⊓ t) : Set α) = s ∩ t :=
  by
  cases s
  · rw [WithBot.none_eq_bot, bot_inf_eq]
    exact (empty_inter _).symm
  cases t
  · rw [WithBot.none_eq_bot, inf_bot_eq]
    exact (inter_empty _).symm
  refine' (_ : coe (dite _ _ _) = _).trans Icc_inter_Icc.symm
  split_ifs
  · rfl
  ·
    exact
      (Icc_eq_empty fun H =>
          h
            ⟨le_sup_left.trans <| H.trans inf_le_right,
              le_sup_right.trans <| H.trans inf_le_left⟩).symm
#align interval.coe_inf Interval.coe_inf

end Decidable

/- warning: interval.disjoint_coe -> Interval.disjoint_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) t)) (Disjoint.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.partialOrder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (Interval.orderBot.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) s t)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Iff (Disjoint.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) s) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) t)) (Disjoint.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.partialOrder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))) (Interval.instOrderBotIntervalInstLEInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) s t)
Case conversion may be inaccurate. Consider using '#align interval.disjoint_coe Interval.disjoint_coeₓ'. -/
@[simp, norm_cast]
theorem disjoint_coe (s t : Interval α) : Disjoint (s : Set α) t ↔ Disjoint s t := by
  classical
    rw [disjoint_iff_inf_le, disjoint_iff_inf_le, le_eq_subset, ← coe_subset_coe, coe_inf]
    rfl
#align interval.disjoint_coe Interval.disjoint_coe

end Lattice

end Interval

namespace NonemptyInterval

section Preorder

variable [Preorder α] {s : NonemptyInterval α} {a : α}

/- warning: nonempty_interval.coe_pure_interval -> NonemptyInterval.coe_pure_interval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (NonemptyInterval.pure.{u1} α _inst_1 a)) (Interval.pure.{u1} α _inst_1 a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] (a : α), Eq.{succ u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.pure.{u1} α _inst_1 a)) (Interval.pure.{u1} α _inst_1 a)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_pure_interval NonemptyInterval.coe_pure_intervalₓ'. -/
@[simp, norm_cast]
theorem coe_pure_interval (a : α) : (pure a : Interval α) = Interval.pure a :=
  rfl
#align nonempty_interval.coe_pure_interval NonemptyInterval.coe_pure_interval

/- warning: nonempty_interval.coe_eq_pure -> NonemptyInterval.coe_eq_pure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)} {a : α}, Iff (Eq.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) s) (Interval.pure.{u1} α _inst_1 a)) (Eq.{succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) s (NonemptyInterval.pure.{u1} α _inst_1 a))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)} {a : α}, Iff (Eq.{succ u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) s) (Interval.pure.{u1} α _inst_1 a)) (Eq.{succ u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) s (NonemptyInterval.pure.{u1} α _inst_1 a))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_eq_pure NonemptyInterval.coe_eq_pureₓ'. -/
@[simp, norm_cast]
theorem coe_eq_pure : (s : Interval α) = Interval.pure a ↔ s = pure a := by
  rw [← Interval.coe_inj, coe_pure_interval]
#align nonempty_interval.coe_eq_pure NonemptyInterval.coe_eq_pure

/- warning: nonempty_interval.coe_top_interval -> NonemptyInterval.coe_top_interval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toHasLe.{u1} α _inst_1)], Eq.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α _inst_1)))) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderTop.toHasTop.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (NonemptyInterval.orderTop.{u1} α _inst_1 _inst_2)))) (Top.top.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (OrderTop.toHasTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (BoundedOrder.toOrderTop.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.hasLe.{u1} α (Preorder.toHasLe.{u1} α _inst_1)) (Interval.boundedOrder.{u1} α _inst_1 _inst_2))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Preorder.{u1} α] [_inst_2 : BoundedOrder.{u1} α (Preorder.toLE.{u1} α _inst_1)], Eq.{succ u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (Top.top.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (OrderTop.toTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_2)))) (Top.top.{u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))) (OrderTop.toTop.{u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1))) (Interval.instLEInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (WithBot.orderTop.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.le.{u1} α (Preorder.toLE.{u1} α _inst_1)) (NonemptyInterval.instOrderTopNonemptyIntervalToLELe.{u1} α _inst_1 _inst_2))))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_top_interval NonemptyInterval.coe_top_intervalₓ'. -/
@[simp, norm_cast]
theorem coe_top_interval [BoundedOrder α] : ((⊤ : NonemptyInterval α) : Interval α) = ⊤ :=
  rfl
#align nonempty_interval.coe_top_interval NonemptyInterval.coe_top_interval

end Preorder

/- warning: nonempty_interval.mem_coe_interval -> NonemptyInterval.mem_coe_interval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {x : α}, Iff (Membership.Mem.{u1, u1} α (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (SetLike.hasMem.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) α (Interval.setLike.{u1} α _inst_1)) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))))) s)) (Membership.Mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.hasMem.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : PartialOrder.{u1} α] {s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))} {x : α}, Iff (Membership.mem.{u1, u1} α (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) (SetLike.instMembership.{u1, u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)))) α (Interval.setLike.{u1} α _inst_1)) x (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) s)) (Membership.mem.{u1, u1} α (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1))) (NonemptyInterval.instMembershipNonemptyIntervalToLE.{u1} α (PartialOrder.toPreorder.{u1} α _inst_1)) x s)
Case conversion may be inaccurate. Consider using '#align nonempty_interval.mem_coe_interval NonemptyInterval.mem_coe_intervalₓ'. -/
@[simp, norm_cast]
theorem mem_coe_interval [PartialOrder α] {s : NonemptyInterval α} {x : α} :
    x ∈ (s : Interval α) ↔ x ∈ s :=
  Iff.rfl
#align nonempty_interval.mem_coe_interval NonemptyInterval.mem_coe_interval

/- warning: nonempty_interval.coe_sup_interval -> NonemptyInterval.coe_sup_interval is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.hasSup.{u1} α _inst_1) s t)) (Sup.sup.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (SemilatticeSup.toHasSup.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.semilatticeSup.{u1} α _inst_1)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))))) s) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (HasLiftT.mk.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (CoeTCₓ.coe.{succ u1, succ u1} (NonemptyInterval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Interval.hasCoeT.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))))) t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Lattice.{u1} α] (s : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (t : NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))), Eq.{succ u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (Sup.sup.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) (NonemptyInterval.instSupNonemptyIntervalToLEToPreorderToPartialOrderToSemilatticeInf.{u1} α _inst_1) s t)) (Sup.sup.{u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) (SemilatticeSup.toSup.{u1} (WithBot.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1)))))) (Interval.semilatticeSup.{u1} α _inst_1)) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) s) (WithBot.some.{u1} (NonemptyInterval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α (Lattice.toSemilatticeInf.{u1} α _inst_1))))) t))
Case conversion may be inaccurate. Consider using '#align nonempty_interval.coe_sup_interval NonemptyInterval.coe_sup_intervalₓ'. -/
@[simp, norm_cast]
theorem coe_sup_interval [Lattice α] (s t : NonemptyInterval α) : (↑(s ⊔ t) : Interval α) = s ⊔ t :=
  rfl
#align nonempty_interval.coe_sup_interval NonemptyInterval.coe_sup_interval

end NonemptyInterval

namespace Interval

section CompleteLattice

variable [CompleteLattice α]

noncomputable instance [@DecidableRel α (· ≤ ·)] : CompleteLattice (Interval α) := by
  classical exact
      { Interval.lattice,
        Interval.boundedOrder with
        sSup := fun S =>
          if h : S ⊆ {⊥} then ⊥
          else
            some
              ⟨⟨⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst,
                  ⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩,
                by
                obtain ⟨s, hs, ha⟩ := not_subset.1 h
                lift s to NonemptyInterval α using ha
                exact iInf₂_le_of_le s hs (le_iSup₂_of_le s hs s.fst_le_snd)⟩
        le_sup := fun s s ha => by
          split_ifs
          · exact (h ha).le
          cases s
          · exact bot_le
          · exact WithBot.some_le_some.2 ⟨iInf₂_le _ ha, le_iSup₂_of_le _ ha le_rfl⟩
        sup_le := fun s s ha => by
          split_ifs
          · exact bot_le
          obtain ⟨b, hs, hb⟩ := not_subset.1 h
          lift s to NonemptyInterval α using ne_bot_of_le_ne_bot hb (ha _ hs)
          exact
            WithBot.coe_le_coe.2
              ⟨le_iInf₂ fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).1,
                iSup₂_le fun c hc => (WithBot.coe_le_coe.1 <| ha _ hc).2⟩
        sInf := fun S =>
          if h :
              ⊥ ∉ S ∧
                ∀ ⦃s : NonemptyInterval α⦄,
                  ↑s ∈ S → ∀ ⦃t : NonemptyInterval α⦄, ↑t ∈ S → s.fst ≤ t.snd then
            some
              ⟨⟨⨆ (s : NonemptyInterval α) (h : ↑s ∈ S), s.fst,
                  ⨅ (s : NonemptyInterval α) (h : ↑s ∈ S), s.snd⟩,
                iSup₂_le fun s hs => le_iInf₂ <| h.2 hs⟩
          else ⊥
        inf_le := fun s s ha => by
          split_ifs
          · lift s to NonemptyInterval α using ne_of_mem_of_not_mem ha h.1
            exact WithBot.coe_le_coe.2 ⟨le_iSup₂ s ha, iInf₂_le s ha⟩
          · exact bot_le
        le_inf := fun S s ha => by
          cases s
          · exact bot_le
          split_ifs
          ·
            exact
              WithBot.some_le_some.2
                ⟨iSup₂_le fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).1,
                  le_iInf₂ fun t hb => (WithBot.coe_le_coe.1 <| ha _ hb).2⟩
          rw [not_and_or, Classical.not_not] at h
          cases h
          · exact ha _ h
          cases
            h fun t hb c hc =>
              (WithBot.coe_le_coe.1 <| ha _ hb).1.trans <|
                s.fst_le_snd.trans (WithBot.coe_le_coe.1 <| ha _ hc).2 }

/- warning: interval.coe_Inf -> Interval.coe_sInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))] (S : Set.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (InfSet.sInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Interval.completeLattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b)))) S)) (Set.iInter.{u1, succ u1} α (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (fun (s : Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) => Set.iInter.{u1, 0} α (Membership.Mem.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (Set.hasMem.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) s S) (fun (H : Membership.Mem.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (Set.hasMem.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) s S) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) s)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (fun (x._@.Mathlib.Order.Interval._hyg.6312 : α) (x._@.Mathlib.Order.Interval._hyg.6314 : α) => LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))) x._@.Mathlib.Order.Interval._hyg.6312 x._@.Mathlib.Order.Interval._hyg.6314)] (S : Set.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))), Eq.{succ u1} (Set.{u1} α) (SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (InfSet.sInf.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteLattice.toInfSet.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Interval.completeLattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) S)) (Set.iInter.{u1, succ u1} α (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (fun (s : Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) => Set.iInter.{u1, 0} α (Membership.mem.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (Set.instMembershipSet.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) s S) (fun (H : Membership.mem.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (Set.instMembershipSet.{u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) s S) => SetLike.coe.{u1, u1} (Interval.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) s)))
Case conversion may be inaccurate. Consider using '#align interval.coe_Inf Interval.coe_sInfₓ'. -/
@[simp, norm_cast]
theorem coe_sInf [@DecidableRel α (· ≤ ·)] (S : Set (Interval α)) :
    ↑(sInf S) = ⋂ s ∈ S, (s : Set α) :=
  by
  change coe (dite _ _ _) = _
  split_ifs
  · ext
    simp [WithBot.some_eq_coe, Interval.forall, h.1, ← forall_and, ← NonemptyInterval.mem_def]
  simp_rw [not_and_or, Classical.not_not] at h
  cases h
  · refine' (eq_empty_of_subset_empty _).symm
    exact Inter₂_subset_of_subset _ h subset.rfl
  · refine' (not_nonempty_iff_eq_empty.1 _).symm
    rintro ⟨x, hx⟩
    rw [mem_Inter₂] at hx
    exact h fun s ha t hb => (hx _ ha).1.trans (hx _ hb).2
#align interval.coe_Inf Interval.coe_sInf

/- warning: interval.coe_infi -> Interval.coe_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))] (f : ι -> (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (iInf.{u1, u2} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Interval.completeLattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b)))) ι (fun (i : ι) => f i))) (Set.iInter.{u1, u2} α ι (fun (i : ι) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (f i)))
but is expected to have type
  forall {α : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : DecidableRel.{succ u2} α (fun (x._@.Mathlib.Order.Interval._hyg.6540 : α) (x._@.Mathlib.Order.Interval._hyg.6542 : α) => LE.le.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) x._@.Mathlib.Order.Interval._hyg.6540 x._@.Mathlib.Order.Interval._hyg.6542)] (f : ι -> (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))))), Eq.{succ u2} (Set.{u2} α) (SetLike.coe.{u2, u2} (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) α (Interval.setLike.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (iInf.{u2, u1} (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) (CompleteLattice.toInfSet.{u2} (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) (Interval.completeLattice.{u2} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) ι (fun (i : ι) => f i))) (Set.iInter.{u2, u1} α ι (fun (i : ι) => SetLike.coe.{u2, u2} (Interval.{u2} α (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))))) α (Interval.setLike.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1))) (f i)))
Case conversion may be inaccurate. Consider using '#align interval.coe_infi Interval.coe_iInfₓ'. -/
@[simp, norm_cast]
theorem coe_iInf [@DecidableRel α (· ≤ ·)] (f : ι → Interval α) :
    ↑(⨅ i, f i) = ⋂ i, (f i : Set α) := by simp [iInf]
#align interval.coe_infi Interval.coe_iInf

/- warning: interval.coe_infi₂ -> Interval.coe_iInf₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {ι : Sort.{u2}} {κ : ι -> Sort.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : DecidableRel.{succ u1} α (LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))] (f : forall (i : ι), (κ i) -> (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))), Eq.{succ u1} (Set.{u1} α) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (iInf.{u1, u2} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Interval.completeLattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b)))) ι (fun (i : ι) => iInf.{u1, u3} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteSemilatticeInf.toHasInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Interval.completeLattice.{u1} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b)))) (κ i) (fun (j : κ i) => f i j)))) (Set.iInter.{u1, u2} α ι (fun (i : ι) => Set.iInter.{u1, u3} α (κ i) (fun (j : κ i) => (fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (HasLiftT.mk.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (CoeTCₓ.coe.{succ u1, succ u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) (Set.{u1} α) (SetLike.Set.hasCoeT.{u1, u1} (Interval.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))))) α (Interval.setLike.{u1} α (CompleteSemilatticeInf.toPartialOrder.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)))))) (f i j))))
but is expected to have type
  forall {α : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : CompleteLattice.{u3} α] [_inst_2 : DecidableRel.{succ u3} α (fun (x._@.Mathlib.Order.Interval._hyg.6625 : α) (x._@.Mathlib.Order.Interval._hyg.6627 : α) => LE.le.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))) x._@.Mathlib.Order.Interval._hyg.6625 x._@.Mathlib.Order.Interval._hyg.6627)] (f : forall (i : ι), (κ i) -> (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1)))))), Eq.{succ u3} (Set.{u3} α) (SetLike.coe.{u3, u3} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) α (Interval.setLike.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (iInf.{u3, u2} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) (CompleteLattice.toInfSet.{u3} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) (Interval.completeLattice.{u3} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) ι (fun (i : ι) => iInf.{u3, u1} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) (CompleteLattice.toInfSet.{u3} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) (Interval.completeLattice.{u3} α _inst_1 (fun (a : α) (b : α) => _inst_2 a b))) (κ i) (fun (j : κ i) => f i j)))) (Set.iInter.{u3, u2} α ι (fun (i : ι) => Set.iInter.{u3, u1} α (κ i) (fun (j : κ i) => SetLike.coe.{u3, u3} (Interval.{u3} α (Preorder.toLE.{u3} α (PartialOrder.toPreorder.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))))) α (Interval.setLike.{u3} α (CompleteSemilatticeInf.toPartialOrder.{u3} α (CompleteLattice.toCompleteSemilatticeInf.{u3} α _inst_1))) (f i j))))
Case conversion may be inaccurate. Consider using '#align interval.coe_infi₂ Interval.coe_iInf₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp, norm_cast]
theorem coe_iInf₂ [@DecidableRel α (· ≤ ·)] (f : ∀ i, κ i → Interval α) :
    ↑(⨅ (i) (j), f i j) = ⋂ (i) (j), (f i j : Set α) := by simp_rw [coe_infi]
#align interval.coe_infi₂ Interval.coe_iInf₂

end CompleteLattice

end Interval

