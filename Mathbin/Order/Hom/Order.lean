/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen

! This file was ported from Lean 3 source module order.hom.order
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Function.Iterate
import Mathbin.Order.GaloisConnection
import Mathbin.Order.Hom.Basic

/-!
# Lattice structure on order homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lattice structure on order homomorphisms, which are bundled
monotone functions.

## Main definitions

 * `order_hom.complete_lattice`: if `β` is a complete lattice, so is `α →o β`

## Tags

monotone map, bundled morphism
-/


namespace OrderHom

variable {α β : Type _}

section Preorder

variable [Preorder α]

@[simps]
instance [SemilatticeSup β] : Sup (α →o β) where sup f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrder (α →o β)) with
    sup := Sup.sup
    le_sup_left := fun a b x => le_sup_left
    le_sup_right := fun a b x => le_sup_right
    sup_le := fun a b c h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

@[simps]
instance [SemilatticeInf β] : Inf (α →o β) where inf f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

instance [SemilatticeInf β] : SemilatticeInf (α →o β) :=
  { (_ : PartialOrder (α →o β)), (dualIso α β).symm.toGaloisInsertion.liftSemilatticeInf with
    inf := (· ⊓ ·) }

instance [Lattice β] : Lattice (α →o β) :=
  { (_ : SemilatticeSup (α →o β)), (_ : SemilatticeInf (α →o β)) with }

@[simps]
instance [Preorder β] [OrderBot β] : Bot (α →o β) where bot := const α ⊥

instance [Preorder β] [OrderBot β] : OrderBot (α →o β)
    where
  bot := ⊥
  bot_le a x := bot_le

@[simps]
instance [Preorder β] [OrderTop β] : Top (α →o β) where top := const α ⊤

instance [Preorder β] [OrderTop β] : OrderTop (α →o β)
    where
  top := ⊤
  le_top a x := le_top

instance [CompleteLattice β] : InfSet (α →o β)
    where sInf s := ⟨fun x => ⨅ f ∈ s, (f : _) x, fun x y h => iInf₂_mono fun f _ => f.mono h⟩

/- warning: order_hom.Inf_apply -> OrderHom.sInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (InfSet.sInf.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) s) x) (iInf.{u2, succ (max u1 u2)} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => iInf.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfSet.sInf.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) s) x) (iInf.{u2, succ (max u1 u2)} β (CompleteLattice.toInfSet.{u2} β _inst_2) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => iInf.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f x)))
Case conversion may be inaccurate. Consider using '#align order_hom.Inf_apply OrderHom.sInf_applyₓ'. -/
@[simp]
theorem sInf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : sInf s x = ⨅ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Inf_apply OrderHom.sInf_apply

/- warning: order_hom.infi_apply -> OrderHom.iInf_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (iInf.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (iInf.{u2, u3} β (CompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i) x))
Case conversion may be inaccurate. Consider using '#align order_hom.infi_apply OrderHom.iInf_applyₓ'. -/
theorem iInf_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (sInf_apply _ _).trans iInf_range
#align order_hom.infi_apply OrderHom.iInf_apply

/- warning: order_hom.coe_infi -> OrderHom.coe_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (iInf.{max u1 u2, u3} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} (α -> β) (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (iInf.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (iInf.{max u1 u2, u3} (α -> β) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toInfSet.{u2} β _inst_2)) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i)))
Case conversion may be inaccurate. Consider using '#align order_hom.coe_infi OrderHom.coe_iInfₓ'. -/
@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
  funext fun x => (iInf_apply f x).trans (@iInf_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_infi OrderHom.coe_iInf

instance [CompleteLattice β] : SupSet (α →o β)
    where sSup s := ⟨fun x => ⨆ f ∈ s, (f : _) x, fun x y h => iSup₂_mono fun f _ => f.mono h⟩

/- warning: order_hom.Sup_apply -> OrderHom.sSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (SupSet.sSup.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) s) x) (iSup.{u2, succ (max u1 u2)} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => iSup.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (SupSet.sSup.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) s) x) (iSup.{u2, succ (max u1 u2)} β (CompleteLattice.toSupSet.{u2} β _inst_2) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => iSup.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f x)))
Case conversion may be inaccurate. Consider using '#align order_hom.Sup_apply OrderHom.sSup_applyₓ'. -/
@[simp]
theorem sSup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : sSup s x = ⨆ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Sup_apply OrderHom.sSup_apply

/- warning: order_hom.supr_apply -> OrderHom.iSup_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (iSup.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (iSup.{u2, u3} β (CompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i) x))
Case conversion may be inaccurate. Consider using '#align order_hom.supr_apply OrderHom.iSup_applyₓ'. -/
theorem iSup_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (sSup_apply _ _).trans iSup_range
#align order_hom.supr_apply OrderHom.iSup_apply

/- warning: order_hom.coe_supr -> OrderHom.coe_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (iSup.{max u1 u2, u3} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} (α -> β) (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (iSup.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (iSup.{max u1 u2, u3} (α -> β) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toSupSet.{u2} β _inst_2)) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i)))
Case conversion may be inaccurate. Consider using '#align order_hom.coe_supr OrderHom.coe_iSupₓ'. -/
@[simp, norm_cast]
theorem coe_iSup {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
  funext fun x => (iSup_apply f x).trans (@iSup_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_supr OrderHom.coe_iSup

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop,
    OrderHom.orderBot with
    sSup := sSup
    le_sup := fun s f hf x => le_iSup_of_le f (le_iSup _ hf)
    sup_le := fun s f hf x => iSup₂_le fun g hg => hf g hg x
    sInf := sInf
    le_inf := fun s f hf x => le_iInf₂ fun g hg => hf g hg x
    inf_le := fun s f hf x => iInf_le_of_le f (iInf_le _ hf) }

/- warning: order_hom.iterate_sup_le_sup_iff -> OrderHom.iterate_sup_le_sup_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_2 : SemilatticeSup.{u1} α] (f : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))), Iff (forall (n₁ : Nat) (n₂ : Nat) (a₁ : α) (a₂ : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (fun (_x : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) => α -> α) (OrderHom.hasCoeToFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) f) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n₁ n₂) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a₁ a₂)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) (Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (fun (_x : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) => α -> α) (OrderHom.hasCoeToFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) f) n₁ a₁) (Nat.iterate.{succ u1} α (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (fun (_x : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) => α -> α) (OrderHom.hasCoeToFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) f) n₂ a₂))) (forall (a₁ : α) (a₂ : α), LE.le.{u1} α (Preorder.toHasLe.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (fun (_x : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) => α -> α) (OrderHom.hasCoeToFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) f (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) a₁ a₂)) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_2) (coeFn.{succ u1, succ u1} (OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (fun (_x : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) => α -> α) (OrderHom.hasCoeToFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) f a₁) a₂))
but is expected to have type
  forall {α : Type.{u1}} [_inst_2 : SemilatticeSup.{u1} α] (f : OrderHom.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))), Iff (forall (n₁ : Nat) (n₂ : Nat) (a₁ : α) (a₂ : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (Nat.iterate.{succ u1} α (OrderHom.toFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) f) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n₁ n₂) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a₁ a₂)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) (Nat.iterate.{succ u1} α (OrderHom.toFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) f) n₁ a₁) (Nat.iterate.{succ u1} α (OrderHom.toFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) f) n₂ a₂))) (forall (a₁ : α) (a₂ : α), LE.le.{u1} α (Preorder.toLE.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2))) (OrderHom.toFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) f (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) a₁ a₂)) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α _inst_2) (OrderHom.toFun.{u1, u1} α α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_2)) f a₁) a₂))
Case conversion may be inaccurate. Consider using '#align order_hom.iterate_sup_le_sup_iff OrderHom.iterate_sup_le_sup_iffₓ'. -/
theorem iterate_sup_le_sup_iff {α : Type _} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, (f^[n₁ + n₂]) (a₁ ⊔ a₂) ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂) ↔
      ∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ f a₁ ⊔ a₂ :=
  by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂
    have h' : ∀ n a₁ a₂, (f^[n]) (a₁ ⊔ a₂) ≤ (f^[n]) a₁ ⊔ a₂ :=
      by
      intro n
      induction' n with n ih <;> intro a₁ a₂
      · rfl
      ·
        calc
          (f^[n + 1]) (a₁ ⊔ a₂) = (f^[n]) (f (a₁ ⊔ a₂)) := Function.iterate_succ_apply f n _
          _ ≤ (f^[n]) (f a₁ ⊔ a₂) := (f.mono.iterate n (h a₁ a₂))
          _ ≤ (f^[n]) (f a₁) ⊔ a₂ := (ih _ _)
          _ = (f^[n + 1]) a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]
          
    calc
      (f^[n₁ + n₂]) (a₁ ⊔ a₂) = (f^[n₁]) ((f^[n₂]) (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = (f^[n₁]) ((f^[n₂]) (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ ≤ (f^[n₁]) ((f^[n₂]) a₂ ⊔ a₁) := (f.mono.iterate n₁ (h' n₂ _ _))
      _ = (f^[n₁]) (a₁ ⊔ (f^[n₂]) a₂) := by rw [sup_comm]
      _ ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂ := h' n₁ a₁ _
      
#align order_hom.iterate_sup_le_sup_iff OrderHom.iterate_sup_le_sup_iff

end Preorder

end OrderHom

