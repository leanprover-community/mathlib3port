/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Anne Baanen

! This file was ported from Lean 3 source module order.hom.order
! leanprover-community/mathlib commit dd71334db81d0bd444af1ee339a29298bef40734
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
instance [SemilatticeSup β] : HasSup (α →o β)
    where sup f g := ⟨fun a => f a ⊔ g a, f.mono.sup g.mono⟩

instance [SemilatticeSup β] : SemilatticeSup (α →o β) :=
  { (_ : PartialOrder (α →o β)) with
    sup := HasSup.sup
    le_sup_left := fun a b x => le_sup_left
    le_sup_right := fun a b x => le_sup_right
    sup_le := fun a b c h₀ h₁ x => sup_le (h₀ x) (h₁ x) }

@[simps]
instance [SemilatticeInf β] : HasInf (α →o β)
    where inf f g := ⟨fun a => f a ⊓ g a, f.mono.inf g.mono⟩

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
    where inf s := ⟨fun x => ⨅ f ∈ s, (f : _) x, fun x y h => infᵢ₂_mono fun f _ => f.mono h⟩

/- warning: order_hom.Inf_apply -> OrderHom.infₛ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (InfSet.infₛ.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) s) x) (infᵢ.{u2, succ (max u1 u2)} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => infᵢ.{u2, 0} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfSet.infₛ.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) s) x) (infᵢ.{u2, succ (max u1 u2)} β (CompleteLattice.toInfSet.{u2} β _inst_2) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => infᵢ.{u2, 0} β (CompleteLattice.toInfSet.{u2} β _inst_2) (Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f x)))
Case conversion may be inaccurate. Consider using '#align order_hom.Inf_apply OrderHom.infₛ_applyₓ'. -/
@[simp]
theorem infₛ_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : infₛ s x = ⨅ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Inf_apply OrderHom.infₛ_apply

/- warning: order_hom.infi_apply -> OrderHom.infᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (infᵢ.{u2, u3} β (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (infᵢ.{u2, u3} β (CompleteLattice.toInfSet.{u2} β _inst_2) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i) x))
Case conversion may be inaccurate. Consider using '#align order_hom.infi_apply OrderHom.infᵢ_applyₓ'. -/
theorem infᵢ_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (infₛ_apply _ _).trans infᵢ_range
#align order_hom.infi_apply OrderHom.infᵢ_apply

/- warning: order_hom.coe_infi -> OrderHom.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (infᵢ.{max u1 u2, u3} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} (α -> β) (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (infᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instInfSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (infᵢ.{max u1 u2, u3} (α -> β) (Pi.infSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toInfSet.{u2} β _inst_2)) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i)))
Case conversion may be inaccurate. Consider using '#align order_hom.coe_infi OrderHom.coe_infᵢₓ'. -/
@[simp, norm_cast]
theorem coe_infᵢ {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
  funext fun x => (infᵢ_apply f x).trans (@infᵢ_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_infi OrderHom.coe_infᵢ

instance [CompleteLattice β] : SupSet (α →o β)
    where sup s := ⟨fun x => ⨆ f ∈ s, (f : _) x, fun x y h => supᵢ₂_mono fun f _ => f.mono h⟩

/- warning: order_hom.Sup_apply -> OrderHom.supₛ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (SupSet.supₛ.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) s) x) (supᵢ.{u2, succ (max u1 u2)} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => supᵢ.{u2, 0} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) (Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.hasMem.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) f x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (s : Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (SupSet.supₛ.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) s) x) (supᵢ.{u2, succ (max u1 u2)} β (CompleteLattice.toSupSet.{u2} β _inst_2) (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (f : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => supᵢ.{u2, 0} β (CompleteLattice.toSupSet.{u2} β _inst_2) (Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (Set.{max u2 u1} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (Set.instMembershipSet.{max u1 u2} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) f s) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) f x)))
Case conversion may be inaccurate. Consider using '#align order_hom.Sup_apply OrderHom.supₛ_applyₓ'. -/
@[simp]
theorem supₛ_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : supₛ s x = ⨆ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Sup_apply OrderHom.supₛ_apply

/- warning: order_hom.supr_apply -> OrderHom.supᵢ_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (supᵢ.{u2, u3} β (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i) x))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))) (x : α), Eq.{succ u2} β (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i)) x) (supᵢ.{u2, u3} β (CompleteLattice.toSupSet.{u2} β _inst_2) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i) x))
Case conversion may be inaccurate. Consider using '#align order_hom.supr_apply OrderHom.supᵢ_applyₓ'. -/
theorem supᵢ_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (supₛ_apply _ _).trans supᵢ_range
#align order_hom.supr_apply OrderHom.supᵢ_apply

/- warning: order_hom.coe_supr -> OrderHom.coe_supᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{max u1 u2, u3} ((fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.hasSup.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) ι (fun (i : ι) => coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (fun (_x : OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) => α -> β) (OrderHom.hasCoeToFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {ι : Sort.{u3}} [_inst_2 : CompleteLattice.{u2} β] (f : ι -> (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))))), Eq.{max (succ u1) (succ u2)} (α -> β) (OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (supᵢ.{max u1 u2, u3} (OrderHom.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)))) (OrderHom.instSupSetOrderHomToPreorderToPartialOrderToCompleteSemilatticeInf.{u1, u2} α β _inst_1 _inst_2) ι (fun (i : ι) => f i))) (supᵢ.{max u1 u2, u3} (α -> β) (Pi.supSet.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toSupSet.{u2} β _inst_2)) ι (fun (i : ι) => OrderHom.toFun.{u1, u2} α β _inst_1 (PartialOrder.toPreorder.{u2} β (CompleteSemilatticeInf.toPartialOrder.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (f i)))
Case conversion may be inaccurate. Consider using '#align order_hom.coe_supr OrderHom.coe_supᵢₓ'. -/
@[simp, norm_cast]
theorem coe_supᵢ {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
  funext fun x => (supᵢ_apply f x).trans (@supᵢ_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_supr OrderHom.coe_supᵢ

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop,
    OrderHom.orderBot with
    sup := supₛ
    le_Sup := fun s f hf x => le_supᵢ_of_le f (le_supᵢ _ hf)
    Sup_le := fun s f hf x => supᵢ₂_le fun g hg => hf g hg x
    inf := infₛ
    le_Inf := fun s f hf x => le_infᵢ₂ fun g hg => hf g hg x
    Inf_le := fun s f hf x => infᵢ_le_of_le f (infᵢ_le _ hf) }

#print OrderHom.iterate_sup_le_sup_iff /-
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
          _ ≤ (f^[n]) (f a₁ ⊔ a₂) := f.mono.iterate n (h a₁ a₂)
          _ ≤ (f^[n]) (f a₁) ⊔ a₂ := ih _ _
          _ = (f^[n + 1]) a₁ ⊔ a₂ := by rw [← Function.iterate_succ_apply]
          
    calc
      (f^[n₁ + n₂]) (a₁ ⊔ a₂) = (f^[n₁]) ((f^[n₂]) (a₁ ⊔ a₂)) :=
        Function.iterate_add_apply f n₁ n₂ _
      _ = (f^[n₁]) ((f^[n₂]) (a₂ ⊔ a₁)) := by rw [sup_comm]
      _ ≤ (f^[n₁]) ((f^[n₂]) a₂ ⊔ a₁) := f.mono.iterate n₁ (h' n₂ _ _)
      _ = (f^[n₁]) (a₁ ⊔ (f^[n₂]) a₂) := by rw [sup_comm]
      _ ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂ := h' n₁ a₁ _
      
#align order_hom.iterate_sup_le_sup_iff OrderHom.iterate_sup_le_sup_iff
-/

end Preorder

end OrderHom

