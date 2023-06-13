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

#print OrderHom.sInf_apply /-
@[simp]
theorem sInf_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : sInf s x = ⨅ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Inf_apply OrderHom.sInf_apply
-/

#print OrderHom.iInf_apply /-
theorem iInf_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨅ i, f i) x = ⨅ i, f i x :=
  (sInf_apply _ _).trans iInf_range
#align order_hom.infi_apply OrderHom.iInf_apply
-/

#print OrderHom.coe_iInf /-
@[simp, norm_cast]
theorem coe_iInf {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨅ i, f i : α →o β) : α → β) = ⨅ i, f i :=
  funext fun x => (iInf_apply f x).trans (@iInf_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_infi OrderHom.coe_iInf
-/

instance [CompleteLattice β] : SupSet (α →o β)
    where sSup s := ⟨fun x => ⨆ f ∈ s, (f : _) x, fun x y h => iSup₂_mono fun f _ => f.mono h⟩

#print OrderHom.sSup_apply /-
@[simp]
theorem sSup_apply [CompleteLattice β] (s : Set (α →o β)) (x : α) : sSup s x = ⨆ f ∈ s, (f : _) x :=
  rfl
#align order_hom.Sup_apply OrderHom.sSup_apply
-/

#print OrderHom.iSup_apply /-
theorem iSup_apply {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) (x : α) :
    (⨆ i, f i) x = ⨆ i, f i x :=
  (sSup_apply _ _).trans iSup_range
#align order_hom.supr_apply OrderHom.iSup_apply
-/

#print OrderHom.coe_iSup /-
@[simp, norm_cast]
theorem coe_iSup {ι : Sort _} [CompleteLattice β] (f : ι → α →o β) :
    ((⨆ i, f i : α →o β) : α → β) = ⨆ i, f i :=
  funext fun x => (iSup_apply f x).trans (@iSup_apply _ _ _ _ (fun i => f i) _).symm
#align order_hom.coe_supr OrderHom.coe_iSup
-/

instance [CompleteLattice β] : CompleteLattice (α →o β) :=
  { (_ : Lattice (α →o β)), OrderHom.orderTop,
    OrderHom.orderBot with
    sSup := sSup
    le_sup := fun s f hf x => le_iSup_of_le f (le_iSup _ hf)
    sup_le := fun s f hf x => iSup₂_le fun g hg => hf g hg x
    sInf := sInf
    le_inf := fun s f hf x => le_iInf₂ fun g hg => hf g hg x
    inf_le := fun s f hf x => iInf_le_of_le f (iInf_le _ hf) }

#print OrderHom.iterate_sup_le_sup_iff /-
theorem iterate_sup_le_sup_iff {α : Type _} [SemilatticeSup α] (f : α →o α) :
    (∀ n₁ n₂ a₁ a₂, (f^[n₁ + n₂]) (a₁ ⊔ a₂) ≤ (f^[n₁]) a₁ ⊔ (f^[n₂]) a₂) ↔
      ∀ a₁ a₂, f (a₁ ⊔ a₂) ≤ f a₁ ⊔ a₂ :=
  by
  constructor <;> intro h
  · exact h 1 0
  · intro n₁ n₂ a₁ a₂;
    have h' : ∀ n a₁ a₂, (f^[n]) (a₁ ⊔ a₂) ≤ (f^[n]) a₁ ⊔ a₂ :=
      by
      intro n; induction' n with n ih <;> intro a₁ a₂
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
-/

end Preorder

end OrderHom

