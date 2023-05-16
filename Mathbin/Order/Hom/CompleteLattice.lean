/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.hom.complete_lattice
! leanprover-community/mathlib commit 9d684a893c52e1d6692a504a118bfccbae04feeb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice
import Mathbin.Order.Hom.Lattice

/-!
# Complete lattice homomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines frame homorphisms and complete lattice homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `Sup_hom`: Maps which preserve `⨆`.
* `Inf_hom`: Maps which preserve `⨅`.
* `frame_hom`: Frame homomorphisms. Maps which preserve `⨆`, `⊓` and `⊤`.
* `complete_lattice_hom`: Complete lattice homomorphisms. Maps which preserve `⨆` and `⨅`.

## Typeclasses

* `Sup_hom_class`
* `Inf_hom_class`
* `frame_hom_class`
* `complete_lattice_hom_class`

## Concrete homs

* `complete_lattice.set_preimage`: `set.preimage` as a complete lattice homomorphism.

## TODO

Frame homs are Heyting homs.
-/


open Function OrderDual Set

variable {F α β γ δ : Type _} {ι : Sort _} {κ : ι → Sort _}

#print sSupHom /-
/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure sSupHom (α β : Type _) [SupSet α] [SupSet β] where
  toFun : α → β
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align Sup_hom sSupHom
-/

#print sInfHom /-
/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure sInfHom (α β : Type _) [InfSet α] [InfSet β] where
  toFun : α → β
  map_Inf' (s : Set α) : to_fun (sInf s) = sInf (to_fun '' s)
#align Inf_hom sInfHom
-/

#print FrameHom /-
/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align frame_hom FrameHom
-/

#print CompleteLatticeHom /-
/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  sInfHom α β where
  map_Sup' (s : Set α) : to_fun (sSup s) = sSup (to_fun '' s)
#align complete_lattice_hom CompleteLatticeHom
-/

section

#print sSupHomClass /-
/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class sSupHomClass (F : Type _) (α β : outParam <| Type _) [SupSet α] [SupSet β] extends
  FunLike F α fun _ => β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align Sup_hom_class sSupHomClass
-/

#print sInfHomClass /-
/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class sInfHomClass (F : Type _) (α β : outParam <| Type _) [InfSet α] [InfSet β] extends
  FunLike F α fun _ => β where
  map_sInf (f : F) (s : Set α) : f (sInf s) = sInf (f '' s)
#align Inf_hom_class sInfHomClass
-/

#print FrameHomClass /-
/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfTopHomClass F α β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align frame_hom_class FrameHomClass
-/

#print CompleteLatticeHomClass /-
/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends sInfHomClass F α β where
  map_sSup (f : F) (s : Set α) : f (sSup s) = sSup (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass
-/

end

export sSupHomClass (map_sSup)

export sInfHomClass (map_sInf)

attribute [simp] map_Sup map_Inf

/- warning: map_supr -> map_iSup is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : sSupHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sSupHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (iSup.{u2, u4} α _inst_1 ι (fun (i : ι) => g i))) (iSup.{u3, u4} β _inst_2 ι (fun (i : ι) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sSupHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u4} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : sSupHomClass.{u2, u4, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) (iSup.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (iSup.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (iSup.{u3, u1} β _inst_2 ι (fun (i : ι) => FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (g i)))
Case conversion may be inaccurate. Consider using '#align map_supr map_iSupₓ'. -/
theorem map_iSup [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by rw [iSup, iSup, map_Sup, Set.range_comp]
#align map_supr map_iSup

/- warning: map_supr₂ -> map_iSup₂ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : sSupHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sSupHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (iSup.{u2, u4} α _inst_1 ι (fun (i : ι) => iSup.{u2, u5} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (iSup.{u3, u4} β _inst_2 ι (fun (i : ι) => iSup.{u3, u5} β _inst_2 (κ i) (fun (j : κ i) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sSupHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i j))))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u5}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SupSet.{u5} α] [_inst_2 : SupSet.{u4} β] [_inst_3 : sSupHomClass.{u3, u5, u4} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u4} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) (iSup.{u5, u2} α _inst_1 ι (fun (i : ι) => iSup.{u5, u1} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (FunLike.coe.{succ u3, succ u5, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{u3, u5, u4} F α β _inst_1 _inst_2 _inst_3) f (iSup.{u5, u2} α _inst_1 ι (fun (i : ι) => iSup.{u5, u1} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (iSup.{u4, u2} β _inst_2 ι (fun (i : ι) => iSup.{u4, u1} β _inst_2 (κ i) (fun (j : κ i) => FunLike.coe.{succ u3, succ u5, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{u3, u5, u4} F α β _inst_1 _inst_2 _inst_3) f (g i j))))
Case conversion may be inaccurate. Consider using '#align map_supr₂ map_iSup₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_iSup₂ [SupSet α] [SupSet β] [sSupHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_iSup]
#align map_supr₂ map_iSup₂

/- warning: map_infi -> map_iInf is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : sInfHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sInfHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (iInf.{u2, u4} α _inst_1 ι (fun (i : ι) => g i))) (iInf.{u3, u4} β _inst_2 ι (fun (i : ι) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (sInfHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u4} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : sInfHomClass.{u2, u4, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) (iInf.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (iInf.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (iInf.{u3, u1} β _inst_2 ι (fun (i : ι) => FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (g i)))
Case conversion may be inaccurate. Consider using '#align map_infi map_iInfₓ'. -/
theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by rw [iInf, iInf, map_Inf, Set.range_comp]
#align map_infi map_iInf

/- warning: map_infi₂ clashes with map_infi -> map_iInf
warning: map_infi₂ -> map_iInf is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u_1}} {α : Type.{u_2}} {β : Type.{u_3}} {ι : Sort.{u_6}} {κ : ι -> Sort.{u_7}} [_inst_1 : InfSet.{u_2} α] [_inst_2 : InfSet.{u_3} β] [_inst_3 : sInfHomClass.{u_1, u_2, u_3} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u_3} β (coeFn.{succ u_1, max (succ u_2) (succ u_3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u_1, succ u_2, succ u_3} F α (fun (_x : α) => β) (sInfHomClass.toFunLike.{u_1, u_2, u_3} F α β _inst_1 _inst_2 _inst_3)) f (iInf.{u_2, u_6} α _inst_1 ι (fun (i : ι) => iInf.{u_2, u_7} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (iInf.{u_3, u_6} β _inst_2 ι (fun (i : ι) => iInf.{u_3, u_7} β _inst_2 (κ i) (fun (j : κ i) => coeFn.{succ u_1, max (succ u_2) (succ u_3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u_1, succ u_2, succ u_3} F α (fun (_x : α) => β) (sInfHomClass.toFunLike.{u_1, u_2, u_3} F α β _inst_1 _inst_2 _inst_3)) f (g i j))))
but is expected to have type
  forall {F : Type.{u_3}} {α : Type.{u_1}} {β : Type.{u_2}} {ι : Sort.{u_4}} [κ : InfSet.{u_1} α] [_inst_1 : InfSet.{u_2} β] [_inst_2 : sInfHomClass.{u_3, u_1, u_2} F α β κ _inst_1] (_inst_3 : F) (f : ι -> α), Eq.{succ u_2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) (iInf.{u_1, u_4} α κ ι (fun (i : ι) => f i))) (FunLike.coe.{succ u_3, succ u_1, succ u_2} F α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (sInfHomClass.toFunLike.{u_3, u_1, u_2} F α β κ _inst_1 _inst_2) _inst_3 (iInf.{u_1, u_4} α κ ι (fun (i : ι) => f i))) (iInf.{u_2, u_4} β _inst_1 ι (fun (i : ι) => FunLike.coe.{succ u_3, succ u_1, succ u_2} F α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (sInfHomClass.toFunLike.{u_3, u_1, u_2} F α β κ _inst_1 _inst_2) _inst_3 (f i)))
Case conversion may be inaccurate. Consider using '#align map_infi₂ map_iInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_iInf [InfSet α] [InfSet β] [sInfHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_iInf]
#align map_infi₂ map_iInf

/- warning: Sup_hom_class.to_sup_bot_hom_class -> sSupHomClass.toSupBotHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : sSupHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))], SupBotHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeSup.toHasSup.{u3} β (Lattice.toSemilatticeSup.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toHasBot.{u2} α _inst_1) (CompleteLattice.toHasBot.{u3} β _inst_2)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : sSupHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)], SupBotHomClass.{u1, u2, u3} F α β (SemilatticeSup.toSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeSup.toSup.{u3} β (Lattice.toSemilatticeSup.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toBot.{u2} α _inst_1) (CompleteLattice.toBot.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align Sup_hom_class.to_sup_bot_hom_class sSupHomClass.toSupBotHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) sSupHomClass.toSupBotHomClass [CompleteLattice α] [CompleteLattice β]
    [sSupHomClass F α β] : SupBotHomClass F α β :=
  {
    ‹sSupHomClass F α
        β› with
    map_sup := fun f a b => by rw [← sSup_pair, map_Sup, Set.image_pair, sSup_pair]
    map_bot := fun f => by rw [← sSup_empty, map_Sup, Set.image_empty, sSup_empty] }
#align Sup_hom_class.to_sup_bot_hom_class sSupHomClass.toSupBotHomClass

/- warning: Inf_hom_class.to_inf_top_hom_class -> sInfHomClass.toInfTopHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : sInfHomClass.{u1, u2, u3} F α β (CompleteSemilatticeInf.toHasInf.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))], InfTopHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeInf.toHasInf.{u3} β (Lattice.toSemilatticeInf.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toHasTop.{u2} α _inst_1) (CompleteLattice.toHasTop.{u3} β _inst_2)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : sInfHomClass.{u1, u2, u3} F α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2)], InfTopHomClass.{u1, u2, u3} F α β (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toInf.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2)) (CompleteLattice.toTop.{u2} α _inst_1) (CompleteLattice.toTop.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align Inf_hom_class.to_inf_top_hom_class sInfHomClass.toInfTopHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) sInfHomClass.toInfTopHomClass [CompleteLattice α] [CompleteLattice β]
    [sInfHomClass F α β] : InfTopHomClass F α β :=
  {
    ‹sInfHomClass F α
        β› with
    map_inf := fun f a b => by rw [← sInf_pair, map_Inf, Set.image_pair, sInf_pair]
    map_top := fun f => by rw [← sInf_empty, map_Inf, Set.image_empty, sInf_empty] }
#align Inf_hom_class.to_inf_top_hom_class sInfHomClass.toInfTopHomClass

/- warning: frame_hom_class.to_Sup_hom_class -> FrameHomClass.tosSupHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : FrameHomClass.{u1, u2, u3} F α β _inst_1 _inst_2], sSupHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : FrameHomClass.{u1, u2, u3} F α β _inst_1 _inst_2], sSupHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align frame_hom_class.to_Sup_hom_class FrameHomClass.tosSupHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.tosSupHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : sSupHomClass F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.tosSupHomClass

#print FrameHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, sSupHomClass.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass
-/

#print CompleteLatticeHomClass.toFrameHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass
-/

#print CompleteLatticeHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { sSupHomClass.toSupBotHomClass, sInfHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass
-/

/- warning: order_iso_class.to_Sup_hom_class -> OrderIsoClass.tosSupHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], sSupHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], sSupHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Sup_hom_class OrderIsoClass.tosSupHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosSupHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : sSupHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sSup := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sSup_le_iff, Set.ball_image_iff] }
#align order_iso_class.to_Sup_hom_class OrderIsoClass.tosSupHomClass

/- warning: order_iso_class.to_Inf_hom_class -> OrderIsoClass.tosInfHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], sInfHomClass.{u1, u2, u3} F α β (CompleteSemilatticeInf.toHasInf.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], sInfHomClass.{u1, u2, u3} F α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Inf_hom_class OrderIsoClass.tosInfHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.tosInfHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : sInfHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_sInf := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_sInf_iff, Set.ball_image_iff] }
#align order_iso_class.to_Inf_hom_class OrderIsoClass.tosInfHomClass

/- warning: order_iso_class.to_complete_lattice_hom_class -> OrderIsoClass.toCompleteLatticeHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toHasLe.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toHasLe.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], CompleteLatticeHomClass.{u1, u2, u3} F α β _inst_1 _inst_2
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], CompleteLatticeHomClass.{u1, u2, u3} F α β _inst_1 _inst_2
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.tosSupHomClass, OrderIsoClass.toLatticeHomClass,
    show sInfHomClass F α β from inferInstance with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass

instance [SupSet α] [SupSet β] [sSupHomClass F α β] : CoeTC F (sSupHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [InfSet α] [InfSet β] [sInfHomClass F α β] : CoeTC F (sInfHom α β) :=
  ⟨fun f => ⟨f, map_sInf f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_sSup f⟩⟩

/-! ### Supremum homomorphisms -/


namespace sSupHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : sSupHomClass (sSupHom α β) α β
    where
  coe := sSupHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_sSup := sSupHom.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (sSupHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: Sup_hom.to_fun_eq_coe -> sSupHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {f : sSupHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (sSupHom.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {f : sSupHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (sSupHom.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align Sup_hom.to_fun_eq_coe sSupHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : sSupHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Sup_hom.to_fun_eq_coe sSupHom.toFun_eq_coe

/- warning: Sup_hom.ext -> sSupHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {f : sSupHom.{u1, u2} α β _inst_1 _inst_2} {g : sSupHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {f : sSupHom.{u2, u1} α β _inst_1 _inst_2} {g : sSupHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (sSupHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align Sup_hom.ext sSupHom.extₓ'. -/
@[ext]
theorem ext {f g : sSupHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext sSupHom.ext

/- warning: Sup_hom.copy -> sSupHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (sSupHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sSupHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (sSupHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u1, u2} α β _inst_1 _inst_2)) f)) -> (sSupHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align Sup_hom.copy sSupHom.copyₓ'. -/
/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : sSupHom α β
    where
  toFun := f'
  map_Sup' := h.symm ▸ f.map_Sup'
#align Sup_hom.copy sSupHom.copy

/- warning: Sup_hom.coe_copy -> sSupHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (sSupHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : sSupHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) (sSupHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_copy sSupHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : sSupHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy sSupHom.coe_copy

/- warning: Sup_hom.copy_eq -> sSupHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : sSupHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (sSupHom.{u2, u1} α β _inst_1 _inst_2) (sSupHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.copy_eq sSupHom.copy_eqₓ'. -/
theorem copy_eq (f : sSupHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq sSupHom.copy_eq

variable (α)

#print sSupHom.id /-
/-- `id` as a `Sup_hom`. -/
protected def id : sSupHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id sSupHom.id
-/

instance : Inhabited (sSupHom α α) :=
  ⟨sSupHom.id α⟩

/- warning: Sup_hom.coe_id -> sSupHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sSupHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (sSupHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (sSupHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (sSupHomClass.toFunLike.{u1, u1, u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (sSupHom.instSSupHomClassSSupHom.{u1, u1} α α _inst_1 _inst_1)) (sSupHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_id sSupHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(sSupHom.id α) = id :=
  rfl
#align Sup_hom.coe_id sSupHom.coe_id

variable {α}

/- warning: Sup_hom.id_apply -> sSupHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sSupHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (sSupHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (sSupHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (sSupHomClass.toFunLike.{u1, u1, u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (sSupHom.instSSupHomClassSSupHom.{u1, u1} α α _inst_1 _inst_1)) (sSupHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align Sup_hom.id_apply sSupHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : sSupHom.id α a = a :=
  rfl
#align Sup_hom.id_apply sSupHom.id_apply

#print sSupHom.comp /-
/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : sSupHom β γ) (g : sSupHom α β) : sSupHom α γ
    where
  toFun := f ∘ g
  map_Sup' s := by rw [comp_apply, map_Sup, map_Sup, Set.image_image]
#align Sup_hom.comp sSupHom.comp
-/

/- warning: Sup_hom.coe_comp -> sSupHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (f : sSupHom.{u2, u3} β γ _inst_2 _inst_3) (g : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : sSupHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (sSupHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sSupHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sSupHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (f : sSupHom.{u3, u2} β γ _inst_2 _inst_3) (g : sSupHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (sSupHom.instSSupHomClassSSupHom.{u1, u2} α γ _inst_1 _inst_3)) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sSupHom.instSSupHomClassSSupHom.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_comp sSupHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : sSupHom β γ) (g : sSupHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp sSupHom.coe_comp

/- warning: Sup_hom.comp_apply -> sSupHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (f : sSupHom.{u2, u3} β γ _inst_2 _inst_3) (g : sSupHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : sSupHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (sSupHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sSupHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sSupHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (f : sSupHom.{u3, u2} β γ _inst_2 _inst_3) (g : sSupHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (sSupHom.instSSupHomClassSSupHom.{u1, u2} α γ _inst_1 _inst_3)) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sSupHom.instSSupHomClassSSupHom.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_apply sSupHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : sSupHom β γ) (g : sSupHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply sSupHom.comp_apply

/- warning: Sup_hom.comp_assoc -> sSupHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] [_inst_4 : SupSet.{u4} δ] (f : sSupHom.{u3, u4} γ δ _inst_3 _inst_4) (g : sSupHom.{u2, u3} β γ _inst_2 _inst_3) (h : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (sSupHom.{u1, u4} α δ _inst_1 _inst_4) (sSupHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (sSupHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (sSupHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u4} γ] [_inst_4 : SupSet.{u3} δ] (f : sSupHom.{u4, u3} γ δ _inst_3 _inst_4) (g : sSupHom.{u2, u4} β γ _inst_2 _inst_3) (h : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} α δ _inst_1 _inst_4) (sSupHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (sSupHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (sSupHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (sSupHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_assoc sSupHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : sSupHom γ δ) (g : sSupHom β γ) (h : sSupHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc sSupHom.comp_assoc

/- warning: Sup_hom.comp_id -> sSupHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (sSupHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : sSupHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (sSupHom.{u2, u1} α β _inst_1 _inst_2) (sSupHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (sSupHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_id sSupHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : sSupHom α β) : f.comp (sSupHom.id α) = f :=
  ext fun a => rfl
#align Sup_hom.comp_id sSupHom.comp_id

/- warning: Sup_hom.id_comp -> sSupHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (sSupHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : sSupHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (sSupHom.{u2, u1} α β _inst_1 _inst_2) (sSupHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (sSupHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.id_comp sSupHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : sSupHom α β) : (sSupHom.id β).comp f = f :=
  ext fun a => rfl
#align Sup_hom.id_comp sSupHom.id_comp

/- warning: Sup_hom.cancel_right -> sSupHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] {g₁ : sSupHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : sSupHom.{u2, u3} β γ _inst_2 _inst_3} {f : sSupHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] {g₁ : sSupHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : sSupHom.{u3, u2} β γ _inst_2 _inst_3} {f : sSupHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (sSupHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sSupHom.instSSupHomClassSSupHom.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align Sup_hom.cancel_right sSupHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : sSupHom β γ} {f : sSupHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Sup_hom.cancel_right sSupHom.cancel_right

/- warning: Sup_hom.cancel_left -> sSupHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] {g : sSupHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : sSupHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : sSupHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sSupHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sSupHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] {g : sSupHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : sSupHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : sSupHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sSupHom.instSSupHomClassSSupHom.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align Sup_hom.cancel_left sSupHom.cancel_leftₓ'. -/
theorem cancel_left {g : sSupHom β γ} {f₁ f₂ : sSupHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Sup_hom.cancel_left sSupHom.cancel_left

end SupSet

variable [CompleteLattice β]

instance : PartialOrder (sSupHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (sSupHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sSup_empty]
      · rw [hs.image_const, sSup_singleton]⟩⟩

instance : OrderBot (sSupHom α β) :=
  ⟨⊥, fun f a => bot_le⟩

/- warning: Sup_hom.coe_bot -> sSupHom.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β], Eq.{succ (max u1 u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (fun (_x : sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (sSupHom.hasBot.{u1, u2} α β _inst_1 _inst_2))) (Bot.bot.{max u1 u2} (α -> β) (Pi.hasBot.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toHasBot.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] {_inst_2 : CompleteLattice.{u1} β}, Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sSupHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (sSupHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2) (sSupHom.instSSupHomClassSSupHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2))) (Bot.bot.{max u2 u1} (sSupHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) (sSupHom.instBotSSupHomToSupSet.{u2, u1} α β _inst_1 _inst_2))) (Bot.bot.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (Pi.instBotForAll.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (fun (i : α) => CompleteLattice.toBot.{u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) i) _inst_2)))
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_bot sSupHom.coe_botₓ'. -/
@[simp]
theorem coe_bot : ⇑(⊥ : sSupHom α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot sSupHom.coe_bot

/- warning: Sup_hom.bot_apply -> sSupHom.bot_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (fun (_x : sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) => α -> β) (sSupHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (sSupHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (sSupHom.hasBot.{u1, u2} α β _inst_1 _inst_2)) a) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] {_inst_2 : CompleteLattice.{u2} β} (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sSupHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (sSupHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2) (sSupHom.instSSupHomClassSSupHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (sSupHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) (sSupHom.instBotSSupHomToSupSet.{u1, u2} α β _inst_1 _inst_2)) a) (Bot.bot.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (CompleteLattice.toBot.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) _inst_2))
Case conversion may be inaccurate. Consider using '#align Sup_hom.bot_apply sSupHom.bot_applyₓ'. -/
@[simp]
theorem bot_apply (a : α) : (⊥ : sSupHom α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply sSupHom.bot_apply

end sSupHom

/-! ### Infimum homomorphisms -/


namespace sInfHom

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : sInfHomClass (sInfHom α β) α β
    where
  coe := sInfHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_sInf := sInfHom.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (sInfHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: Inf_hom.to_fun_eq_coe -> sInfHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {f : sInfHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (sInfHom.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {f : sInfHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (sInfHom.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align Inf_hom.to_fun_eq_coe sInfHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : sInfHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Inf_hom.to_fun_eq_coe sInfHom.toFun_eq_coe

/- warning: Inf_hom.ext -> sInfHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {f : sInfHom.{u1, u2} α β _inst_1 _inst_2} {g : sInfHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {f : sInfHom.{u2, u1} α β _inst_1 _inst_2} {g : sInfHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (sInfHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align Inf_hom.ext sInfHom.extₓ'. -/
@[ext]
theorem ext {f g : sInfHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext sInfHom.ext

/- warning: Inf_hom.copy -> sInfHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (sInfHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sInfHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (sInfHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u1, u2} α β _inst_1 _inst_2)) f)) -> (sInfHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align Inf_hom.copy sInfHom.copyₓ'. -/
/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : sInfHom α β
    where
  toFun := f'
  map_Inf' := h.symm ▸ f.map_Inf'
#align Inf_hom.copy sInfHom.copy

/- warning: Inf_hom.coe_copy -> sInfHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (sInfHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : sInfHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) (sInfHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_copy sInfHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : sInfHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy sInfHom.coe_copy

/- warning: Inf_hom.copy_eq -> sInfHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : sInfHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (sInfHom.{u2, u1} α β _inst_1 _inst_2) (sInfHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.copy_eq sInfHom.copy_eqₓ'. -/
theorem copy_eq (f : sInfHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq sInfHom.copy_eq

variable (α)

#print sInfHom.id /-
/-- `id` as an `Inf_hom`. -/
protected def id : sInfHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id sInfHom.id
-/

instance : Inhabited (sInfHom α α) :=
  ⟨sInfHom.id α⟩

/- warning: Inf_hom.coe_id -> sInfHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sInfHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (sInfHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (sInfHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (sInfHom.instSInfHomClassSInfHom.{u1, u1} α α _inst_1 _inst_1)) (sInfHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_id sInfHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(sInfHom.id α) = id :=
  rfl
#align Inf_hom.coe_id sInfHom.coe_id

variable {α}

/- warning: Inf_hom.id_apply -> sInfHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sInfHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (sInfHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (sInfHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (sInfHom.instSInfHomClassSInfHom.{u1, u1} α α _inst_1 _inst_1)) (sInfHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align Inf_hom.id_apply sInfHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : sInfHom.id α a = a :=
  rfl
#align Inf_hom.id_apply sInfHom.id_apply

#print sInfHom.comp /-
/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : sInfHom β γ) (g : sInfHom α β) : sInfHom α γ
    where
  toFun := f ∘ g
  map_Inf' s := by rw [comp_apply, map_Inf, map_Inf, Set.image_image]
#align Inf_hom.comp sInfHom.comp
-/

/- warning: Inf_hom.coe_comp -> sInfHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (f : sInfHom.{u2, u3} β γ _inst_2 _inst_3) (g : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : sInfHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (sInfHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sInfHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sInfHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (f : sInfHom.{u3, u2} β γ _inst_2 _inst_3) (g : sInfHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (sInfHom.instSInfHomClassSInfHom.{u1, u2} α γ _inst_1 _inst_3)) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sInfHom.instSInfHomClassSInfHom.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_comp sInfHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : sInfHom β γ) (g : sInfHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp sInfHom.coe_comp

/- warning: Inf_hom.comp_apply -> sInfHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (f : sInfHom.{u2, u3} β γ _inst_2 _inst_3) (g : sInfHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : sInfHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (sInfHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sInfHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sInfHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (f : sInfHom.{u3, u2} β γ _inst_2 _inst_3) (g : sInfHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (sInfHom.instSInfHomClassSInfHom.{u1, u2} α γ _inst_1 _inst_3)) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sInfHom.instSInfHomClassSInfHom.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_apply sInfHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : sInfHom β γ) (g : sInfHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply sInfHom.comp_apply

/- warning: Inf_hom.comp_assoc -> sInfHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] [_inst_4 : InfSet.{u4} δ] (f : sInfHom.{u3, u4} γ δ _inst_3 _inst_4) (g : sInfHom.{u2, u3} β γ _inst_2 _inst_3) (h : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (sInfHom.{u1, u4} α δ _inst_1 _inst_4) (sInfHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (sInfHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (sInfHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u4} γ] [_inst_4 : InfSet.{u3} δ] (f : sInfHom.{u4, u3} γ δ _inst_3 _inst_4) (g : sInfHom.{u2, u4} β γ _inst_2 _inst_3) (h : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} α δ _inst_1 _inst_4) (sInfHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (sInfHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (sInfHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (sInfHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_assoc sInfHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : sInfHom γ δ) (g : sInfHom β γ) (h : sInfHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc sInfHom.comp_assoc

/- warning: Inf_hom.comp_id -> sInfHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (sInfHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : sInfHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (sInfHom.{u2, u1} α β _inst_1 _inst_2) (sInfHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (sInfHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_id sInfHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : sInfHom α β) : f.comp (sInfHom.id α) = f :=
  ext fun a => rfl
#align Inf_hom.comp_id sInfHom.comp_id

/- warning: Inf_hom.id_comp -> sInfHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (sInfHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : sInfHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (sInfHom.{u2, u1} α β _inst_1 _inst_2) (sInfHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (sInfHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.id_comp sInfHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : sInfHom α β) : (sInfHom.id β).comp f = f :=
  ext fun a => rfl
#align Inf_hom.id_comp sInfHom.id_comp

/- warning: Inf_hom.cancel_right -> sInfHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] {g₁ : sInfHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : sInfHom.{u2, u3} β γ _inst_2 _inst_3} {f : sInfHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] {g₁ : sInfHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : sInfHom.{u3, u2} β γ _inst_2 _inst_3} {f : sInfHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (sInfHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (sInfHom.instSInfHomClassSInfHom.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align Inf_hom.cancel_right sInfHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : sInfHom β γ} {f : sInfHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Inf_hom.cancel_right sInfHom.cancel_right

/- warning: Inf_hom.cancel_left -> sInfHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] {g : sInfHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : sInfHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : sInfHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : sInfHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (sInfHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] {g : sInfHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : sInfHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : sInfHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (sInfHom.instSInfHomClassSInfHom.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align Inf_hom.cancel_left sInfHom.cancel_leftₓ'. -/
theorem cancel_left {g : sInfHom β γ} {f₁ f₂ : sInfHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Inf_hom.cancel_left sInfHom.cancel_left

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (sInfHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (sInfHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, sInf_empty]
      · rw [hs.image_const, sInf_singleton]⟩⟩

instance : OrderTop (sInfHom α β) :=
  ⟨⊤, fun f a => le_top⟩

/- warning: Inf_hom.coe_top -> sInfHom.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β], Eq.{succ (max u1 u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (fun (_x : sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (Top.top.{max u1 u2} (sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (sInfHom.hasTop.{u1, u2} α β _inst_1 _inst_2))) (Top.top.{max u1 u2} (α -> β) (Pi.hasTop.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toHasTop.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : CompleteLattice.{u1} β], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (sInfHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (sInfHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2) (sInfHom.instSInfHomClassSInfHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2))) (Top.top.{max u2 u1} (sInfHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) (sInfHom.instTopSInfHomToInfSet.{u2, u1} α β _inst_1 _inst_2))) (Top.top.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) ᾰ) (Pi.instTopForAll.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) ᾰ) (fun (i : α) => CompleteLattice.toTop.{u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) i) _inst_2)))
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_top sInfHom.coe_topₓ'. -/
@[simp]
theorem coe_top : ⇑(⊤ : sInfHom α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top sInfHom.coe_top

/- warning: Inf_hom.top_apply -> sInfHom.top_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (fun (_x : sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) => α -> β) (sInfHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (Top.top.{max u1 u2} (sInfHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (sInfHom.hasTop.{u1, u2} α β _inst_1 _inst_2)) a) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (sInfHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (sInfHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2) (sInfHom.instSInfHomClassSInfHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2))) (Top.top.{max u1 u2} (sInfHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) (sInfHom.instTopSInfHomToInfSet.{u1, u2} α β _inst_1 _inst_2)) a) (Top.top.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (CompleteLattice.toTop.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) _inst_2))
Case conversion may be inaccurate. Consider using '#align Inf_hom.top_apply sInfHom.top_applyₓ'. -/
@[simp]
theorem top_apply (a : α) : (⊤ : sInfHom α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply sInfHom.top_apply

end sInfHom

/-! ### Frame homomorphisms -/


namespace FrameHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : FrameHomClass (FrameHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g
    congr
  map_sSup f := f.map_Sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (FrameHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

#print FrameHom.toLatticeHom /-
/-- Reinterpret a `frame_hom` as a `lattice_hom`. -/
def toLatticeHom (f : FrameHom α β) : LatticeHom α β :=
  f
#align frame_hom.to_lattice_hom FrameHom.toLatticeHom
-/

/- warning: frame_hom.to_fun_eq_coe -> FrameHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : FrameHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (InfHom.toFun.{u1, u2} α β (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))) (InfTopHom.toInfHom.{u1, u2} α β (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (CompleteLattice.toLattice.{u2} β _inst_2))) (CompleteLattice.toHasTop.{u1} α _inst_1) (CompleteLattice.toHasTop.{u2} β _inst_2) (FrameHom.toInfTopHom.{u1, u2} α β _inst_1 _inst_2 f))) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : FrameHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (InfHom.toFun.{u2, u1} α β (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_2)) (InfTopHom.toInfHom.{u2, u1} α β (Lattice.toInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_2)) (CompleteLattice.toTop.{u2} α _inst_1) (CompleteLattice.toTop.{u1} β _inst_2) (FrameHom.toInfTopHom.{u2, u1} α β _inst_1 _inst_2 f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl
#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coe

/- warning: frame_hom.ext -> FrameHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : FrameHom.{u1, u2} α β _inst_1 _inst_2} {g : FrameHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : FrameHom.{u2, u1} α β _inst_1 _inst_2} {g : FrameHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) g a)) -> (Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align frame_hom.ext FrameHom.extₓ'. -/
@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align frame_hom.ext FrameHom.ext

/- warning: frame_hom.copy -> FrameHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (FrameHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} β _inst_2) (FrameHomClass.tosSupHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α β _inst_1 _inst_2))) f)) -> (FrameHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align frame_hom.copy FrameHom.copyₓ'. -/
/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : sSupHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy

/- warning: frame_hom.coe_copy -> FrameHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (FrameHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) (FrameHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align frame_hom.coe_copy FrameHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align frame_hom.coe_copy FrameHom.coe_copy

/- warning: frame_hom.copy_eq -> FrameHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (FrameHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.tosSupHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) (FrameHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align frame_hom.copy_eq FrameHom.copy_eqₓ'. -/
theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align frame_hom.copy_eq FrameHom.copy_eq

variable (α)

#print FrameHom.id /-
/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { sSupHom.id α with toInfTopHom := InfTopHom.id α }
#align frame_hom.id FrameHom.id
-/

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

/- warning: frame_hom.coe_id -> FrameHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : FrameHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (FrameHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (FrameHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (sSupHomClass.toFunLike.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1) (FrameHomClass.tosSupHomClass.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (FrameHom.instFrameHomClassFrameHom.{u1, u1} α α _inst_1 _inst_1))) (FrameHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align frame_hom.coe_id FrameHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(FrameHom.id α) = id :=
  rfl
#align frame_hom.coe_id FrameHom.coe_id

variable {α}

/- warning: frame_hom.id_apply -> FrameHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : FrameHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (FrameHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (FrameHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (sSupHomClass.toFunLike.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1) (FrameHomClass.tosSupHomClass.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (FrameHom.instFrameHomClassFrameHom.{u1, u1} α α _inst_1 _inst_1))) (FrameHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align frame_hom.id_apply FrameHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl
#align frame_hom.id_apply FrameHom.id_apply

#print FrameHom.comp /-
/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : sSupHom β γ).comp (g : sSupHom α β) with toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
#align frame_hom.comp FrameHom.comp
-/

/- warning: frame_hom.coe_comp -> FrameHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : FrameHom.{u2, u3} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : FrameHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (FrameHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : FrameHom.{u3, u2} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.tosSupHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α γ _inst_1 _inst_3))) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.tosSupHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.tosSupHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align frame_hom.coe_comp FrameHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align frame_hom.coe_comp FrameHom.coe_comp

/- warning: frame_hom.comp_apply -> FrameHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : FrameHom.{u2, u3} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : FrameHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (FrameHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : FrameHom.{u3, u2} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (sSupHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.tosSupHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α γ _inst_1 _inst_3))) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.tosSupHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.tosSupHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) g a))
Case conversion may be inaccurate. Consider using '#align frame_hom.comp_apply FrameHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : FrameHom β γ) (g : FrameHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align frame_hom.comp_apply FrameHom.comp_apply

/- warning: frame_hom.comp_assoc -> FrameHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] [_inst_4 : CompleteLattice.{u4} δ] (f : FrameHom.{u3, u4} γ δ _inst_3 _inst_4) (g : FrameHom.{u2, u3} β γ _inst_2 _inst_3) (h : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (FrameHom.{u1, u4} α δ _inst_1 _inst_4) (FrameHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (FrameHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (FrameHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u4} γ] [_inst_4 : CompleteLattice.{u3} δ] (f : FrameHom.{u4, u3} γ δ _inst_3 _inst_4) (g : FrameHom.{u2, u4} β γ _inst_2 _inst_3) (h : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α δ _inst_1 _inst_4) (FrameHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (FrameHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (FrameHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (FrameHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align frame_hom.comp_assoc FrameHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : FrameHom γ δ) (g : FrameHom β γ) (h : FrameHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align frame_hom.comp_assoc FrameHom.comp_assoc

/- warning: frame_hom.comp_id -> FrameHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (FrameHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (FrameHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) (FrameHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (FrameHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align frame_hom.comp_id FrameHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : FrameHom α β) : f.comp (FrameHom.id α) = f :=
  ext fun a => rfl
#align frame_hom.comp_id FrameHom.comp_id

/- warning: frame_hom.id_comp -> FrameHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (FrameHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (FrameHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) (FrameHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (FrameHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align frame_hom.id_comp FrameHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : FrameHom α β) : (FrameHom.id β).comp f = f :=
  ext fun a => rfl
#align frame_hom.id_comp FrameHom.id_comp

/- warning: frame_hom.cancel_right -> FrameHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g₁ : FrameHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : FrameHom.{u2, u3} β γ _inst_2 _inst_3} {f : FrameHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g₁ : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {f : FrameHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (sSupHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.tosSupHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align frame_hom.cancel_right FrameHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align frame_hom.cancel_right FrameHom.cancel_right

/- warning: frame_hom.cancel_left -> FrameHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g : FrameHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : FrameHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : FrameHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : FrameHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : FrameHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (sSupHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.tosSupHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align frame_hom.cancel_left FrameHom.cancel_leftₓ'. -/
theorem cancel_left {g : FrameHom β γ} {f₁ f₂ : FrameHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align frame_hom.cancel_left FrameHom.cancel_left

instance : PartialOrder (FrameHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

end FrameHom

/-! ### Complete lattice homomorphisms -/


namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ] [CompleteLattice δ]

instance : CompleteLatticeHomClass (CompleteLatticeHom α β) α β
    where
  coe f := f.toFun
  coe_injective' f g h := by obtain ⟨⟨_, _⟩, _⟩ := f <;> obtain ⟨⟨_, _⟩, _⟩ := g <;> congr
  map_sSup f := f.map_Sup'
  map_sInf f := f.map_Inf'

/- warning: complete_lattice_hom.to_Sup_hom -> CompleteLatticeHom.tosSupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β], (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) -> (sSupHom.{u1, u2} α β (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β], (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) -> (sSupHom.{u1, u2} α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.tosSupHomₓ'. -/
/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def tosSupHom (f : CompleteLatticeHom α β) : sSupHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.tosSupHom

#print CompleteLatticeHom.toBoundedLatticeHom /-
/-- Reinterpret a `complete_lattice_hom` as a `bounded_lattice_hom`. -/
def toBoundedLatticeHom (f : CompleteLatticeHom α β) : BoundedLatticeHom α β :=
  f
#align complete_lattice_hom.to_bounded_lattice_hom CompleteLatticeHom.toBoundedLatticeHom
-/

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CompleteLatticeHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: complete_lattice_hom.to_fun_eq_coe -> CompleteLatticeHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (sInfHom.toFun.{u1, u2} α β (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (CompleteLatticeHom.toInfHom.{u1, u2} α β _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (sInfHom.toFun.{u2, u1} α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHom.tosInfHom.{u2, u1} α β _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coe

/- warning: complete_lattice_hom.ext -> CompleteLatticeHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2} {g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2} {g : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) g a)) -> (Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.ext CompleteLatticeHom.extₓ'. -/
@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext

/- warning: complete_lattice_hom.copy -> CompleteLatticeHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2))) f)) -> (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.copy CompleteLatticeHom.copyₓ'. -/
/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.tosSupHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy

/- warning: complete_lattice_hom.coe_copy -> CompleteLatticeHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) (CompleteLatticeHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copy

/- warning: complete_lattice_hom.copy_eq -> CompleteLatticeHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eqₓ'. -/
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eq

variable (α)

#print CompleteLatticeHom.id /-
/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { sSupHom.id α, sInfHom.id α with toFun := id }
#align complete_lattice_hom.id CompleteLatticeHom.id
-/

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

/- warning: complete_lattice_hom.coe_id -> CompleteLatticeHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (CompleteLatticeHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) (CompleteLatticeHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_id CompleteLatticeHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(CompleteLatticeHom.id α) = id :=
  rfl
#align complete_lattice_hom.coe_id CompleteLatticeHom.coe_id

variable {α}

/- warning: complete_lattice_hom.id_apply -> CompleteLatticeHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (CompleteLatticeHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.tosInfHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) (CompleteLatticeHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.id_apply CompleteLatticeHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl
#align complete_lattice_hom.id_apply CompleteLatticeHom.id_apply

#print CompleteLatticeHom.comp /-
/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.tosSupHom.comp g.tosSupHom with toInfHom := f.toInfHom.comp g.toInfHom }
#align complete_lattice_hom.comp CompleteLatticeHom.comp
-/

/- warning: complete_lattice_hom.coe_comp -> CompleteLatticeHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CompleteLatticeHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3))) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.tosInfHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_comp

/- warning: complete_lattice_hom.comp_apply -> CompleteLatticeHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CompleteLatticeHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => γ) _x) (sInfHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3))) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.tosInfHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) g a))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.comp_apply CompleteLatticeHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl
#align complete_lattice_hom.comp_apply CompleteLatticeHom.comp_apply

/- warning: complete_lattice_hom.comp_assoc -> CompleteLatticeHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] [_inst_4 : CompleteLattice.{u4} δ] (f : CompleteLatticeHom.{u3, u4} γ δ _inst_3 _inst_4) (g : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (h : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (CompleteLatticeHom.{u1, u4} α δ _inst_1 _inst_4) (CompleteLatticeHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (CompleteLatticeHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (CompleteLatticeHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u4} γ] [_inst_4 : CompleteLattice.{u3} δ] (f : CompleteLatticeHom.{u4, u3} γ δ _inst_3 _inst_4) (g : CompleteLatticeHom.{u2, u4} β γ _inst_2 _inst_3) (h : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α δ _inst_1 _inst_4) (CompleteLatticeHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (CompleteLatticeHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (CompleteLatticeHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (CompleteLatticeHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.comp_assoc CompleteLatticeHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : CompleteLatticeHom γ δ) (g : CompleteLatticeHom β γ)
    (h : CompleteLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align complete_lattice_hom.comp_assoc CompleteLatticeHom.comp_assoc

/- warning: complete_lattice_hom.comp_id -> CompleteLatticeHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (CompleteLatticeHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (CompleteLatticeHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (CompleteLatticeHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.comp_id CompleteLatticeHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : CompleteLatticeHom α β) : f.comp (CompleteLatticeHom.id α) = f :=
  ext fun a => rfl
#align complete_lattice_hom.comp_id CompleteLatticeHom.comp_id

/- warning: complete_lattice_hom.id_comp -> CompleteLatticeHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (CompleteLatticeHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (CompleteLatticeHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (CompleteLatticeHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.id_comp CompleteLatticeHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : CompleteLatticeHom α β) : (CompleteLatticeHom.id β).comp f = f :=
  ext fun a => rfl
#align complete_lattice_hom.id_comp CompleteLatticeHom.id_comp

/- warning: complete_lattice_hom.cancel_right -> CompleteLatticeHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g₁ : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3} {f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g₁ : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {f : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : α) => β) _x) (sInfHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_right

/- warning: complete_lattice_hom.cancel_left -> CompleteLatticeHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : β) => γ) _x) (sInfHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.tosInfHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_leftₓ'. -/
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left

end CompleteLatticeHom

/-! ### Dual homs -/


namespace sSupHom

variable [SupSet α] [SupSet β] [SupSet γ]

/- warning: Sup_hom.dual -> sSupHom.dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual sSupHom.dualₓ'. -/
/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sSupHom α β ≃ sInfHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_Sup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_Inf'⟩
  left_inv f := sSupHom.ext fun a => rfl
  right_inv f := sInfHom.ext fun a => rfl
#align Sup_hom.dual sSupHom.dual

/- warning: Sup_hom.dual_id -> sSupHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) => (sSupHom.{u1, u1} α α _inst_1 _inst_1) -> (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (sSupHom.dual.{u1, u1} α α _inst_1 _inst_1) (sSupHom.id.{u1} α _inst_1)) (sInfHom.id.{u1} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u1} α α _inst_1 _inst_1) => sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1)) (sSupHom.id.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1))) (sSupHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sSupHom.{u1, u1} α α _inst_1 _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u1} α α _inst_1 _inst_1) => sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (sSupHom.{u1, u1} α α _inst_1 _inst_1) (sInfHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1))) (sSupHom.dual.{u1, u1} α α _inst_1 _inst_1) (sSupHom.id.{u1} α _inst_1)) (sInfHom.id.{u1} (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_id sSupHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (sSupHom.id α).dual = sInfHom.id _ :=
  rfl
#align Sup_hom.dual_id sSupHom.dual_id

/- warning: Sup_hom.dual_comp -> sSupHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (g : sSupHom.{u2, u3} β γ _inst_2 _inst_3) (f : sSupHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) => (sSupHom.{u1, u3} α γ _inst_1 _inst_3) -> (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (sSupHom.dual.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (sInfHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) => (sSupHom.{u2, u3} β γ _inst_2 _inst_3) -> (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (sSupHom.dual.{u2, u3} β γ _inst_2 _inst_3) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) => (sSupHom.{u1, u2} α β _inst_1 _inst_2) -> (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (sSupHom.dual.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (g : sSupHom.{u3, u2} β γ _inst_2 _inst_3) (f : sSupHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u2} α γ _inst_1 _inst_3) => sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3))) (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : sSupHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u2} α γ _inst_1 _inst_3) => sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3))) (sSupHom.dual.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (sInfHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3))) (sSupHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : sSupHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u3, u2} β γ _inst_2 _inst_3) => sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3))) (sSupHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sSupHom.{u1, u3} α β _inst_1 _inst_2) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2))) (sSupHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : sSupHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u3} α β _inst_1 _inst_2) => sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sSupHom.{u1, u3} α β _inst_1 _inst_2) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2))) (sSupHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_comp sSupHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : sSupHom β γ) (f : sSupHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Sup_hom.dual_comp sSupHom.dual_comp

#print sSupHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : sSupHom.dual.symm (sInfHom.id _) = sSupHom.id α :=
  rfl
#align Sup_hom.symm_dual_id sSupHom.symm_dual_id
-/

/- warning: Sup_hom.symm_dual_comp -> sSupHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (g : sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (f : sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)), Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u1, u3} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u1, u3} α γ _inst_1 _inst_3)) => (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) -> (sSupHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.dual.{u1, u3} α γ _inst_1 _inst_3)) (sInfHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3) g f)) (sSupHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u2, u3} β γ _inst_2 _inst_3)) => (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) -> (sSupHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} β γ _inst_2 _inst_3) (sInfHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (sSupHom.dual.{u2, u3} β γ _inst_2 _inst_3)) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (sSupHom.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (sSupHom.{u1, u2} α β _inst_1 _inst_2)) => (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) -> (sSupHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (sSupHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} α β _inst_1 _inst_2) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (sSupHom.dual.{u1, u2} α β _inst_1 _inst_2)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (g : sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (f : sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.{u1, u2} α γ _inst_1 _inst_3)) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (fun (_x : sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => sSupHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (sInfHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) g f)) (sSupHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.{u3, u2} β γ _inst_2 _inst_3)) (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (fun (_x : sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) => sSupHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u3, u2} β γ _inst_2 _inst_3) (sInfHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (sSupHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (sSupHom.{u1, u3} α β _inst_1 _inst_2)) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (fun (_x : sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) => sSupHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (sSupHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sSupHom.{u1, u3} α β _inst_1 _inst_2) (sInfHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (sSupHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align Sup_hom.symm_dual_comp sSupHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : sInfHom βᵒᵈ γᵒᵈ) (f : sInfHom αᵒᵈ βᵒᵈ) :
    sSupHom.dual.symm (g.comp f) = (sSupHom.dual.symm g).comp (sSupHom.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp sSupHom.symm_dual_comp

end sSupHom

namespace sInfHom

variable [InfSet α] [InfSet β] [InfSet γ]

/- warning: Inf_hom.dual -> sInfHom.dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual sInfHom.dualₓ'. -/
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : sInfHom α β ≃ sSupHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_Sup' := fun _ => congr_arg toDual (map_sInf f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_Inf' := fun _ => congr_arg ofDual (map_sSup f _) }
  left_inv f := sInfHom.ext fun a => rfl
  right_inv f := sSupHom.ext fun a => rfl
#align Inf_hom.dual sInfHom.dual

/- warning: Inf_hom.dual_id -> sInfHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) => (sInfHom.{u1, u1} α α _inst_1 _inst_1) -> (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (sInfHom.dual.{u1, u1} α α _inst_1 _inst_1) (sInfHom.id.{u1} α _inst_1)) (sSupHom.id.{u1} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u1} α α _inst_1 _inst_1) => sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1)) (sInfHom.id.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1))) (sInfHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : sInfHom.{u1, u1} α α _inst_1 _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u1} α α _inst_1 _inst_1) => sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (sInfHom.{u1, u1} α α _inst_1 _inst_1) (sSupHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1))) (sInfHom.dual.{u1, u1} α α _inst_1 _inst_1) (sInfHom.id.{u1} α _inst_1)) (sSupHom.id.{u1} (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_id sInfHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (sInfHom.id α).dual = sSupHom.id _ :=
  rfl
#align Inf_hom.dual_id sInfHom.dual_id

/- warning: Inf_hom.dual_comp -> sInfHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (g : sInfHom.{u2, u3} β γ _inst_2 _inst_3) (f : sInfHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) => (sInfHom.{u1, u3} α γ _inst_1 _inst_3) -> (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (sInfHom.dual.{u1, u3} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (sSupHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) => (sInfHom.{u2, u3} β γ _inst_2 _inst_3) -> (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (sInfHom.dual.{u2, u3} β γ _inst_2 _inst_3) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) => (sInfHom.{u1, u2} α β _inst_1 _inst_2) -> (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (sInfHom.dual.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (g : sInfHom.{u3, u2} β γ _inst_2 _inst_3) (f : sInfHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u2} α γ _inst_1 _inst_3) => sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3))) (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : sInfHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u2} α γ _inst_1 _inst_3) => sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3))) (sInfHom.dual.{u1, u2} α γ _inst_1 _inst_3) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (sSupHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3))) (sInfHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : sInfHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u3, u2} β γ _inst_2 _inst_3) => sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3))) (sInfHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sInfHom.{u1, u3} α β _inst_1 _inst_2) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2))) (sInfHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : sInfHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sInfHom.{u1, u3} α β _inst_1 _inst_2) => sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sInfHom.{u1, u3} α β _inst_1 _inst_2) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2))) (sInfHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_comp sInfHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : sInfHom β γ) (f : sInfHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Inf_hom.dual_comp sInfHom.dual_comp

#print sInfHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : sInfHom.dual.symm (sSupHom.id _) = sInfHom.id α :=
  rfl
#align Inf_hom.symm_dual_id sInfHom.symm_dual_id
-/

/- warning: Inf_hom.symm_dual_comp -> sInfHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (g : sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (f : sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)), Eq.{max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u1, u3} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u1, u3} α γ _inst_1 _inst_3)) => (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) -> (sInfHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (sInfHom.{u1, u3} α γ _inst_1 _inst_3) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.dual.{u1, u3} α γ _inst_1 _inst_3)) (sSupHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3) g f)) (sInfHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u2, u3} β γ _inst_2 _inst_3)) => (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) -> (sInfHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u2, u3} β γ _inst_2 _inst_3) (sSupHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (sInfHom.dual.{u2, u3} β γ _inst_2 _inst_3)) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (sInfHom.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (sInfHom.{u1, u2} α β _inst_1 _inst_2)) => (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) -> (sInfHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (sInfHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (sInfHom.{u1, u2} α β _inst_1 _inst_2) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (sInfHom.dual.{u1, u2} α β _inst_1 _inst_2)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (g : sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (f : sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.{u1, u2} α γ _inst_1 _inst_3)) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (fun (_x : sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => sInfHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (sInfHom.{u1, u2} α γ _inst_1 _inst_3) (sSupHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (sSupHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) g f)) (sInfHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.{u3, u2} β γ _inst_2 _inst_3)) (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (fun (_x : sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) => sInfHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (sInfHom.{u3, u2} β γ _inst_2 _inst_3) (sSupHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (sInfHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (sInfHom.{u1, u3} α β _inst_1 _inst_2)) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (fun (_x : sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) => sInfHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (sInfHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (sInfHom.{u1, u3} α β _inst_1 _inst_2) (sSupHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (sInfHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align Inf_hom.symm_dual_comp sInfHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : sSupHom βᵒᵈ γᵒᵈ) (f : sSupHom αᵒᵈ βᵒᵈ) :
    sInfHom.dual.symm (g.comp f) = (sInfHom.dual.symm g).comp (sInfHom.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp sInfHom.symm_dual_comp

end sInfHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

#print CompleteLatticeHom.dual /-
/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.tosSupHom.dual, f.map_Inf'⟩
  invFun f := ⟨f.tosSupHom.dual, f.map_Inf'⟩
  left_inv f := ext fun a => rfl
  right_inv f := ext fun a => rfl
#align complete_lattice_hom.dual CompleteLatticeHom.dual
-/

#print CompleteLatticeHom.dual_id /-
@[simp]
theorem dual_id : (CompleteLatticeHom.id α).dual = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.dual_id CompleteLatticeHom.dual_id
-/

/- warning: complete_lattice_hom.dual_comp -> CompleteLatticeHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (g : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3))) => (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) -> (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3))) (CompleteLatticeHom.dual.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (CompleteLatticeHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3))) => (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) -> (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3))) (CompleteLatticeHom.dual.{u2, u3} β γ _inst_2 _inst_3) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2))) => (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) -> (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2))) (CompleteLatticeHom.dual.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (g : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (f : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.dual.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) => CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2))) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) => CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2))) (CompleteLatticeHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.dual_comp CompleteLatticeHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : CompleteLatticeHom β γ) (f : CompleteLatticeHom α β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align complete_lattice_hom.dual_comp CompleteLatticeHom.dual_comp

#print CompleteLatticeHom.symm_dual_id /-
@[simp]
theorem symm_dual_id :
    CompleteLatticeHom.dual.symm (CompleteLatticeHom.id _) = CompleteLatticeHom.id α :=
  rfl
#align complete_lattice_hom.symm_dual_id CompleteLatticeHom.symm_dual_id
-/

/- warning: complete_lattice_hom.symm_dual_comp -> CompleteLatticeHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (g : CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) (f : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)), Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3)) => (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) -> (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.dual.{u1, u3} α γ _inst_1 _inst_3)) (CompleteLatticeHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3) g f)) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3)) => (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) -> (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.completeLattice.{u2} β _inst_2) (OrderDual.completeLattice.{u3} γ _inst_3)) (CompleteLatticeHom.dual.{u2, u3} β γ _inst_2 _inst_3)) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)) (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)) (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)) => (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)) -> (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)) (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} β _inst_2)) (CompleteLatticeHom.dual.{u1, u2} α β _inst_1 _inst_2)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (g : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (f : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3)) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (fun (_x : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) g f)) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3)) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (fun (_x : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2)) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (fun (_x : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.808 : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) => CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.symm_dual_comp CompleteLatticeHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : CompleteLatticeHom βᵒᵈ γᵒᵈ) (f : CompleteLatticeHom αᵒᵈ βᵒᵈ) :
    CompleteLatticeHom.dual.symm (g.comp f) =
      (CompleteLatticeHom.dual.symm g).comp (CompleteLatticeHom.dual.symm f) :=
  rfl
#align complete_lattice_hom.symm_dual_comp CompleteLatticeHom.symm_dual_comp

end CompleteLatticeHom

/-! ### Concrete homs -/


namespace CompleteLatticeHom

/- warning: complete_lattice_hom.set_preimage -> CompleteLatticeHom.setPreimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimageₓ'. -/
/-- `set.preimage` as a complete lattice homomorphism.

See also `Sup_hom.set_image`. -/
def setPreimage (f : α → β) : CompleteLatticeHom (Set β) (Set α)
    where
  toFun := preimage f
  map_Sup' s := preimage_sUnion.trans <| by simp only [Set.sSup_eq_sUnion, Set.sUnion_image]
  map_Inf' s := preimage_sInter.trans <| by simp only [Set.sInf_eq_sInter, Set.sInter_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage

/- warning: complete_lattice_hom.coe_set_preimage -> CompleteLatticeHom.coe_setPreimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u2) (succ u1)} ((Set.{u2} β) -> (Set.{u1} α)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (fun (_x : CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) => (Set.{u2} β) -> (Set.{u1} α)) (CompleteLatticeHom.hasCoeToFun.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f)) (Set.preimage.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Set.{u1} β), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Set.{u1} β) => Set.{u2} α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (fun (_x : Set.{u1} β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Set.{u1} β) => Set.{u2} α) _x) (sInfHomClass.toFunLike.{max u2 u1, u1, u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (Set.{u2} α) (CompleteLattice.toInfSet.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))) (CompleteLattice.toInfSet.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (CompleteLatticeHomClass.tosInfHomClass.{max u2 u1, u1, u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))) (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (CompleteLatticeHom.setPreimage.{u2, u1} α β f)) (Set.preimage.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimageₓ'. -/
@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimage

/- warning: complete_lattice_hom.set_preimage_apply -> CompleteLatticeHom.setPreimage_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (fun (_x : CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) => (Set.{u2} β) -> (Set.{u1} α)) (CompleteLatticeHom.hasCoeToFun.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f) s) (Set.preimage.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Set.{u2} β) => Set.{u1} α) s) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (fun (_x : Set.{u2} β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Set.{u2} β) => Set.{u1} α) _x) (sInfHomClass.toFunLike.{max u1 u2, u2, u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (Set.{u1} α) (CompleteLattice.toInfSet.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))) (CompleteLattice.toInfSet.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (CompleteLatticeHomClass.tosInfHomClass.{max u1 u2, u2, u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))) (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f) s) (Set.preimage.{u1, u2} α β f s)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.set_preimage_apply CompleteLatticeHom.setPreimage_applyₓ'. -/
@[simp]
theorem setPreimage_apply (f : α → β) (s : Set β) : setPreimage f s = s.Preimage f :=
  rfl
#align complete_lattice_hom.set_preimage_apply CompleteLatticeHom.setPreimage_apply

/- warning: complete_lattice_hom.set_preimage_id -> CompleteLatticeHom.setPreimage_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (CompleteLatticeHom.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u1} α α (id.{succ u1} α)) (CompleteLatticeHom.id.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (CompleteLatticeHom.{u1, u1} (Set.{u1} α) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u1} α α (id.{succ u1} α)) (CompleteLatticeHom.id.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.set_preimage_id CompleteLatticeHom.setPreimage_idₓ'. -/
@[simp]
theorem setPreimage_id : setPreimage (id : α → α) = CompleteLatticeHom.id _ :=
  rfl
#align complete_lattice_hom.set_preimage_id CompleteLatticeHom.setPreimage_id

/- warning: complete_lattice_hom.set_preimage_comp -> CompleteLatticeHom.setPreimage_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} (g : β -> γ) (f : α -> β), Eq.{max (succ u3) (succ u1)} (CompleteLatticeHom.{u3, u1} (Set.{u3} γ) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u3} α γ (Function.comp.{succ u1, succ u2, succ u3} α β γ g f)) (CompleteLatticeHom.comp.{u3, u2, u1} (Set.{u3} γ) (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} γ) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} γ) (Set.completeBooleanAlgebra.{u3} γ)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f) (CompleteLatticeHom.setPreimage.{u2, u3} β γ g))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u1}} {γ : Type.{u2}} (g : β -> γ) (f : α -> β), Eq.{max (succ u3) (succ u2)} (CompleteLatticeHom.{u2, u3} (Set.{u2} γ) (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} γ) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} γ) (Set.instCompleteBooleanAlgebraSet.{u2} γ)))) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α))))) (CompleteLatticeHom.setPreimage.{u3, u2} α γ (Function.comp.{succ u3, succ u1, succ u2} α β γ g f)) (CompleteLatticeHom.comp.{u2, u1, u3} (Set.{u2} γ) (Set.{u1} β) (Set.{u3} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} γ) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} γ) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} γ) (Set.instCompleteBooleanAlgebraSet.{u2} γ)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u3} (Set.{u3} α) (CompleteDistribLattice.toCoframe.{u3} (Set.{u3} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u3} (Set.{u3} α) (Set.instCompleteBooleanAlgebraSet.{u3} α)))) (CompleteLatticeHom.setPreimage.{u3, u1} α β f) (CompleteLatticeHom.setPreimage.{u1, u2} β γ g))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.set_preimage_comp CompleteLatticeHom.setPreimage_compₓ'. -/
-- This lemma can't be `simp` because `g ∘ f` matches anything (`id ∘ f = f` synctatically)
theorem setPreimage_comp (g : β → γ) (f : α → β) :
    setPreimage (g ∘ f) = (setPreimage f).comp (setPreimage g) :=
  rfl
#align complete_lattice_hom.set_preimage_comp CompleteLatticeHom.setPreimage_comp

end CompleteLatticeHom

/- warning: set.image_Sup -> Set.image_sSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (SupSet.sSup.{u1} (Set.{u1} α) (Set.hasSup.{u1} α) s)) (SupSet.sSup.{u2} (Set.{u2} β) (Set.hasSup.{u2} β) (Set.image.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.image.{u1, u2} α β f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} (s : Set.{u2} (Set.{u2} α)), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (SupSet.sSup.{u2} (Set.{u2} α) (Set.instSupSetSet.{u2} α) s)) (SupSet.sSup.{u1} (Set.{u1} β) (Set.instSupSetSet.{u1} β) (Set.image.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.image.{u2, u1} α β f) s))
Case conversion may be inaccurate. Consider using '#align set.image_Sup Set.image_sSupₓ'. -/
theorem Set.image_sSup {f : α → β} (s : Set (Set α)) : f '' sSup s = sSup (image f '' s) :=
  by
  ext b
  simp only [Sup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_Union]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
#align set.image_Sup Set.image_sSup

/- warning: Sup_hom.set_image -> sSupHom.setImage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (sSupHom.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.hasSup.{u1} α) (Set.hasSup.{u2} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (sSupHom.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.instSupSetSet.{u1} α) (Set.instSupSetSet.{u2} β))
Case conversion may be inaccurate. Consider using '#align Sup_hom.set_image sSupHom.setImageₓ'. -/
/-- Using `set.image`, a function between types yields a `Sup_hom` between their lattices of
subsets.

See also `complete_lattice_hom.set_preimage`. -/
@[simps]
def sSupHom.setImage (f : α → β) : sSupHom (Set α) (Set β)
    where
  toFun := image f
  map_Sup' := Set.image_sSup
#align Sup_hom.set_image sSupHom.setImage

#print Equiv.toOrderIsoSet /-
/-- An equivalence of types yields an order isomorphism between their lattices of subsets. -/
@[simps]
def Equiv.toOrderIsoSet (e : α ≃ β) : Set α ≃o Set β
    where
  toFun := image e
  invFun := image e.symm
  left_inv s := by simp only [← image_comp, Equiv.symm_comp_self, id.def, image_id']
  right_inv s := by simp only [← image_comp, Equiv.self_comp_symm, id.def, image_id']
  map_rel_iff' s t :=
    ⟨fun h => by simpa using @monotone_image _ _ e.symm _ _ h, fun h => monotone_image h⟩
#align equiv.to_order_iso_set Equiv.toOrderIsoSet
-/

variable [CompleteLattice α] (x : α × α)

/- warning: sup_Sup_hom -> supsSupHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align sup_Sup_hom supsSupHomₓ'. -/
/-- The map `(a, b) ↦ a ⊔ b` as a `Sup_hom`. -/
def supsSupHom : sSupHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_Sup' s := by simp_rw [Prod.fst_sSup, Prod.snd_sSup, sSup_image, iSup_sup_eq]
#align sup_Sup_hom supsSupHom

/- warning: inf_Inf_hom -> infsInfHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align inf_Inf_hom infsInfHomₓ'. -/
/-- The map `(a, b) ↦ a ⊓ b` as an `Inf_hom`. -/
def infsInfHom : sInfHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_Inf' s := by simp_rw [Prod.fst_sInf, Prod.snd_sInf, sInf_image, iInf_inf_eq]
#align inf_Inf_hom infsInfHom

/- warning: sup_Sup_hom_apply -> supsSupHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (fun (_x : sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) => (Prod.{u1, u1} α α) -> α) (sSupHom.hasCoeToFun.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (supsSupHom.{u1} α _inst_1) x) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : Prod.{u1, u1} α α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (_x : Prod.{u1, u1} α α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : Prod.{u1, u1} α α) => α) _x) (sSupHomClass.toFunLike.{u1, u1, u1} (sSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1) (sSupHom.instSSupHomClassSSupHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1))) (supsSupHom.{u1} α _inst_1) x) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
Case conversion may be inaccurate. Consider using '#align sup_Sup_hom_apply supsSupHom_applyₓ'. -/
@[simp, norm_cast]
theorem supsSupHom_apply : supsSupHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supsSupHom_apply

/- warning: inf_Inf_hom_apply -> infsInfHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (fun (_x : sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) => (Prod.{u1, u1} α α) -> α) (sInfHom.hasCoeToFun.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (infsInfHom.{u1} α _inst_1) x) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Prod.{u1, u1} α α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (_x : Prod.{u1, u1} α α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.374 : Prod.{u1, u1} α α) => α) _x) (sInfHomClass.toFunLike.{u1, u1, u1} (sInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1) (sInfHom.instSInfHomClassSInfHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1))) (infsInfHom.{u1} α _inst_1) x) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
Case conversion may be inaccurate. Consider using '#align inf_Inf_hom_apply infsInfHom_applyₓ'. -/
@[simp, norm_cast]
theorem infsInfHom_apply : infsInfHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infsInfHom_apply

