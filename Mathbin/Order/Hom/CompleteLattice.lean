/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.hom.complete_lattice
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.CompleteLattice
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

#print SupₛHom /-
/-- The type of `⨆`-preserving functions from `α` to `β`. -/
structure SupₛHom (α β : Type _) [SupSet α] [SupSet β] where
  toFun : α → β
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align Sup_hom SupₛHom
-/

#print InfₛHom /-
/-- The type of `⨅`-preserving functions from `α` to `β`. -/
structure InfₛHom (α β : Type _) [InfSet α] [InfSet β] where
  toFun : α → β
  map_Inf' (s : Set α) : to_fun (infₛ s) = infₛ (to_fun '' s)
#align Inf_hom InfₛHom
-/

#print FrameHom /-
/-- The type of frame homomorphisms from `α` to `β`. They preserve finite meets and arbitrary joins.
-/
structure FrameHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfTopHom α β where
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align frame_hom FrameHom
-/

#print CompleteLatticeHom /-
/-- The type of complete lattice homomorphisms from `α` to `β`. -/
structure CompleteLatticeHom (α β : Type _) [CompleteLattice α] [CompleteLattice β] extends
  InfₛHom α β where
  map_Sup' (s : Set α) : to_fun (supₛ s) = supₛ (to_fun '' s)
#align complete_lattice_hom CompleteLatticeHom
-/

section

#print SupₛHomClass /-
/-- `Sup_hom_class F α β` states that `F` is a type of `⨆`-preserving morphisms.

You should extend this class when you extend `Sup_hom`. -/
class SupₛHomClass (F : Type _) (α β : outParam <| Type _) [SupSet α] [SupSet β] extends
  FunLike F α fun _ => β where
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align Sup_hom_class SupₛHomClass
-/

#print InfₛHomClass /-
/-- `Inf_hom_class F α β` states that `F` is a type of `⨅`-preserving morphisms.

You should extend this class when you extend `Inf_hom`. -/
class InfₛHomClass (F : Type _) (α β : outParam <| Type _) [InfSet α] [InfSet β] extends
  FunLike F α fun _ => β where
  map_infₛ (f : F) (s : Set α) : f (infₛ s) = infₛ (f '' s)
#align Inf_hom_class InfₛHomClass
-/

#print FrameHomClass /-
/-- `frame_hom_class F α β` states that `F` is a type of frame morphisms. They preserve `⊓` and `⨆`.

You should extend this class when you extend `frame_hom`. -/
class FrameHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfTopHomClass F α β where
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align frame_hom_class FrameHomClass
-/

#print CompleteLatticeHomClass /-
/-- `complete_lattice_hom_class F α β` states that `F` is a type of complete lattice morphisms.

You should extend this class when you extend `complete_lattice_hom`. -/
class CompleteLatticeHomClass (F : Type _) (α β : outParam <| Type _) [CompleteLattice α]
  [CompleteLattice β] extends InfₛHomClass F α β where
  map_supₛ (f : F) (s : Set α) : f (supₛ s) = supₛ (f '' s)
#align complete_lattice_hom_class CompleteLatticeHomClass
-/

end

export SupₛHomClass (map_supₛ)

export InfₛHomClass (map_infₛ)

attribute [simp] map_Sup map_Inf

/- warning: map_supr -> map_supᵢ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupₛHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (supᵢ.{u2, u4} α _inst_1 ι (fun (i : ι) => g i))) (supᵢ.{u3, u4} β _inst_2 ι (fun (i : ι) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : SupSet.{u4} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupₛHomClass.{u2, u4, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) (supᵢ.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (supᵢ.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (supᵢ.{u3, u1} β _inst_2 ι (fun (i : ι) => FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (g i)))
Case conversion may be inaccurate. Consider using '#align map_supr map_supᵢₓ'. -/
theorem map_supᵢ [SupSet α] [SupSet β] [SupₛHomClass F α β] (f : F) (g : ι → α) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by rw [supᵢ, supᵢ, map_Sup, Set.range_comp]
#align map_supr map_supᵢ

/- warning: map_supr₂ -> map_supᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} {κ : ι -> Sort.{u5}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupₛHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (supᵢ.{u2, u4} α _inst_1 ι (fun (i : ι) => supᵢ.{u2, u5} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (supᵢ.{u3, u4} β _inst_2 ι (fun (i : ι) => supᵢ.{u3, u5} β _inst_2 (κ i) (fun (j : κ i) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (SupₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i j))))
but is expected to have type
  forall {F : Type.{u3}} {α : Type.{u5}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SupSet.{u5} α] [_inst_2 : SupSet.{u4} β] [_inst_3 : SupₛHomClass.{u3, u5, u4} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u4} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) (supᵢ.{u5, u2} α _inst_1 ι (fun (i : ι) => supᵢ.{u5, u1} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (FunLike.coe.{succ u3, succ u5, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{u3, u5, u4} F α β _inst_1 _inst_2 _inst_3) f (supᵢ.{u5, u2} α _inst_1 ι (fun (i : ι) => supᵢ.{u5, u1} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (supᵢ.{u4, u2} β _inst_2 ι (fun (i : ι) => supᵢ.{u4, u1} β _inst_2 (κ i) (fun (j : κ i) => FunLike.coe.{succ u3, succ u5, succ u4} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{u3, u5, u4} F α β _inst_1 _inst_2 _inst_3) f (g i j))))
Case conversion may be inaccurate. Consider using '#align map_supr₂ map_supᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_supᵢ₂ [SupSet α] [SupSet β] [SupₛHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨆ (i) (j), g i j) = ⨆ (i) (j), f (g i j) := by simp_rw [map_supᵢ]
#align map_supr₂ map_supᵢ₂

/- warning: map_infi -> map_infᵢ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u4}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfₛHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (InfₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (infᵢ.{u2, u4} α _inst_1 ι (fun (i : ι) => g i))) (infᵢ.{u3, u4} β _inst_2 ι (fun (i : ι) => coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (InfₛHomClass.toFunLike.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3)) f (g i)))
but is expected to have type
  forall {F : Type.{u2}} {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : InfSet.{u4} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfₛHomClass.{u2, u4, u3} F α β _inst_1 _inst_2] (f : F) (g : ι -> α), Eq.{succ u3} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) (infᵢ.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (infᵢ.{u4, u1} α _inst_1 ι (fun (i : ι) => g i))) (infᵢ.{u3, u1} β _inst_2 ι (fun (i : ι) => FunLike.coe.{succ u2, succ u4, succ u3} F α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{u2, u4, u3} F α β _inst_1 _inst_2 _inst_3) f (g i)))
Case conversion may be inaccurate. Consider using '#align map_infi map_infᵢₓ'. -/
theorem map_infᵢ [InfSet α] [InfSet β] [InfₛHomClass F α β] (f : F) (g : ι → α) :
    f (⨅ i, g i) = ⨅ i, f (g i) := by rw [infᵢ, infᵢ, map_Inf, Set.range_comp]
#align map_infi map_infᵢ

/- warning: map_infi₂ clashes with map_infi -> map_infᵢ
warning: map_infi₂ -> map_infᵢ is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u_1}} {α : Type.{u_2}} {β : Type.{u_3}} {ι : Sort.{u_6}} {κ : ι -> Sort.{u_7}} [_inst_1 : InfSet.{u_2} α] [_inst_2 : InfSet.{u_3} β] [_inst_3 : InfₛHomClass.{u_1, u_2, u_3} F α β _inst_1 _inst_2] (f : F) (g : forall (i : ι), (κ i) -> α), Eq.{succ u_3} β (coeFn.{succ u_1, max (succ u_2) (succ u_3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u_1, succ u_2, succ u_3} F α (fun (_x : α) => β) (InfₛHomClass.toFunLike.{u_1, u_2, u_3} F α β _inst_1 _inst_2 _inst_3)) f (infᵢ.{u_2, u_6} α _inst_1 ι (fun (i : ι) => infᵢ.{u_2, u_7} α _inst_1 (κ i) (fun (j : κ i) => g i j)))) (infᵢ.{u_3, u_6} β _inst_2 ι (fun (i : ι) => infᵢ.{u_3, u_7} β _inst_2 (κ i) (fun (j : κ i) => coeFn.{succ u_1, max (succ u_2) (succ u_3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u_1, succ u_2, succ u_3} F α (fun (_x : α) => β) (InfₛHomClass.toFunLike.{u_1, u_2, u_3} F α β _inst_1 _inst_2 _inst_3)) f (g i j))))
but is expected to have type
  forall {F : Type.{u_3}} {α : Type.{u_1}} {β : Type.{u_2}} {ι : Sort.{u_4}} [κ : InfSet.{u_1} α] [_inst_1 : InfSet.{u_2} β] [_inst_2 : InfₛHomClass.{u_3, u_1, u_2} F α β κ _inst_1] (_inst_3 : F) (f : ι -> α), Eq.{succ u_2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) (infᵢ.{u_1, u_4} α κ ι (fun (i : ι) => f i))) (FunLike.coe.{succ u_3, succ u_1, succ u_2} F α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (InfₛHomClass.toFunLike.{u_3, u_1, u_2} F α β κ _inst_1 _inst_2) _inst_3 (infᵢ.{u_1, u_4} α κ ι (fun (i : ι) => f i))) (infᵢ.{u_2, u_4} β _inst_1 ι (fun (i : ι) => FunLike.coe.{succ u_3, succ u_1, succ u_2} F α (fun (a : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (InfₛHomClass.toFunLike.{u_3, u_1, u_2} F α β κ _inst_1 _inst_2) _inst_3 (f i)))
Case conversion may be inaccurate. Consider using '#align map_infi₂ map_infᵢₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem map_infᵢ [InfSet α] [InfSet β] [InfₛHomClass F α β] (f : F) (g : ∀ i, κ i → α) :
    f (⨅ (i) (j), g i j) = ⨅ (i) (j), f (g i j) := by simp_rw [map_infᵢ]
#align map_infi₂ map_infᵢ

/- warning: Sup_hom_class.to_sup_bot_hom_class -> SupₛHomClass.toSupBotHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : SupₛHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))], SupBotHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeSup.toHasSup.{u3} β (Lattice.toSemilatticeSup.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toHasBot.{u2} α _inst_1) (CompleteLattice.toHasBot.{u3} β _inst_2)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : CompleteLattice.{u2} α} {_inst_2 : CompleteLattice.{u3} β} [_inst_3 : SupₛHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)], SupBotHomClass.{u1, u2, u3} F α β (SemilatticeSup.toHasSup.{u2} α (Lattice.toSemilatticeSup.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeSup.toHasSup.{u3} β (Lattice.toSemilatticeSup.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toBot.{u2} α _inst_1) (CompleteLattice.toBot.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align Sup_hom_class.to_sup_bot_hom_class SupₛHomClass.toSupBotHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) SupₛHomClass.toSupBotHomClass [CompleteLattice α] [CompleteLattice β]
    [SupₛHomClass F α β] : SupBotHomClass F α β :=
  {
    ‹SupₛHomClass F α
        β› with
    map_sup := fun f a b => by rw [← supₛ_pair, map_Sup, Set.image_pair, supₛ_pair]
    map_bot := fun f => by rw [← supₛ_empty, map_Sup, Set.image_empty, supₛ_empty] }
#align Sup_hom_class.to_sup_bot_hom_class SupₛHomClass.toSupBotHomClass

/- warning: Inf_hom_class.to_inf_top_hom_class -> InfₛHomClass.toInfTopHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : InfₛHomClass.{u1, u2, u3} F α β (CompleteSemilatticeInf.toHasInf.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))], InfTopHomClass.{u1, u2, u3} F α β (SemilatticeInf.toHasInf.{u2} α (Lattice.toSemilatticeInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1))) (SemilatticeInf.toHasInf.{u3} β (Lattice.toSemilatticeInf.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2))) (CompleteLattice.toHasTop.{u2} α _inst_1) (CompleteLattice.toHasTop.{u3} β _inst_2)
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : CompleteLattice.{u2} α} {_inst_2 : CompleteLattice.{u3} β} [_inst_3 : InfₛHomClass.{u1, u2, u3} F α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2)], InfTopHomClass.{u1, u2, u3} F α β (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toHasInf.{u3} β (CompleteLattice.toLattice.{u3} β _inst_2)) (CompleteLattice.toTop.{u2} α _inst_1) (CompleteLattice.toTop.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align Inf_hom_class.to_inf_top_hom_class InfₛHomClass.toInfTopHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) InfₛHomClass.toInfTopHomClass [CompleteLattice α] [CompleteLattice β]
    [InfₛHomClass F α β] : InfTopHomClass F α β :=
  {
    ‹InfₛHomClass F α
        β› with
    map_inf := fun f a b => by rw [← infₛ_pair, map_Inf, Set.image_pair, infₛ_pair]
    map_top := fun f => by rw [← infₛ_empty, map_Inf, Set.image_empty, infₛ_empty] }
#align Inf_hom_class.to_inf_top_hom_class InfₛHomClass.toInfTopHomClass

/- warning: frame_hom_class.to_Sup_hom_class -> FrameHomClass.toSupₛHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : FrameHomClass.{u1, u2, u3} F α β _inst_1 _inst_2], SupₛHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : CompleteLattice.{u2} α} {_inst_2 : CompleteLattice.{u3} β} [_inst_3 : FrameHomClass.{u1, u2, u3} F α β _inst_1 _inst_2], SupₛHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align frame_hom_class.to_Sup_hom_class FrameHomClass.toSupₛHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toSupₛHomClass [CompleteLattice α] [CompleteLattice β]
    [FrameHomClass F α β] : SupₛHomClass F α β :=
  { ‹FrameHomClass F α β› with }
#align frame_hom_class.to_Sup_hom_class FrameHomClass.toSupₛHomClass

#print FrameHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) FrameHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [FrameHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹FrameHomClass F α β›, SupₛHomClass.toSupBotHomClass with }
#align frame_hom_class.to_bounded_lattice_hom_class FrameHomClass.toBoundedLatticeHomClass
-/

#print CompleteLatticeHomClass.toFrameHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toFrameHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : FrameHomClass F α β :=
  { ‹CompleteLatticeHomClass F α β›, InfₛHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_frame_hom_class CompleteLatticeHomClass.toFrameHomClass
-/

#print CompleteLatticeHomClass.toBoundedLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) CompleteLatticeHomClass.toBoundedLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [CompleteLatticeHomClass F α β] : BoundedLatticeHomClass F α β :=
  { SupₛHomClass.toSupBotHomClass, InfₛHomClass.toInfTopHomClass with }
#align complete_lattice_hom_class.to_bounded_lattice_hom_class CompleteLatticeHomClass.toBoundedLatticeHomClass
-/

/- warning: order_iso_class.to_Sup_hom_class -> OrderIsoClass.toSupₛHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], SupₛHomClass.{u1, u2, u3} F α β (CompleteSemilatticeSup.toHasSup.{u2} α (CompleteLattice.toCompleteSemilatticeSup.{u2} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u3} β (CompleteLattice.toCompleteSemilatticeSup.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : CompleteLattice.{u2} α} {_inst_2 : CompleteLattice.{u3} β} [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], SupₛHomClass.{u1, u2, u3} F α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Sup_hom_class OrderIsoClass.toSupₛHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toSupₛHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : SupₛHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_supₛ := fun f s =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, supₛ_le_iff, Set.ball_image_iff] }
#align order_iso_class.to_Sup_hom_class OrderIsoClass.toSupₛHomClass

/- warning: order_iso_class.to_Inf_hom_class -> OrderIsoClass.toInfₛHomClass is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], InfₛHomClass.{u1, u2, u3} F α β (CompleteSemilatticeInf.toHasInf.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} {_inst_1 : CompleteLattice.{u2} α} {_inst_2 : CompleteLattice.{u3} β} [_inst_3 : OrderIsoClass.{u1, u2, u3} F α β (Preorder.toLE.{u2} α (PartialOrder.toPreorder.{u2} α (CompleteSemilatticeInf.toPartialOrder.{u2} α (CompleteLattice.toCompleteSemilatticeInf.{u2} α _inst_1)))) (Preorder.toLE.{u3} β (PartialOrder.toPreorder.{u3} β (CompleteSemilatticeInf.toPartialOrder.{u3} β (CompleteLattice.toCompleteSemilatticeInf.{u3} β _inst_2))))], InfₛHomClass.{u1, u2, u3} F α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2)
Case conversion may be inaccurate. Consider using '#align order_iso_class.to_Inf_hom_class OrderIsoClass.toInfₛHomClassₓ'. -/
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toInfₛHomClass [CompleteLattice α] [CompleteLattice β]
    [OrderIsoClass F α β] : InfₛHomClass F α β :=
  { show OrderHomClass F α β from inferInstance with
    map_infₛ := fun f s =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_infₛ_iff, Set.ball_image_iff] }
#align order_iso_class.to_Inf_hom_class OrderIsoClass.toInfₛHomClass

#print OrderIsoClass.toCompleteLatticeHomClass /-
-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCompleteLatticeHomClass [CompleteLattice α]
    [CompleteLattice β] [OrderIsoClass F α β] : CompleteLatticeHomClass F α β :=
  { OrderIsoClass.toSupₛHomClass, OrderIsoClass.toLatticeHomClass,
    show InfₛHomClass F α β from inferInstance with }
#align order_iso_class.to_complete_lattice_hom_class OrderIsoClass.toCompleteLatticeHomClass
-/

instance [SupSet α] [SupSet β] [SupₛHomClass F α β] : CoeTC F (SupₛHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [InfSet α] [InfSet β] [InfₛHomClass F α β] : CoeTC F (InfₛHom α β) :=
  ⟨fun f => ⟨f, map_infₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [FrameHomClass F α β] : CoeTC F (FrameHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

instance [CompleteLattice α] [CompleteLattice β] [CompleteLatticeHomClass F α β] :
    CoeTC F (CompleteLatticeHom α β) :=
  ⟨fun f => ⟨f, map_supₛ f⟩⟩

/-! ### Supremum homomorphisms -/


namespace SupₛHom

variable [SupSet α]

section SupSet

variable [SupSet β] [SupSet γ] [SupSet δ]

instance : SupₛHomClass (SupₛHom α β) α β
    where
  coe := SupₛHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_supₛ := SupₛHom.map_Sup'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (SupₛHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: Sup_hom.to_fun_eq_coe -> SupₛHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {f : SupₛHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (SupₛHom.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {f : SupₛHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (SupₛHom.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align Sup_hom.to_fun_eq_coe SupₛHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : SupₛHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Sup_hom.to_fun_eq_coe SupₛHom.toFun_eq_coe

/- warning: Sup_hom.ext -> SupₛHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] {f : SupₛHom.{u1, u2} α β _inst_1 _inst_2} {g : SupₛHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] {f : SupₛHom.{u2, u1} α β _inst_1 _inst_2} {g : SupₛHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align Sup_hom.ext SupₛHom.extₓ'. -/
@[ext]
theorem ext {f g : SupₛHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Sup_hom.ext SupₛHom.ext

/- warning: Sup_hom.copy -> SupₛHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (SupₛHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u2} α β _inst_1 _inst_2)) f)) -> (SupₛHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align Sup_hom.copy SupₛHom.copyₓ'. -/
/-- Copy of a `Sup_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : SupₛHom α β) (f' : α → β) (h : f' = f) : SupₛHom α β
    where
  toFun := f'
  map_Sup' := h.symm ▸ f.map_Sup'
#align Sup_hom.copy SupₛHom.copy

/- warning: Sup_hom.coe_copy -> SupₛHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : SupₛHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) (SupₛHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_copy SupₛHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : SupₛHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Sup_hom.coe_copy SupₛHom.coe_copy

/- warning: Sup_hom.copy_eq -> SupₛHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : SupₛHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) (SupₛHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.copy_eq SupₛHom.copy_eqₓ'. -/
theorem copy_eq (f : SupₛHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Sup_hom.copy_eq SupₛHom.copy_eq

variable (α)

#print SupₛHom.id /-
/-- `id` as a `Sup_hom`. -/
protected def id : SupₛHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Sup_hom.id SupₛHom.id
-/

instance : Inhabited (SupₛHom α α) :=
  ⟨SupₛHom.id α⟩

/- warning: Sup_hom.coe_id -> SupₛHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : SupₛHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (SupₛHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (SupₛHomClass.toFunLike.{u1, u1, u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u1} α α _inst_1 _inst_1)) (SupₛHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_id SupₛHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(SupₛHom.id α) = id :=
  rfl
#align Sup_hom.coe_id SupₛHom.coe_id

variable {α}

/- warning: Sup_hom.id_apply -> SupₛHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : SupₛHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (SupₛHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (SupₛHomClass.toFunLike.{u1, u1, u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u1} α α _inst_1 _inst_1)) (SupₛHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align Sup_hom.id_apply SupₛHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : SupₛHom.id α a = a :=
  rfl
#align Sup_hom.id_apply SupₛHom.id_apply

#print SupₛHom.comp /-
/-- Composition of `Sup_hom`s as a `Sup_hom`. -/
def comp (f : SupₛHom β γ) (g : SupₛHom α β) : SupₛHom α γ
    where
  toFun := f ∘ g
  map_Sup' s := by rw [comp_apply, map_Sup, map_Sup, Set.image_image]
#align Sup_hom.comp SupₛHom.comp
-/

/- warning: Sup_hom.coe_comp -> SupₛHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (f : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (g : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : SupₛHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (SupₛHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SupₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (f : SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (g : SupₛHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u2} α γ _inst_1 _inst_3)) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SupₛHom.instSupₛHomClassSupₛHom.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_comp SupₛHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : SupₛHom β γ) (g : SupₛHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Sup_hom.coe_comp SupₛHom.coe_comp

/- warning: Sup_hom.comp_apply -> SupₛHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (f : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (g : SupₛHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : SupₛHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (SupₛHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SupₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (f : SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (g : SupₛHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u2} α γ _inst_1 _inst_3)) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SupₛHom.instSupₛHomClassSupₛHom.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_apply SupₛHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : SupₛHom β γ) (g : SupₛHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Sup_hom.comp_apply SupₛHom.comp_apply

/- warning: Sup_hom.comp_assoc -> SupₛHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] [_inst_4 : SupSet.{u4} δ] (f : SupₛHom.{u3, u4} γ δ _inst_3 _inst_4) (g : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (h : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (SupₛHom.{u1, u4} α δ _inst_1 _inst_4) (SupₛHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (SupₛHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (SupₛHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u4} γ] [_inst_4 : SupSet.{u3} δ] (f : SupₛHom.{u4, u3} γ δ _inst_3 _inst_4) (g : SupₛHom.{u2, u4} β γ _inst_2 _inst_3) (h : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α δ _inst_1 _inst_4) (SupₛHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (SupₛHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (SupₛHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (SupₛHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_assoc SupₛHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : SupₛHom γ δ) (g : SupₛHom β γ) (h : SupₛHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Sup_hom.comp_assoc SupₛHom.comp_assoc

/- warning: Sup_hom.comp_id -> SupₛHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (SupₛHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : SupₛHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) (SupₛHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (SupₛHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.comp_id SupₛHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : SupₛHom α β) : f.comp (SupₛHom.id α) = f :=
  ext fun a => rfl
#align Sup_hom.comp_id SupₛHom.comp_id

/- warning: Sup_hom.id_comp -> SupₛHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (SupₛHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] [_inst_2 : SupSet.{u1} β] (f : SupₛHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (SupₛHom.{u2, u1} α β _inst_1 _inst_2) (SupₛHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (SupₛHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align Sup_hom.id_comp SupₛHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : SupₛHom α β) : (SupₛHom.id β).comp f = f :=
  ext fun a => rfl
#align Sup_hom.id_comp SupₛHom.id_comp

/- warning: Sup_hom.cancel_right -> SupₛHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] {g₁ : SupₛHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : SupₛHom.{u2, u3} β γ _inst_2 _inst_3} {f : SupₛHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] {g₁ : SupₛHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : SupₛHom.{u3, u2} β γ _inst_2 _inst_3} {f : SupₛHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (SupₛHom.instSupₛHomClassSupₛHom.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align Sup_hom.cancel_right SupₛHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : SupₛHom β γ} {f : SupₛHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Sup_hom.cancel_right SupₛHom.cancel_right

/- warning: Sup_hom.cancel_left -> SupₛHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] {g : SupₛHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : SupₛHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : SupₛHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (SupₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] {g : SupₛHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : SupₛHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : SupₛHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (SupₛHom.instSupₛHomClassSupₛHom.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align Sup_hom.cancel_left SupₛHom.cancel_leftₓ'. -/
theorem cancel_left {g : SupₛHom β γ} {f₁ f₂ : SupₛHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Sup_hom.cancel_left SupₛHom.cancel_left

end SupSet

variable [CompleteLattice β]

instance : PartialOrder (SupₛHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Bot (SupₛHom α β) :=
  ⟨⟨fun _ => ⊥, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, supₛ_empty]
      · rw [hs.image_const, supₛ_singleton]⟩⟩

instance : OrderBot (SupₛHom α β) :=
  ⟨⊥, fun f a => bot_le⟩

/- warning: Sup_hom.coe_bot -> SupₛHom.coe_bot is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β], Eq.{succ (max u1 u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (SupₛHom.hasBot.{u1, u2} α β _inst_1 _inst_2))) (Bot.bot.{max u1 u2} (α -> β) (Pi.hasBot.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toHasBot.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SupSet.{u2} α] {_inst_2 : CompleteLattice.{u1} β}, Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (SupₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (SupₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2) (SupₛHom.instSupₛHomClassSupₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2))) (Bot.bot.{max u2 u1} (SupₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toSupSet.{u1} β _inst_2)) (SupₛHom.instBotSupₛHomToSupSet.{u2, u1} α β _inst_1 _inst_2))) (Bot.bot.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (Pi.instBotForAll.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (fun (i : α) => CompleteLattice.toBot.{u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) i) _inst_2)))
Case conversion may be inaccurate. Consider using '#align Sup_hom.coe_bot SupₛHom.coe_botₓ'. -/
@[simp]
theorem coe_bot : ⇑(⊥ : SupₛHom α β) = ⊥ :=
  rfl
#align Sup_hom.coe_bot SupₛHom.coe_bot

/- warning: Sup_hom.bot_apply -> SupₛHom.bot_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (fun (_x : SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) => α -> β) (SupₛHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (SupₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2))) (SupₛHom.hasBot.{u1, u2} α β _inst_1 _inst_2)) a) (Bot.bot.{u2} β (CompleteLattice.toHasBot.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] {_inst_2 : CompleteLattice.{u2} β} (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (SupₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (SupₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2) (SupₛHom.instSupₛHomClassSupₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2))) (Bot.bot.{max u1 u2} (SupₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toSupSet.{u2} β _inst_2)) (SupₛHom.instBotSupₛHomToSupSet.{u1, u2} α β _inst_1 _inst_2)) a) (Bot.bot.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (CompleteLattice.toBot.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) _inst_2))
Case conversion may be inaccurate. Consider using '#align Sup_hom.bot_apply SupₛHom.bot_applyₓ'. -/
@[simp]
theorem bot_apply (a : α) : (⊥ : SupₛHom α β) a = ⊥ :=
  rfl
#align Sup_hom.bot_apply SupₛHom.bot_apply

end SupₛHom

/-! ### Infimum homomorphisms -/


namespace InfₛHom

variable [InfSet α]

section InfSet

variable [InfSet β] [InfSet γ] [InfSet δ]

instance : InfₛHomClass (InfₛHom α β) α β
    where
  coe := InfₛHom.toFun
  coe_injective' f g h := by cases f <;> cases g <;> congr
  map_infₛ := InfₛHom.map_Inf'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (InfₛHom α β) fun _ => α → β :=
  FunLike.hasCoeToFun

/- warning: Inf_hom.to_fun_eq_coe -> InfₛHom.toFun_eq_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {f : InfₛHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (InfₛHom.toFun.{u1, u2} α β _inst_1 _inst_2 f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {f : InfₛHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (InfₛHom.toFun.{u2, u1} α β _inst_1 _inst_2 f) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) f)
Case conversion may be inaccurate. Consider using '#align Inf_hom.to_fun_eq_coe InfₛHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : InfₛHom α β} : f.toFun = (f : α → β) :=
  rfl
#align Inf_hom.to_fun_eq_coe InfₛHom.toFun_eq_coe

/- warning: Inf_hom.ext -> InfₛHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] {f : InfₛHom.{u1, u2} α β _inst_1 _inst_2} {g : InfₛHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] {f : InfₛHom.{u2, u1} α β _inst_1 _inst_2} {g : InfₛHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) g a)) -> (Eq.{max (succ u2) (succ u1)} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align Inf_hom.ext InfₛHom.extₓ'. -/
@[ext]
theorem ext {f g : InfₛHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align Inf_hom.ext InfₛHom.ext

/- warning: Inf_hom.copy -> InfₛHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (InfₛHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u2} α β _inst_1 _inst_2)) f)) -> (InfₛHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align Inf_hom.copy InfₛHom.copyₓ'. -/
/-- Copy of a `Inf_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : InfₛHom α β) (f' : α → β) (h : f' = f) : InfₛHom α β
    where
  toFun := f'
  map_Inf' := h.symm ▸ f.map_Inf'
#align Inf_hom.copy InfₛHom.copy

/- warning: Inf_hom.coe_copy -> InfₛHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : InfₛHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) (InfₛHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_copy InfₛHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : InfₛHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align Inf_hom.coe_copy InfₛHom.coe_copy

/- warning: Inf_hom.copy_eq -> InfₛHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : InfₛHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 _inst_2)) f)), Eq.{max (succ u2) (succ u1)} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) (InfₛHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.copy_eq InfₛHom.copy_eqₓ'. -/
theorem copy_eq (f : InfₛHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align Inf_hom.copy_eq InfₛHom.copy_eq

variable (α)

#print InfₛHom.id /-
/-- `id` as an `Inf_hom`. -/
protected def id : InfₛHom α α :=
  ⟨id, fun s => by rw [id, Set.image_id]⟩
#align Inf_hom.id InfₛHom.id
-/

instance : Inhabited (InfₛHom α α) :=
  ⟨InfₛHom.id α⟩

/- warning: Inf_hom.coe_id -> InfₛHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : InfₛHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (InfₛHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) _x) (InfₛHomClass.toFunLike.{u1, u1, u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u1} α α _inst_1 _inst_1)) (InfₛHom.id.{u1} α _inst_1)) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_id InfₛHom.coe_idₓ'. -/
@[simp]
theorem coe_id : ⇑(InfₛHom.id α) = id :=
  rfl
#align Inf_hom.coe_id InfₛHom.coe_id

variable {α}

/- warning: Inf_hom.id_apply -> InfₛHom.id_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α] (a : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : InfₛHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (InfₛHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.id.{u1} α _inst_1) a) a
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) _x) (InfₛHomClass.toFunLike.{u1, u1, u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u1} α α _inst_1 _inst_1)) (InfₛHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align Inf_hom.id_apply InfₛHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : InfₛHom.id α a = a :=
  rfl
#align Inf_hom.id_apply InfₛHom.id_apply

#print InfₛHom.comp /-
/-- Composition of `Inf_hom`s as a `Inf_hom`. -/
def comp (f : InfₛHom β γ) (g : InfₛHom α β) : InfₛHom α γ
    where
  toFun := f ∘ g
  map_Inf' s := by rw [comp_apply, map_Inf, map_Inf, Set.image_image]
#align Inf_hom.comp InfₛHom.comp
-/

/- warning: Inf_hom.coe_comp -> InfₛHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (f : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (g : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : InfₛHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (InfₛHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (InfₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (f : InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (g : InfₛHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u2} α γ _inst_1 _inst_3)) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (InfₛHom.instInfₛHomClassInfₛHom.{u3, u2} β γ _inst_2 _inst_3)) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u3} α β _inst_1 _inst_2)) g))
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_comp InfₛHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : InfₛHom β γ) (g : InfₛHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align Inf_hom.coe_comp InfₛHom.coe_comp

/- warning: Inf_hom.comp_apply -> InfₛHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (f : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (g : InfₛHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : InfₛHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (InfₛHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (InfₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (f : InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (g : InfₛHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u2} α γ _inst_1 _inst_3)) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (InfₛHom.instInfₛHomClassInfₛHom.{u3, u2} β γ _inst_2 _inst_3)) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u3} α β _inst_1 _inst_2)) g a))
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_apply InfₛHom.comp_applyₓ'. -/
@[simp]
theorem comp_apply (f : InfₛHom β γ) (g : InfₛHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl
#align Inf_hom.comp_apply InfₛHom.comp_apply

/- warning: Inf_hom.comp_assoc -> InfₛHom.comp_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] [_inst_4 : InfSet.{u4} δ] (f : InfₛHom.{u3, u4} γ δ _inst_3 _inst_4) (g : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (h : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u4)} (InfₛHom.{u1, u4} α δ _inst_1 _inst_4) (InfₛHom.comp.{u1, u2, u4} α β δ _inst_1 _inst_2 _inst_4 (InfₛHom.comp.{u2, u3, u4} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (InfₛHom.comp.{u1, u3, u4} α γ δ _inst_1 _inst_3 _inst_4 f (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g h))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u4}} {δ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u4} γ] [_inst_4 : InfSet.{u3} δ] (f : InfₛHom.{u4, u3} γ δ _inst_3 _inst_4) (g : InfₛHom.{u2, u4} β γ _inst_2 _inst_3) (h : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α δ _inst_1 _inst_4) (InfₛHom.comp.{u1, u2, u3} α β δ _inst_1 _inst_2 _inst_4 (InfₛHom.comp.{u2, u4, u3} β γ δ _inst_2 _inst_3 _inst_4 f g) h) (InfₛHom.comp.{u1, u4, u3} α γ δ _inst_1 _inst_3 _inst_4 f (InfₛHom.comp.{u1, u2, u4} α β γ _inst_1 _inst_2 _inst_3 g h))
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_assoc InfₛHom.comp_assocₓ'. -/
@[simp]
theorem comp_assoc (f : InfₛHom γ δ) (g : InfₛHom β γ) (h : InfₛHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
#align Inf_hom.comp_assoc InfₛHom.comp_assoc

/- warning: Inf_hom.comp_id -> InfₛHom.comp_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.comp.{u1, u1, u2} α α β _inst_1 _inst_1 _inst_2 f (InfₛHom.id.{u1} α _inst_1)) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : InfₛHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) (InfₛHom.comp.{u2, u2, u1} α α β _inst_1 _inst_1 _inst_2 f (InfₛHom.id.{u2} α _inst_1)) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.comp_id InfₛHom.comp_idₓ'. -/
@[simp]
theorem comp_id (f : InfₛHom α β) : f.comp (InfₛHom.id α) = f :=
  ext fun a => rfl
#align Inf_hom.comp_id InfₛHom.comp_id

/- warning: Inf_hom.id_comp -> InfₛHom.id_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.comp.{u1, u2, u2} α β β _inst_1 _inst_2 _inst_2 (InfₛHom.id.{u2} β _inst_2) f) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : InfSet.{u1} β] (f : InfₛHom.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (InfₛHom.{u2, u1} α β _inst_1 _inst_2) (InfₛHom.comp.{u2, u1, u1} α β β _inst_1 _inst_2 _inst_2 (InfₛHom.id.{u1} β _inst_2) f) f
Case conversion may be inaccurate. Consider using '#align Inf_hom.id_comp InfₛHom.id_compₓ'. -/
@[simp]
theorem id_comp (f : InfₛHom α β) : (InfₛHom.id β).comp f = f :=
  ext fun a => rfl
#align Inf_hom.id_comp InfₛHom.id_comp

/- warning: Inf_hom.cancel_right -> InfₛHom.cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] {g₁ : InfₛHom.{u2, u3} β γ _inst_2 _inst_3} {g₂ : InfₛHom.{u2, u3} β γ _inst_2 _inst_3} {f : InfₛHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (Iff (Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) g₁ g₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] {g₁ : InfₛHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : InfₛHom.{u3, u2} β γ _inst_2 _inst_3} {f : InfₛHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (InfₛHom.instInfₛHomClassInfₛHom.{u1, u3} α β _inst_1 _inst_2)) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align Inf_hom.cancel_right InfₛHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : InfₛHom β γ} {f : InfₛHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align Inf_hom.cancel_right InfₛHom.cancel_right

/- warning: Inf_hom.cancel_left -> InfₛHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] {g : InfₛHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : InfₛHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : InfₛHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (InfₛHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] {g : InfₛHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : InfₛHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : InfₛHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (InfₛHom.instInfₛHomClassInfₛHom.{u3, u2} β γ _inst_2 _inst_3)) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align Inf_hom.cancel_left InfₛHom.cancel_leftₓ'. -/
theorem cancel_left {g : InfₛHom β γ} {f₁ f₂ : InfₛHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align Inf_hom.cancel_left InfₛHom.cancel_left

end InfSet

variable [CompleteLattice β]

instance : PartialOrder (InfₛHom α β) :=
  PartialOrder.lift _ FunLike.coe_injective

instance : Top (InfₛHom α β) :=
  ⟨⟨fun _ => ⊤, fun s => by
      obtain rfl | hs := s.eq_empty_or_nonempty
      · rw [Set.image_empty, infₛ_empty]
      · rw [hs.image_const, infₛ_singleton]⟩⟩

instance : OrderTop (InfₛHom α β) :=
  ⟨⊤, fun f a => le_top⟩

/- warning: Inf_hom.coe_top -> InfₛHom.coe_top is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β], Eq.{succ (max u1 u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), succ (max u1 u2)} (InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (Top.top.{max u1 u2} (InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfₛHom.hasTop.{u1, u2} α β _inst_1 _inst_2))) (Top.top.{max u1 u2} (α -> β) (Pi.hasTop.{u1, u2} α (fun (ᾰ : α) => β) (fun (i : α) => CompleteLattice.toHasTop.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : InfSet.{u2} α] [_inst_2 : CompleteLattice.{u1} β], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (InfₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (InfₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2) (InfₛHom.instInfₛHomClassInfₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2))) (Top.top.{max u2 u1} (InfₛHom.{u2, u1} α β _inst_1 (CompleteLattice.toInfSet.{u1} β _inst_2)) (InfₛHom.instTopInfₛHomToInfSet.{u2, u1} α β _inst_1 _inst_2))) (Top.top.{max u2 u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) ᾰ) (Pi.instTopForAll.{u2, u1} α (fun (ᾰ : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) ᾰ) (fun (i : α) => CompleteLattice.toTop.{u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) i) _inst_2)))
Case conversion may be inaccurate. Consider using '#align Inf_hom.coe_top InfₛHom.coe_topₓ'. -/
@[simp]
theorem coe_top : ⇑(⊤ : InfₛHom α β) = ⊤ :=
  rfl
#align Inf_hom.coe_top InfₛHom.coe_top

/- warning: Inf_hom.top_apply -> InfₛHom.top_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (fun (_x : InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) => α -> β) (InfₛHom.hasCoeToFun.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (Top.top.{max u1 u2} (InfₛHom.{u1, u2} α β _inst_1 (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2))) (InfₛHom.hasTop.{u1, u2} α β _inst_1 _inst_2)) a) (Top.top.{u2} β (CompleteLattice.toHasTop.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (InfₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (InfₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2) (InfₛHom.instInfₛHomClassInfₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2))) (Top.top.{max u1 u2} (InfₛHom.{u1, u2} α β _inst_1 (CompleteLattice.toInfSet.{u2} β _inst_2)) (InfₛHom.instTopInfₛHomToInfSet.{u1, u2} α β _inst_1 _inst_2)) a) (Top.top.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (CompleteLattice.toTop.{u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) _inst_2))
Case conversion may be inaccurate. Consider using '#align Inf_hom.top_apply InfₛHom.top_applyₓ'. -/
@[simp]
theorem top_apply (a : α) : (⊤ : InfₛHom α β) a = ⊤ :=
  rfl
#align Inf_hom.top_apply InfₛHom.top_apply

end InfₛHom

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
  map_supₛ f := f.map_Sup'
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
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : FrameHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (InfHom.toFun.{u2, u1} α β (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toHasInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_2)) (InfTopHom.toInfHom.{u2, u1} α β (Lattice.toHasInf.{u2} α (CompleteLattice.toLattice.{u2} α _inst_1)) (Lattice.toHasInf.{u1} β (CompleteLattice.toLattice.{u1} β _inst_2)) (CompleteLattice.toTop.{u2} α _inst_1) (CompleteLattice.toTop.{u1} β _inst_2) (FrameHom.toInfTopHom.{u2, u1} α β _inst_1 _inst_2 f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : FrameHom α β} : f.toFun = (f : α → β) :=
  rfl
#align frame_hom.to_fun_eq_coe FrameHom.toFun_eq_coe

/- warning: frame_hom.ext -> FrameHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : FrameHom.{u1, u2} α β _inst_1 _inst_2} {g : FrameHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : FrameHom.{u2, u1} α β _inst_1 _inst_2} {g : FrameHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) g a)) -> (Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align frame_hom.ext FrameHom.extₓ'. -/
@[ext]
theorem ext {f g : FrameHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align frame_hom.ext FrameHom.ext

/- warning: frame_hom.copy -> FrameHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (FrameHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α β _inst_1 _inst_2))) f)) -> (FrameHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align frame_hom.copy FrameHom.copyₓ'. -/
/-- Copy of a `frame_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : FrameHom α β :=
  { (f : SupₛHom α β).copy f' h with toInfTopHom := f.toInfTopHom.copy f' h }
#align frame_hom.copy FrameHom.copy

/- warning: frame_hom.coe_copy -> FrameHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (FrameHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) (FrameHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align frame_hom.coe_copy FrameHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : FrameHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align frame_hom.coe_copy FrameHom.coe_copy

/- warning: frame_hom.copy_eq -> FrameHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : FrameHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (FrameHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : FrameHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u2} α _inst_1) (CompleteLattice.toSupSet.{u1} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u2 u1, u2, u1} (FrameHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (FrameHom.{u2, u1} α β _inst_1 _inst_2) (FrameHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align frame_hom.copy_eq FrameHom.copy_eqₓ'. -/
theorem copy_eq (f : FrameHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align frame_hom.copy_eq FrameHom.copy_eq

variable (α)

#print FrameHom.id /-
/-- `id` as a `frame_hom`. -/
protected def id : FrameHom α α :=
  { SupₛHom.id α with toInfTopHom := InfTopHom.id α }
#align frame_hom.id FrameHom.id
-/

instance : Inhabited (FrameHom α α) :=
  ⟨FrameHom.id α⟩

/- warning: frame_hom.coe_id -> FrameHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : FrameHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (FrameHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (FrameHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (SupₛHomClass.toFunLike.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1) (FrameHomClass.toSupₛHomClass.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (FrameHom.instFrameHomClassFrameHom.{u1, u1} α α _inst_1 _inst_1))) (FrameHom.id.{u1} α _inst_1)) (id.{succ u1} α)
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
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => α) _x) (SupₛHomClass.toFunLike.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1) (FrameHomClass.toSupₛHomClass.{u1, u1, u1} (FrameHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (FrameHom.instFrameHomClassFrameHom.{u1, u1} α α _inst_1 _inst_1))) (FrameHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align frame_hom.id_apply FrameHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : FrameHom.id α a = a :=
  rfl
#align frame_hom.id_apply FrameHom.id_apply

#print FrameHom.comp /-
/-- Composition of `frame_hom`s as a `frame_hom`. -/
def comp (f : FrameHom β γ) (g : FrameHom α β) : FrameHom α γ :=
  { (f : SupₛHom β γ).comp (g : SupₛHom α β) with toInfTopHom := f.toInfTopHom.comp g.toInfTopHom }
#align frame_hom.comp FrameHom.comp
-/

/- warning: frame_hom.coe_comp -> FrameHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : FrameHom.{u2, u3} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : FrameHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (FrameHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : FrameHom.{u3, u2} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.toSupₛHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α γ _inst_1 _inst_3))) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.toSupₛHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align frame_hom.coe_comp FrameHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : FrameHom β γ) (g : FrameHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align frame_hom.coe_comp FrameHom.coe_comp

/- warning: frame_hom.comp_apply -> FrameHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : FrameHom.{u2, u3} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : FrameHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (FrameHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : FrameHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (FrameHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : FrameHom.{u3, u2} β γ _inst_2 _inst_3) (g : FrameHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => γ) _x) (SupₛHomClass.toFunLike.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.toSupₛHomClass.{max u1 u2, u1, u2} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u1, u2} α γ _inst_1 _inst_3))) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.toSupₛHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) g a))
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
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g₁ : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {f : FrameHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : α) => β) _x) (SupₛHomClass.toFunLike.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u3} β _inst_2) (FrameHomClass.toSupₛHomClass.{max u1 u3, u1, u3} (FrameHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (FrameHom.instFrameHomClassFrameHom.{u1, u3} α β _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align frame_hom.cancel_right FrameHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : FrameHom β γ} {f : FrameHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align frame_hom.cancel_right FrameHom.cancel_right

/- warning: frame_hom.cancel_left -> FrameHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g : FrameHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : FrameHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : FrameHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (FrameHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : FrameHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (FrameHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (FrameHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g : FrameHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : FrameHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : FrameHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : β) => γ) _x) (SupₛHomClass.toFunLike.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toSupSet.{u3} β _inst_2) (CompleteLattice.toSupSet.{u2} γ _inst_3) (FrameHomClass.toSupₛHomClass.{max u3 u2, u3, u2} (FrameHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (FrameHom.instFrameHomClassFrameHom.{u3, u2} β γ _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (FrameHom.{u1, u2} α γ _inst_1 _inst_3) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (FrameHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (FrameHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
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
  map_supₛ f := f.map_Sup'
  map_infₛ f := f.map_Inf'

/- warning: complete_lattice_hom.to_Sup_hom -> CompleteLatticeHom.toSupₛHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β], (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) -> (SupₛHom.{u1, u2} α β (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u2} β (CompleteLattice.toCompleteSemilatticeSup.{u2} β _inst_2)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β], (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) -> (SupₛHom.{u1, u2} α β (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.toSupₛHomₓ'. -/
/-- Reinterpret a `complete_lattice_hom` as a `Sup_hom`. -/
def toSupₛHom (f : CompleteLatticeHom α β) : SupₛHom α β :=
  f
#align complete_lattice_hom.to_Sup_hom CompleteLatticeHom.toSupₛHom

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
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, Eq.{max (succ u1) (succ u2)} (α -> β) (InfₛHom.toFun.{u1, u2} α β (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u2} β (CompleteLattice.toCompleteSemilatticeInf.{u2} β _inst_2)) (CompleteLatticeHom.toInfHom.{u1, u2} α β _inst_1 _inst_2 f)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2}, Eq.{max (succ u2) (succ u1)} (α -> β) (InfₛHom.toFun.{u2, u1} α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHom.toInfₛHom.{u2, u1} α β _inst_1 _inst_2 f)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coeₓ'. -/
@[simp]
theorem toFun_eq_coe {f : CompleteLatticeHom α β} : f.toFun = (f : α → β) :=
  rfl
#align complete_lattice_hom.to_fun_eq_coe CompleteLatticeHom.toFun_eq_coe

/- warning: complete_lattice_hom.ext -> CompleteLatticeHom.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] {f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2} {g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f a) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a)) -> (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) f g)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] {f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2} {g : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2}, (forall (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) g a)) -> (Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) f g)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.ext CompleteLatticeHom.extₓ'. -/
@[ext]
theorem ext {f g : CompleteLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h
#align complete_lattice_hom.ext CompleteLatticeHom.ext

/- warning: complete_lattice_hom.copy -> CompleteLatticeHom.copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β), (Eq.{max (succ u1) (succ u2)} (α -> β) f' (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2))) f)) -> (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.copy CompleteLatticeHom.copyₓ'. -/
/-- Copy of a `complete_lattice_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) :
    CompleteLatticeHom α β :=
  { f.toSupₛHom.copy f' h with toInfHom := f.toInfHom.copy f' h }
#align complete_lattice_hom.copy CompleteLatticeHom.copy

/- warning: complete_lattice_hom.coe_copy -> CompleteLatticeHom.coe_copy is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h)) f'
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) (CompleteLatticeHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h)) f'
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copyₓ'. -/
@[simp]
theorem coe_copy (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
#align complete_lattice_hom.coe_copy CompleteLatticeHom.coe_copy

/- warning: complete_lattice_hom.copy_eq -> CompleteLatticeHom.copy_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] (f : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u1) (succ u2)} (α -> β) f' (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)), Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u1, u2} α β _inst_1 _inst_2 f f' h) f
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : CompleteLattice.{u2} α] [_inst_2 : CompleteLattice.{u1} β] (f : CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (f' : α -> β) (h : Eq.{max (succ u2) (succ u1)} (α -> β) f' (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u2} α _inst_1) (CompleteLattice.toInfSet.{u1} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u2, u1} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2))) f)), Eq.{max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} α β _inst_1 _inst_2) (CompleteLatticeHom.copy.{u2, u1} α β _inst_1 _inst_2 f f' h) f
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eqₓ'. -/
theorem copy_eq (f : CompleteLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  FunLike.ext' h
#align complete_lattice_hom.copy_eq CompleteLatticeHom.copy_eq

variable (α)

#print CompleteLatticeHom.id /-
/-- `id` as a `complete_lattice_hom`. -/
protected def id : CompleteLatticeHom α α :=
  { SupₛHom.id α, InfₛHom.id α with toFun := id }
#align complete_lattice_hom.id CompleteLatticeHom.id
-/

instance : Inhabited (CompleteLatticeHom α α) :=
  ⟨CompleteLatticeHom.id α⟩

/- warning: complete_lattice_hom.coe_id -> CompleteLatticeHom.coe_id is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) => α -> α) (CompleteLatticeHom.hasCoeToFun.{u1, u1} α α _inst_1 _inst_1) (CompleteLatticeHom.id.{u1} α _inst_1)) (id.{succ u1} α)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CompleteLattice.{u1} α], Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) _x) (InfₛHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.toInfₛHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) (CompleteLatticeHom.id.{u1} α _inst_1)) (id.{succ u1} α)
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
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => α) _x) (InfₛHomClass.toFunLike.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLatticeHomClass.toInfₛHomClass.{u1, u1, u1} (CompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1) α α _inst_1 _inst_1 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u1} α α _inst_1 _inst_1))) (CompleteLatticeHom.id.{u1} α _inst_1) a) a
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.id_apply CompleteLatticeHom.id_applyₓ'. -/
@[simp]
theorem id_apply (a : α) : CompleteLatticeHom.id α a = a :=
  rfl
#align complete_lattice_hom.id_apply CompleteLatticeHom.id_apply

#print CompleteLatticeHom.comp /-
/-- Composition of `complete_lattice_hom`s as a `complete_lattice_hom`. -/
def comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : CompleteLatticeHom α γ :=
  { f.toSupₛHom.comp g.toSupₛHom with toInfHom := f.toInfHom.comp g.toInfHom }
#align complete_lattice_hom.comp CompleteLatticeHom.comp
-/

/- warning: complete_lattice_hom.coe_comp -> CompleteLatticeHom.coe_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (α -> γ) (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CompleteLatticeHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u2, succ u3} α β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3))) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g)) (Function.comp.{succ u1, succ u3, succ u2} α β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.toInfₛHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) f) (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) g))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_compₓ'. -/
@[simp]
theorem coe_comp (f : CompleteLatticeHom β γ) (g : CompleteLatticeHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl
#align complete_lattice_hom.coe_comp CompleteLatticeHom.coe_comp

/- warning: complete_lattice_hom.comp_apply -> CompleteLatticeHom.comp_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] (f : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (CompleteLatticeHom.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 f g) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) f (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) => α -> β) (CompleteLatticeHom.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) g a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (f : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (g : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => γ) _x) (InfₛHomClass.toFunLike.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u2, u1, u2} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) α γ _inst_1 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3))) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 f g) a) (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.toInfₛHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) f (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) g a))
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
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g₁ : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {g₂ : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {f : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Surjective.{succ u1, succ u3} α β (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : α) => β) _x) (InfₛHomClass.toFunLike.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u3, u1, u3} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) α β _inst_1 _inst_2 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2))) f)) -> (Iff (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₁ f) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g₂ f)) (Eq.{max (succ u3) (succ u2)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) g₁ g₂))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_rightₓ'. -/
theorem cancel_right {g₁ g₂ : CompleteLatticeHom β γ} {f : CompleteLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩
#align complete_lattice_hom.cancel_right CompleteLatticeHom.cancel_right

/- warning: complete_lattice_hom.cancel_left -> CompleteLatticeHom.cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u2} β] [_inst_3 : CompleteLattice.{u3} γ] {g : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3} {f₁ : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2} {f₂ : CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2}, (Function.Injective.{succ u2, succ u3} β γ (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (CompleteLatticeHom.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) g)) -> (Iff (Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₁) (CompleteLatticeHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α β _inst_1 _inst_2) f₁ f₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] {g : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3} {f₁ : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2} {f₂ : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2}, (Function.Injective.{succ u3, succ u2} β γ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : β) => γ) _x) (InfₛHomClass.toFunLike.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ (CompleteLattice.toInfSet.{u3} β _inst_2) (CompleteLattice.toInfSet.{u2} γ _inst_3) (CompleteLatticeHomClass.toInfₛHomClass.{max u3 u2, u3, u2} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) β γ _inst_2 _inst_3 (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3))) g)) -> (Iff (Eq.{max (succ u1) (succ u2)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₁) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f₂)) (Eq.{max (succ u1) (succ u3)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) f₁ f₂))
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_leftₓ'. -/
theorem cancel_left {g : CompleteLatticeHom β γ} {f₁ f₂ : CompleteLatticeHom α β}
    (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩
#align complete_lattice_hom.cancel_left CompleteLatticeHom.cancel_left

end CompleteLatticeHom

/-! ### Dual homs -/


namespace SupₛHom

variable [SupSet α] [SupSet β] [SupSet γ]

/- warning: Sup_hom.dual -> SupₛHom.dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual SupₛHom.dualₓ'. -/
/-- Reinterpret a `⨆`-homomorphism as an `⨅`-homomorphism between the dual orders. -/
@[simps]
protected def dual : SupₛHom α β ≃ InfₛHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨toDual ∘ f ∘ ofDual, f.map_Sup'⟩
  invFun f := ⟨ofDual ∘ f ∘ toDual, f.map_Inf'⟩
  left_inv f := SupₛHom.ext fun a => rfl
  right_inv f := InfₛHom.ext fun a => rfl
#align Sup_hom.dual SupₛHom.dual

/- warning: Sup_hom.dual_id -> SupₛHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) => (SupₛHom.{u1, u1} α α _inst_1 _inst_1) -> (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u1} α _inst_1))) (SupₛHom.dual.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.id.{u1} α _inst_1)) (InfₛHom.id.{u1} (OrderDual.{u1} α) (OrderDual.hasInf.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : SupSet.{u1} α], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u1} α α _inst_1 _inst_1) => InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1)) (SupₛHom.id.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1))) (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : SupₛHom.{u1, u1} α α _inst_1 _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u1} α α _inst_1 _inst_1) => InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (SupₛHom.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u1} α _inst_1))) (SupₛHom.dual.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.id.{u1} α _inst_1)) (InfₛHom.id.{u1} (OrderDual.{u1} α) (OrderDual.infSet.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_id SupₛHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (SupₛHom.id α).dual = InfₛHom.id _ :=
  rfl
#align Sup_hom.dual_id SupₛHom.dual_id

/- warning: Sup_hom.dual_comp -> SupₛHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (g : SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (f : SupₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) => (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) -> (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3))) (SupₛHom.dual.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (InfₛHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) => (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) -> (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3))) (SupₛHom.dual.{u2, u3} β γ _inst_2 _inst_3) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) => (SupₛHom.{u1, u2} α β _inst_1 _inst_2) -> (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2))) (SupₛHom.dual.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (g : SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (f : SupₛHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u2} α γ _inst_1 _inst_3) => InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3))) (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : SupₛHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u2} α γ _inst_1 _inst_3) => InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3))) (SupₛHom.dual.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (InfₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3))) (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : SupₛHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u3, u2} β γ _inst_2 _inst_3) => InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3))) (SupₛHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2))) (SupₛHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : SupₛHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u3} α β _inst_1 _inst_2) => InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2))) (SupₛHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align Sup_hom.dual_comp SupₛHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : SupₛHom β γ) (f : SupₛHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Sup_hom.dual_comp SupₛHom.dual_comp

#print SupₛHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : SupₛHom.dual.symm (InfₛHom.id _) = SupₛHom.id α :=
  rfl
#align Sup_hom.symm_dual_id SupₛHom.symm_dual_id
-/

/- warning: Sup_hom.symm_dual_comp -> SupₛHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u2} β] [_inst_3 : SupSet.{u3} γ] (g : InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (f : InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)), Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u1, u3} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u1, u3} α γ _inst_1 _inst_3)) => (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) -> (SupₛHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.dual.{u1, u3} α γ _inst_1 _inst_3)) (InfₛHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3) g f)) (SupₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u2, u3} β γ _inst_2 _inst_3)) => (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) -> (SupₛHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} β γ _inst_2 _inst_3) (InfₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasInf.{u2} β _inst_2) (OrderDual.hasInf.{u3} γ _inst_3)) (SupₛHom.dual.{u2, u3} β γ _inst_2 _inst_3)) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (SupₛHom.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (SupₛHom.{u1, u2} α β _inst_1 _inst_2)) => (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) -> (SupₛHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (SupₛHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} α β _inst_1 _inst_2) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasInf.{u1} α _inst_1) (OrderDual.hasInf.{u2} β _inst_2)) (SupₛHom.dual.{u1, u2} α β _inst_1 _inst_2)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SupSet.{u1} α] [_inst_2 : SupSet.{u3} β] [_inst_3 : SupSet.{u2} γ] (g : InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (f : InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.{u1, u2} α γ _inst_1 _inst_3)) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (fun (_x : InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) => SupₛHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (InfₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3) g f)) (SupₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.{u3, u2} β γ _inst_2 _inst_3)) (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (fun (_x : InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) => SupₛHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u3, u2} β γ _inst_2 _inst_3) (InfₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.infSet.{u3} β _inst_2) (OrderDual.infSet.{u2} γ _inst_3)) (SupₛHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (SupₛHom.{u1, u3} α β _inst_1 _inst_2)) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (fun (_x : InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) => SupₛHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (SupₛHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (SupₛHom.{u1, u3} α β _inst_1 _inst_2) (InfₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.infSet.{u1} α _inst_1) (OrderDual.infSet.{u3} β _inst_2)) (SupₛHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align Sup_hom.symm_dual_comp SupₛHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : InfₛHom βᵒᵈ γᵒᵈ) (f : InfₛHom αᵒᵈ βᵒᵈ) :
    SupₛHom.dual.symm (g.comp f) = (SupₛHom.dual.symm g).comp (SupₛHom.dual.symm f) :=
  rfl
#align Sup_hom.symm_dual_comp SupₛHom.symm_dual_comp

end SupₛHom

namespace InfₛHom

variable [InfSet α] [InfSet β] [InfSet γ]

/- warning: Inf_hom.dual -> InfₛHom.dual is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β], Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β], Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} β _inst_2))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual InfₛHom.dualₓ'. -/
/-- Reinterpret an `⨅`-homomorphism as a `⨆`-homomorphism between the dual orders. -/
@[simps]
protected def dual : InfₛHom α β ≃ SupₛHom αᵒᵈ βᵒᵈ
    where
  toFun f :=
    { toFun := toDual ∘ f ∘ ofDual
      map_Sup' := fun _ => congr_arg toDual (map_infₛ f _) }
  invFun f :=
    { toFun := ofDual ∘ f ∘ toDual
      map_Inf' := fun _ => congr_arg ofDual (map_supₛ f _) }
  left_inv f := InfₛHom.ext fun a => rfl
  right_inv f := SupₛHom.ext fun a => rfl
#align Inf_hom.dual InfₛHom.dual

/- warning: Inf_hom.dual_id -> InfₛHom.dual_id is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α], Eq.{succ u1} (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1)) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (fun (_x : Equiv.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) => (InfₛHom.{u1, u1} α α _inst_1 _inst_1) -> (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (Equiv.hasCoeToFun.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u1} α _inst_1))) (InfₛHom.dual.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.id.{u1} α _inst_1)) (SupₛHom.id.{u1} (OrderDual.{u1} α) (OrderDual.hasSup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : InfSet.{u1} α], Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u1} α α _inst_1 _inst_1) => SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1)) (InfₛHom.id.{u1} α _inst_1)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1))) (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (fun (_x : InfₛHom.{u1, u1} α α _inst_1 _inst_1) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u1} α α _inst_1 _inst_1) => SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (InfₛHom.{u1, u1} α α _inst_1 _inst_1) (SupₛHom.{u1, u1} (OrderDual.{u1} α) (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u1} α _inst_1))) (InfₛHom.dual.{u1, u1} α α _inst_1 _inst_1) (InfₛHom.id.{u1} α _inst_1)) (SupₛHom.id.{u1} (OrderDual.{u1} α) (OrderDual.supSet.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_id InfₛHom.dual_idₓ'. -/
@[simp]
theorem dual_id : (InfₛHom.id α).dual = SupₛHom.id _ :=
  rfl
#align Inf_hom.dual_id InfₛHom.dual_id

/- warning: Inf_hom.dual_comp -> InfₛHom.dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (g : InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (f : InfₛHom.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u3)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) => (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) -> (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3))) (InfₛHom.dual.{u1, u3} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 g f)) (SupₛHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3) (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) => (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) -> (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3))) (InfₛHom.dual.{u2, u3} β γ _inst_2 _inst_3) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) => (InfₛHom.{u1, u2} α β _inst_1 _inst_2) -> (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2))) (InfₛHom.dual.{u1, u2} α β _inst_1 _inst_2) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (g : InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (f : InfₛHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u2} α γ _inst_1 _inst_3) => SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3))) (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : InfₛHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u2} α γ _inst_1 _inst_3) => SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3))) (InfₛHom.dual.{u1, u2} α γ _inst_1 _inst_3) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (SupₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3))) (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : InfₛHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u3, u2} β γ _inst_2 _inst_3) => SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3))) (InfₛHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2))) (InfₛHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : InfₛHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : InfₛHom.{u1, u3} α β _inst_1 _inst_2) => SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2))) (InfₛHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
Case conversion may be inaccurate. Consider using '#align Inf_hom.dual_comp InfₛHom.dual_compₓ'. -/
@[simp]
theorem dual_comp (g : InfₛHom β γ) (f : InfₛHom α β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl
#align Inf_hom.dual_comp InfₛHom.dual_comp

#print InfₛHom.symm_dual_id /-
@[simp]
theorem symm_dual_id : InfₛHom.dual.symm (SupₛHom.id _) = InfₛHom.id α :=
  rfl
#align Inf_hom.symm_dual_id InfₛHom.symm_dual_id
-/

/- warning: Inf_hom.symm_dual_comp -> InfₛHom.symm_dual_comp is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u2} β] [_inst_3 : InfSet.{u3} γ] (g : SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (f : SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)), Eq.{max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u1, u3} α γ _inst_1 _inst_3)) (fun (_x : Equiv.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u1, u3} α γ _inst_1 _inst_3)) => (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) -> (InfₛHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.hasCoeToFun.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u1, u3} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (InfₛHom.{u1, u3} α γ _inst_1 _inst_3) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.dual.{u1, u3} α γ _inst_1 _inst_3)) (SupₛHom.comp.{u1, u2, u3} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3) g f)) (InfₛHom.comp.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u2, u3} β γ _inst_2 _inst_3)) (fun (_x : Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u2, u3} β γ _inst_2 _inst_3)) => (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) -> (InfₛHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.hasCoeToFun.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.{u2, u3} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u2, u3} β γ _inst_2 _inst_3) (SupₛHom.{u2, u3} (OrderDual.{u2} β) (OrderDual.{u3} γ) (OrderDual.hasSup.{u2} β _inst_2) (OrderDual.hasSup.{u3} γ _inst_3)) (InfₛHom.dual.{u2, u3} β γ _inst_2 _inst_3)) g) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (InfₛHom.{u1, u2} α β _inst_1 _inst_2)) (fun (_x : Equiv.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (InfₛHom.{u1, u2} α β _inst_1 _inst_2)) => (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) -> (InfₛHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.hasCoeToFun.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (InfₛHom.{u1, u2} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (InfₛHom.{u1, u2} α β _inst_1 _inst_2) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} β) (OrderDual.hasSup.{u1} α _inst_1) (OrderDual.hasSup.{u2} β _inst_2)) (InfₛHom.dual.{u1, u2} α β _inst_1 _inst_2)) f))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : InfSet.{u1} α] [_inst_2 : InfSet.{u3} β] [_inst_3 : InfSet.{u2} γ] (g : SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (f : SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.{u1, u2} α γ _inst_1 _inst_3)) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (fun (_x : SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) => InfₛHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (InfₛHom.{u1, u2} α γ _inst_1 _inst_3) (SupₛHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (SupₛHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3) g f)) (InfₛHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.{u3, u2} β γ _inst_2 _inst_3)) (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (fun (_x : SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) => InfₛHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (InfₛHom.{u3, u2} β γ _inst_2 _inst_3) (SupₛHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.supSet.{u3} β _inst_2) (OrderDual.supSet.{u2} γ _inst_3)) (InfₛHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (InfₛHom.{u1, u3} α β _inst_1 _inst_2)) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (fun (_x : SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) => InfₛHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (InfₛHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (InfₛHom.{u1, u3} α β _inst_1 _inst_2) (SupₛHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.supSet.{u1} α _inst_1) (OrderDual.supSet.{u3} β _inst_2)) (InfₛHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
Case conversion may be inaccurate. Consider using '#align Inf_hom.symm_dual_comp InfₛHom.symm_dual_compₓ'. -/
@[simp]
theorem symm_dual_comp (g : SupₛHom βᵒᵈ γᵒᵈ) (f : SupₛHom αᵒᵈ βᵒᵈ) :
    InfₛHom.dual.symm (g.comp f) = (InfₛHom.dual.symm g).comp (InfₛHom.dual.symm f) :=
  rfl
#align Inf_hom.symm_dual_comp InfₛHom.symm_dual_comp

end InfₛHom

namespace CompleteLatticeHom

variable [CompleteLattice α] [CompleteLattice β] [CompleteLattice γ]

#print CompleteLatticeHom.dual /-
/-- Reinterpret a complete lattice homomorphism as a complete lattice homomorphism between the dual
lattices. -/
@[simps]
protected def dual : CompleteLatticeHom α β ≃ CompleteLatticeHom αᵒᵈ βᵒᵈ
    where
  toFun f := ⟨f.toSupₛHom.dual, f.map_Inf'⟩
  invFun f := ⟨f.toSupₛHom.dual, f.map_Inf'⟩
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
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (g : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (f : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (fun (_x : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) => CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.dual.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 g f)) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (fun (_x : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) => CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3))) (CompleteLatticeHom.dual.{u3, u2} β γ _inst_2 _inst_3) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2))) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (fun (_x : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) => CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2))) (CompleteLatticeHom.dual.{u1, u3} α β _inst_1 _inst_2) f))
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
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : CompleteLattice.{u1} α] [_inst_2 : CompleteLattice.{u3} β] [_inst_3 : CompleteLattice.{u2} γ] (g : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (f : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)), Eq.{max (succ u1) (succ u2)} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) g f)) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (Equiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3)) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (fun (_x : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3)) (Equiv.symm.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u1, u2} α γ _inst_1 _inst_3) (CompleteLatticeHom.{u1, u2} (OrderDual.{u1} α) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.dual.{u1, u2} α γ _inst_1 _inst_3)) (CompleteLatticeHom.comp.{u1, u3, u2} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3) g f)) (CompleteLatticeHom.comp.{u1, u3, u2} α β γ _inst_1 _inst_2 _inst_3 (FunLike.coe.{max (succ u2) (succ u3), max (succ u2) (succ u3), max (succ u2) (succ u3)} (Equiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3)) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (fun (_x : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) => CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) _x) (Equiv.instFunLikeEquiv.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3)) (Equiv.symm.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (CompleteLatticeHom.{u3, u2} β γ _inst_2 _inst_3) (CompleteLatticeHom.{u3, u2} (OrderDual.{u3} β) (OrderDual.{u2} γ) (OrderDual.completeLattice.{u3} β _inst_2) (OrderDual.completeLattice.{u2} γ _inst_3)) (CompleteLatticeHom.dual.{u3, u2} β γ _inst_2 _inst_3)) g) (FunLike.coe.{max (succ u3) (succ u1), max (succ u3) (succ u1), max (succ u3) (succ u1)} (Equiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2)) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (fun (_x : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) => CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) _x) (Equiv.instFunLikeEquiv.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2)) (Equiv.symm.{max (succ u3) (succ u1), max (succ u3) (succ u1)} (CompleteLatticeHom.{u1, u3} α β _inst_1 _inst_2) (CompleteLatticeHom.{u1, u3} (OrderDual.{u1} α) (OrderDual.{u3} β) (OrderDual.completeLattice.{u1} α _inst_1) (OrderDual.completeLattice.{u3} β _inst_2)) (CompleteLatticeHom.dual.{u1, u3} α β _inst_1 _inst_2)) f))
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
  map_Sup' s := preimage_unionₛ.trans <| by simp only [Set.supₛ_eq_unionₛ, Set.unionₛ_image]
  map_Inf' s := preimage_interₛ.trans <| by simp only [Set.infₛ_eq_interₛ, Set.interₛ_image]
#align complete_lattice_hom.set_preimage CompleteLatticeHom.setPreimage

/- warning: complete_lattice_hom.coe_set_preimage -> CompleteLatticeHom.coe_setPreimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β), Eq.{max (succ u2) (succ u1)} ((Set.{u2} β) -> (Set.{u1} α)) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (fun (_x : CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) => (Set.{u2} β) -> (Set.{u1} α)) (CompleteLatticeHom.hasCoeToFun.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f)) (Set.preimage.{u1, u2} α β f)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (f : α -> β), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Set.{u1} β), (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Set.{u1} β) => Set.{u2} α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (fun (_x : Set.{u1} β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Set.{u1} β) => Set.{u2} α) _x) (InfₛHomClass.toFunLike.{max u2 u1, u1, u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (Set.{u2} α) (CompleteLattice.toInfSet.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))) (CompleteLattice.toInfSet.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (CompleteLatticeHomClass.toInfₛHomClass.{max u2 u1, u1, u2} (CompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))) (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α)))) (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u1, u2} (Set.{u1} β) (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (CompleteLatticeHom.setPreimage.{u2, u1} α β f)) (Set.preimage.{u2, u1} α β f)
Case conversion may be inaccurate. Consider using '#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimageₓ'. -/
@[simp]
theorem coe_setPreimage (f : α → β) : ⇑(setPreimage f) = preimage f :=
  rfl
#align complete_lattice_hom.coe_set_preimage CompleteLatticeHom.coe_setPreimage

/- warning: complete_lattice_hom.set_preimage_apply -> CompleteLatticeHom.setPreimage_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (fun (_x : CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) => (Set.{u2} β) -> (Set.{u1} α)) (CompleteLatticeHom.hasCoeToFun.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f) s) (Set.preimage.{u1, u2} α β f s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (f : α -> β) (s : Set.{u2} β), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Set.{u2} β) => Set.{u1} α) s) (FunLike.coe.{max (succ u1) (succ u2), succ u2, succ u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (fun (_x : Set.{u2} β) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Set.{u2} β) => Set.{u1} α) _x) (InfₛHomClass.toFunLike.{max u1 u2, u2, u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (Set.{u1} α) (CompleteLattice.toInfSet.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))) (CompleteLattice.toInfSet.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (CompleteLatticeHomClass.toInfₛHomClass.{max u1 u2, u2, u1} (CompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))) (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))) (CompleteLatticeHom.instCompleteLatticeHomClassCompleteLatticeHom.{u2, u1} (Set.{u2} β) (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β)))) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (CompleteLatticeHom.setPreimage.{u1, u2} α β f) s) (Set.preimage.{u1, u2} α β f s)
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

/- warning: set.image_Sup -> Set.image_supₛ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : α -> β} (s : Set.{u1} (Set.{u1} α)), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β f (SupSet.supₛ.{u1} (Set.{u1} α) (Set.hasSup.{u1} α) s)) (SupSet.supₛ.{u2} (Set.{u2} β) (Set.hasSup.{u2} β) (Set.image.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.image.{u1, u2} α β f) s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : α -> β} (s : Set.{u2} (Set.{u2} α)), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β f (SupSet.supₛ.{u2} (Set.{u2} α) (Set.instSupSetSet.{u2} α) s)) (SupSet.supₛ.{u1} (Set.{u1} β) (Set.instSupSetSet.{u1} β) (Set.image.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.image.{u2, u1} α β f) s))
Case conversion may be inaccurate. Consider using '#align set.image_Sup Set.image_supₛₓ'. -/
theorem Set.image_supₛ {f : α → β} (s : Set (Set α)) : f '' supₛ s = supₛ (image f '' s) :=
  by
  ext b
  simp only [Sup_eq_sUnion, mem_image, mem_sUnion, exists_prop, sUnion_image, mem_Union]
  constructor
  · rintro ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
    exact ⟨t, ht₁, a, ht₂, rfl⟩
  · rintro ⟨t, ht₁, a, ht₂, rfl⟩
    exact ⟨a, ⟨t, ht₁, ht₂⟩, rfl⟩
#align set.image_Sup Set.image_supₛ

/- warning: Sup_hom.set_image -> SupₛHom.setImage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (SupₛHom.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.hasSup.{u1} α) (Set.hasSup.{u2} β))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}}, (α -> β) -> (SupₛHom.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.instSupSetSet.{u1} α) (Set.instSupSetSet.{u2} β))
Case conversion may be inaccurate. Consider using '#align Sup_hom.set_image SupₛHom.setImageₓ'. -/
/-- Using `set.image`, a function between types yields a `Sup_hom` between their lattices of
subsets.

See also `complete_lattice_hom.set_preimage`. -/
@[simps]
def SupₛHom.setImage (f : α → β) : SupₛHom (Set α) (Set β)
    where
  toFun := image f
  map_Sup' := Set.image_supₛ
#align Sup_hom.set_image SupₛHom.setImage

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

/- warning: sup_Sup_hom -> supSupₛHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align sup_Sup_hom supSupₛHomₓ'. -/
/-- The map `(a, b) ↦ a ⊔ b` as a `Sup_hom`. -/
def supSupₛHom : SupₛHom (α × α) α where
  toFun x := x.1 ⊔ x.2
  map_Sup' s := by simp_rw [Prod.fst_supₛ, Prod.snd_supₛ, supₛ_image, supᵢ_sup_eq]
#align sup_Sup_hom supSupₛHom

/- warning: inf_Inf_hom -> infInfₛHom is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α], InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align inf_Inf_hom infInfₛHomₓ'. -/
/-- The map `(a, b) ↦ a ⊓ b` as an `Inf_hom`. -/
def infInfₛHom : InfₛHom (α × α) α where
  toFun x := x.1 ⊓ x.2
  map_Inf' s := by simp_rw [Prod.fst_infₛ, Prod.snd_infₛ, infₛ_image, infᵢ_inf_eq]
#align inf_Inf_hom infInfₛHom

/- warning: sup_Sup_hom_apply -> supSupₛHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (fun (_x : SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) => (Prod.{u1, u1} α α) -> α) (SupₛHom.hasCoeToFun.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasSup.{u1, u1} α α (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1)) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (CompleteSemilatticeSup.toHasSup.{u1} α (CompleteLattice.toCompleteSemilatticeSup.{u1} α _inst_1))) (supSupₛHom.{u1} α _inst_1) x) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : Prod.{u1, u1} α α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (_x : Prod.{u1, u1} α α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.309 : Prod.{u1, u1} α α) => α) _x) (SupₛHomClass.toFunLike.{u1, u1, u1} (SupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1) (SupₛHom.instSupₛHomClassSupₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.supSet.{u1, u1} α α (CompleteLattice.toSupSet.{u1} α _inst_1) (CompleteLattice.toSupSet.{u1} α _inst_1)) (CompleteLattice.toSupSet.{u1} α _inst_1))) (supSupₛHom.{u1} α _inst_1) x) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
Case conversion may be inaccurate. Consider using '#align sup_Sup_hom_apply supSupₛHom_applyₓ'. -/
@[simp, norm_cast]
theorem supSupₛHom_apply : supSupₛHom x = x.1 ⊔ x.2 :=
  rfl
#align sup_Sup_hom_apply supSupₛHom_apply

/- warning: inf_Inf_hom_apply -> infInfₛHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (fun (_x : InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) => (Prod.{u1, u1} α α) -> α) (InfₛHom.hasCoeToFun.{u1, u1} (Prod.{u1, u1} α α) α (Prod.hasInf.{u1, u1} α α (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1)) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (CompleteSemilatticeInf.toHasInf.{u1} α (CompleteLattice.toCompleteSemilatticeInf.{u1} α _inst_1))) (infInfₛHom.{u1} α _inst_1) x) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (x : Prod.{u1, u1} α α), Eq.{succ u1} ((fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Prod.{u1, u1} α α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) (fun (_x : Prod.{u1, u1} α α) => (fun (x._@.Mathlib.Order.Hom.CompleteLattice._hyg.372 : Prod.{u1, u1} α α) => α) _x) (InfₛHomClass.toFunLike.{u1, u1, u1} (InfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1)) (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1) (InfₛHom.instInfₛHomClassInfₛHom.{u1, u1} (Prod.{u1, u1} α α) α (Prod.infSet.{u1, u1} α α (CompleteLattice.toInfSet.{u1} α _inst_1) (CompleteLattice.toInfSet.{u1} α _inst_1)) (CompleteLattice.toInfSet.{u1} α _inst_1))) (infInfₛHom.{u1} α _inst_1) x) (HasInf.inf.{u1} α (Lattice.toHasInf.{u1} α (CompleteLattice.toLattice.{u1} α _inst_1)) (Prod.fst.{u1, u1} α α x) (Prod.snd.{u1, u1} α α x))
Case conversion may be inaccurate. Consider using '#align inf_Inf_hom_apply infInfₛHom_applyₓ'. -/
@[simp, norm_cast]
theorem infInfₛHom_apply : infInfₛHom x = x.1 ⊓ x.2 :=
  rfl
#align inf_Inf_hom_apply infInfₛHom_apply

