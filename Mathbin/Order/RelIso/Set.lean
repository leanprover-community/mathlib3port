/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module order.rel_iso.set
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.RelIso.Basic
import Mathbin.Logic.Embedding.Set

/-!
# Interactions between relation homomorphisms and sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

It is likely that there are better homes for many of these statement,
in files further down the import graph.
-/


open Function

universe u v w

variable {α β γ δ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  {u : δ → δ → Prop}

namespace RelHomClass

variable {F : Type _}

/- warning: rel_hom_class.map_inf -> RelHomClass.map_inf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_1 : SemilatticeInf.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : RelHomClass.{u3, u2, u1} F β α (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1))))] (a : F) (m : β) (n : β), Eq.{succ u1} α (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a (HasInf.inf.{u2} β (SemilatticeInf.toHasInf.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))) m n)) (HasInf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α _inst_1) (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a m) (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (LT.lt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeInf.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a n))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_1 : SemilatticeInf.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : RelHomClass.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.111 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.113 : β) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.111 x._@.Mathlib.Order.RelIso.Set._hyg.113) (fun (x._@.Mathlib.Order.RelIso.Set._hyg.133 : α) (x._@.Mathlib.Order.RelIso.Set._hyg.135 : α) => LT.lt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α _inst_1))) x._@.Mathlib.Order.RelIso.Set._hyg.133 x._@.Mathlib.Order.RelIso.Set._hyg.135)] (a : F) (m : β) (n : β), Eq.{succ u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))) m n)) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.111 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.113 : β) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.111 x._@.Mathlib.Order.RelIso.Set._hyg.113) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.135 : α) => LT.lt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.135) _inst_3) a (HasInf.inf.{u2} β (Lattice.toHasInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2))) m n)) (HasInf.inf.{u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) m) (SemilatticeInf.toHasInf.{u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) m) _inst_1) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.111 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.113 : β) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.111 x._@.Mathlib.Order.RelIso.Set._hyg.113) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.135 : α) => LT.lt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.135) _inst_3) a m) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.111 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.113 : β) => LT.lt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.111 x._@.Mathlib.Order.RelIso.Set._hyg.113) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.135 : α) => LT.lt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeInf.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.135) _inst_3) a n))
Case conversion may be inaccurate. Consider using '#align rel_hom_class.map_inf RelHomClass.map_infₓ'. -/
theorem map_inf [SemilatticeInf α] [LinearOrder β]
    [RelHomClass F ((· < ·) : β → β → Prop) ((· < ·) : α → α → Prop)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun x y => map_rel a).map_inf m n
#align rel_hom_class.map_inf RelHomClass.map_inf

/- warning: rel_hom_class.map_sup -> RelHomClass.map_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {F : Type.{u3}} [_inst_1 : SemilatticeSup.{u1} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : RelHomClass.{u3, u2, u1} F β α (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1))))] (a : F) (m : β) (n : β), Eq.{succ u1} α (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (LinearOrder.toLattice.{u2} β _inst_2))) m n)) (HasSup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α _inst_1) (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a m) (coeFn.{succ u3, max (succ u2) (succ u1)} F (fun (_x : F) => β -> α) (FunLike.hasCoeToFun.{succ u3, succ u2, succ u1} F β (fun (_x : β) => α) (RelHomClass.toFunLike.{u3, u2, u1} F β α (GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (LinearOrder.toLattice.{u2} β _inst_2)))))) (GT.gt.{u1} α (Preorder.toLT.{u1} α (PartialOrder.toPreorder.{u1} α (SemilatticeSup.toPartialOrder.{u1} α _inst_1)))) _inst_3)) a n))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {F : Type.{u1}} [_inst_1 : SemilatticeSup.{u3} α] [_inst_2 : LinearOrder.{u2} β] [_inst_3 : RelHomClass.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.225 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.227 : β) => GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.225 x._@.Mathlib.Order.RelIso.Set._hyg.227) (fun (x._@.Mathlib.Order.RelIso.Set._hyg.247 : α) (x._@.Mathlib.Order.RelIso.Set._hyg.249 : α) => GT.gt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1))) x._@.Mathlib.Order.RelIso.Set._hyg.247 x._@.Mathlib.Order.RelIso.Set._hyg.249)] (a : F) (m : β) (n : β), Eq.{succ u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))) m n)) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.225 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.227 : β) => GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.225 x._@.Mathlib.Order.RelIso.Set._hyg.227) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.249 : α) => GT.gt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.249) _inst_3) a (HasSup.sup.{u2} β (SemilatticeSup.toHasSup.{u2} β (Lattice.toSemilatticeSup.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))) m n)) (HasSup.sup.{u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) m) (SemilatticeSup.toHasSup.{u3} ((fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) m) _inst_1) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.225 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.227 : β) => GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.225 x._@.Mathlib.Order.RelIso.Set._hyg.227) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.249 : α) => GT.gt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.249) _inst_3) a m) (FunLike.coe.{succ u1, succ u2, succ u3} F β (fun (_x : β) => (fun (x._@.Mathlib.Order.RelIso.Basic._hyg.867 : β) => α) _x) (RelHomClass.toFunLike.{u1, u2, u3} F β α (fun (x._@.Mathlib.Order.RelIso.Set._hyg.225 : β) (x._@.Mathlib.Order.RelIso.Set._hyg.227 : β) => GT.gt.{u2} β (Preorder.toLT.{u2} β (PartialOrder.toPreorder.{u2} β (SemilatticeInf.toPartialOrder.{u2} β (Lattice.toSemilatticeInf.{u2} β (DistribLattice.toLattice.{u2} β (instDistribLattice.{u2} β _inst_2)))))) x._@.Mathlib.Order.RelIso.Set._hyg.225 x._@.Mathlib.Order.RelIso.Set._hyg.227) (fun (_x : α) (x._@.Mathlib.Order.RelIso.Set._hyg.249 : α) => GT.gt.{u3} α (Preorder.toLT.{u3} α (PartialOrder.toPreorder.{u3} α (SemilatticeSup.toPartialOrder.{u3} α _inst_1))) _x x._@.Mathlib.Order.RelIso.Set._hyg.249) _inst_3) a n))
Case conversion may be inaccurate. Consider using '#align rel_hom_class.map_sup RelHomClass.map_supₓ'. -/
theorem map_sup [SemilatticeSup α] [LinearOrder β]
    [RelHomClass F ((· > ·) : β → β → Prop) ((· > ·) : α → α → Prop)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  @map_inf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _
#align rel_hom_class.map_sup RelHomClass.map_sup

end RelHomClass

namespace RelIso

/- warning: rel_iso.range_eq -> RelIso.range_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u1, u2} α β r s), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelIso.{u1, u2} α β r s) (fun (_x : RelIso.{u1, u2} α β r s) => α -> β) (RelIso.hasCoeToFun.{u1, u2} α β r s) e)) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> α -> Prop} {s : β -> β -> Prop} (e : RelIso.{u2, u1} α β r s), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) (RelEmbedding.toEmbedding.{u2, u1} α β r s (RelIso.toRelEmbedding.{u2, u1} α β r s e)))) (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align rel_iso.range_eq RelIso.range_eqₓ'. -/
@[simp]
theorem range_eq (e : r ≃r s) : Set.range e = Set.univ :=
  e.surjective.range_eq
#align rel_iso.range_eq RelIso.range_eq

end RelIso

#print Subrel /-
/-- `subrel r p` is the inherited relation on a subset. -/
def Subrel (r : α → α → Prop) (p : Set α) : p → p → Prop :=
  (coe : p → α) ⁻¹'o r
#align subrel Subrel
-/

#print subrel_val /-
@[simp]
theorem subrel_val (r : α → α → Prop) (p : Set α) {a b} : Subrel r p a b ↔ r a.1 b.1 :=
  Iff.rfl
#align subrel_val subrel_val
-/

namespace Subrel

#print Subrel.relEmbedding /-
/-- The relation embedding from the inherited relation on a subset. -/
protected def relEmbedding (r : α → α → Prop) (p : Set α) : Subrel r p ↪r r :=
  ⟨Embedding.subtype _, fun a b => Iff.rfl⟩
#align subrel.rel_embedding Subrel.relEmbedding
-/

/- warning: subrel.rel_embedding_apply -> Subrel.relEmbedding_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : α -> α -> Prop) (p : Set.{u1} α) (a : coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) p), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (RelEmbedding.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) p) α (Subrel.{u1} α r p) r) (fun (_x : RelEmbedding.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) p) α (Subrel.{u1} α r p) r) => (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) p) -> α) (RelEmbedding.hasCoeToFun.{u1, u1} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) p) α (Subrel.{u1} α r p) r) (Subrel.relEmbedding.{u1} α r p) a) (Subtype.val.{succ u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x p) a)
but is expected to have type
  forall {α : Type.{u1}} (r : α -> α -> Prop) (p : Set.{u1} α) (a : Set.Elem.{u1} α p), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u1} α p) => α) a) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Set.Elem.{u1} α p) α) (Set.Elem.{u1} α p) (fun (_x : Set.Elem.{u1} α p) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{u1} α p) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} (Set.Elem.{u1} α p) α) (Set.Elem.{u1} α p) α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} (Set.Elem.{u1} α p) α)) (RelEmbedding.toEmbedding.{u1, u1} (Set.Elem.{u1} α p) α (Subrel.{u1} α r p) r (Subrel.relEmbedding.{u1} α r p)) a) (Subtype.val.{succ u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x p) a)
Case conversion may be inaccurate. Consider using '#align subrel.rel_embedding_apply Subrel.relEmbedding_applyₓ'. -/
@[simp]
theorem relEmbedding_apply (r : α → α → Prop) (p a) : Subrel.relEmbedding r p a = a.1 :=
  rfl
#align subrel.rel_embedding_apply Subrel.relEmbedding_apply

instance (r : α → α → Prop) [IsWellOrder α r] (p : Set α) : IsWellOrder p (Subrel r p) :=
  RelEmbedding.isWellOrder (Subrel.relEmbedding r p)

instance (r : α → α → Prop) [IsRefl α r] (p : Set α) : IsRefl p (Subrel r p) :=
  ⟨fun x => @IsRefl.refl α r _ x⟩

instance (r : α → α → Prop) [IsSymm α r] (p : Set α) : IsSymm p (Subrel r p) :=
  ⟨fun x y => @IsSymm.symm α r _ x y⟩

instance (r : α → α → Prop) [IsTrans α r] (p : Set α) : IsTrans p (Subrel r p) :=
  ⟨fun x y z => @IsTrans.trans α r _ x y z⟩

instance (r : α → α → Prop) [IsIrrefl α r] (p : Set α) : IsIrrefl p (Subrel r p) :=
  ⟨fun x => @IsIrrefl.irrefl α r _ x⟩

end Subrel

/- warning: rel_embedding.cod_restrict -> RelEmbedding.codRestrict is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : RelEmbedding.{u1, u2} α β r s), (forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) p) -> (RelEmbedding.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : RelEmbedding.{u1, u2} α β r s), (forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f) a) p) -> (RelEmbedding.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p))
Case conversion may be inaccurate. Consider using '#align rel_embedding.cod_restrict RelEmbedding.codRestrictₓ'. -/
/-- Restrict the codomain of a relation embedding. -/
def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r Subrel s p :=
  ⟨f.toEmbedding.codRestrict p H, fun _ _ => f.map_rel_iff'⟩
#align rel_embedding.cod_restrict RelEmbedding.codRestrict

/- warning: rel_embedding.cod_restrict_apply -> RelEmbedding.codRestrict_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : RelEmbedding.{u1, u2} α β r s) (H : forall (a : α), Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) p) (a : α), Eq.{succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) (fun (_x : RelEmbedding.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) => α -> (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p)) (RelEmbedding.hasCoeToFun.{u1, u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) p) r (Subrel.{u2} β s p)) (RelEmbedding.codRestrict.{u1, u2} α β r s p f H) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x p) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (RelEmbedding.{u1, u2} α β r s) (fun (_x : RelEmbedding.{u1, u2} α β r s) => α -> β) (RelEmbedding.hasCoeToFun.{u1, u2} α β r s) f a) (H a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> α -> Prop} {s : β -> β -> Prop} (p : Set.{u2} β) (f : RelEmbedding.{u1, u2} α β r s) (H : forall (a : α), Membership.mem.{u2, u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Set.{u2} β) (Set.instMembershipSet.{u2} β) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f) a) p) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α (Set.Elem.{u2} β p)) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => Set.Elem.{u2} β p) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α (Set.Elem.{u2} β p)) α (Set.Elem.{u2} β p) (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α (Set.Elem.{u2} β p))) (RelEmbedding.toEmbedding.{u1, u2} α (Set.Elem.{u2} β p) r (Subrel.{u2} β s p) (RelEmbedding.codRestrict.{u1, u2} α β r s p f H)) a) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x p) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (RelEmbedding.toEmbedding.{u1, u2} α β r s f) a) (H a))
Case conversion may be inaccurate. Consider using '#align rel_embedding.cod_restrict_apply RelEmbedding.codRestrict_applyₓ'. -/
@[simp]
theorem RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) :
    RelEmbedding.codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align rel_embedding.cod_restrict_apply RelEmbedding.codRestrict_apply

