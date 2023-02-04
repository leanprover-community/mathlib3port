/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.embedding
! leanprover-community/mathlib commit b363547b3113d350d053abdf2884e9850a56b205
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.GroupAction.Group
import Mathbin.GroupTheory.GroupAction.Pi

/-!
# Group actions on embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides a `mul_action G (α ↪ β)` instance that agrees with the `mul_action G (α → β)`
instances defined by `pi.mul_action`.

Note that unlike the `pi` instance, this requires `G` to be a group.
-/


universe u v w

variable {G G' α β : Type _}

namespace Function.Embedding

@[to_additive Function.Embedding.hasVadd]
instance [Group G] [MulAction G β] : SMul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

/- warning: function.embedding.smul_def -> Function.Embedding.smul_def is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] (g : G) (f : Function.Embedding.{succ u2, succ u3} α β), Eq.{succ (max u2 u3)} (Function.Embedding.{succ u2, succ u3} α β) (SMul.smul.{u1, max u2 u3} G (Function.Embedding.{succ u2, succ u3} α β) (Function.Embedding.hasSmul.{u1, u2, u3} G α β _inst_1 _inst_2) g f) (Function.Embedding.trans.{succ u2, succ u3, succ u3} α β β f (Equiv.toEmbedding.{succ u3, succ u3} β β (MulAction.toPerm.{u1, u3} G β _inst_1 _inst_2 g)))
but is expected to have type
  forall {G : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u3} G] [_inst_2 : MulAction.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_1))] (g : G) (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.{succ u1, succ u2} α β) (instHSMul.{u3, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.smul.{u3, u1, u2} G α β _inst_1 _inst_2)) g f) (Function.Embedding.trans.{succ u1, succ u2, succ u2} α β β f (Equiv.toEmbedding.{succ u2, succ u2} β β (MulAction.toPerm.{u3, u2} G β _inst_1 _inst_2 g)))
Case conversion may be inaccurate. Consider using '#align function.embedding.smul_def Function.Embedding.smul_defₓ'. -/
@[to_additive]
theorem smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) :
    g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl
#align function.embedding.smul_def Function.Embedding.smul_def
#align function.embedding.vadd_def Function.Embedding.vadd_def

/- warning: function.embedding.smul_apply -> Function.Embedding.smul_apply is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] (g : G) (f : Function.Embedding.{succ u2, succ u3} α β) (a : α), Eq.{succ u3} β (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} α β) (fun (_x : Function.Embedding.{succ u2, succ u3} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} α β) (SMul.smul.{u1, max u2 u3} G (Function.Embedding.{succ u2, succ u3} α β) (Function.Embedding.hasSmul.{u1, u2, u3} G α β _inst_1 _inst_2) g f) a) (SMul.smul.{u1, u3} G β (MulAction.toHasSmul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2) g (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} α β) (fun (_x : Function.Embedding.{succ u2, succ u3} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} α β) f a))
but is expected to have type
  forall {G : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u3} G] [_inst_2 : MulAction.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_1))] (g : G) (f : Function.Embedding.{succ u1, succ u2} α β) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.{succ u1, succ u2} α β) (instHSMul.{u3, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.smul.{u3, u1, u2} G α β _inst_1 _inst_2)) g f) a) (HSMul.hSMul.{u3, u2, u2} G ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (instHSMul.{u3, u2} G ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (MulAction.toSMul.{u3, u2} G ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_1)) _inst_2)) g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) f a))
Case conversion may be inaccurate. Consider using '#align function.embedding.smul_apply Function.Embedding.smul_applyₓ'. -/
@[simp, to_additive]
theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
  rfl
#align function.embedding.smul_apply Function.Embedding.smul_apply
#align function.embedding.vadd_apply Function.Embedding.vadd_apply

/- warning: function.embedding.coe_smul -> Function.Embedding.coe_smul is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : Group.{u1} G] [_inst_2 : MulAction.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1))] (g : G) (f : Function.Embedding.{succ u2, succ u3} α β), Eq.{succ (max u2 u3)} (α -> β) (coeFn.{succ (max u2 u3), succ (max u2 u3)} (Function.Embedding.{succ u2, succ u3} α β) (fun (_x : Function.Embedding.{succ u2, succ u3} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} α β) (SMul.smul.{u1, max u2 u3} G (Function.Embedding.{succ u2, succ u3} α β) (Function.Embedding.hasSmul.{u1, u2, u3} G α β _inst_1 _inst_2) g f)) (SMul.smul.{u1, max u2 u3} G (α -> β) (Function.hasSMul.{u2, u1, u3} α G β (MulAction.toHasSmul.{u1, u3} G β (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)) _inst_2)) g (coeFn.{max 1 (succ u2) (succ u3), max (succ u2) (succ u3)} (Function.Embedding.{succ u2, succ u3} α β) (fun (_x : Function.Embedding.{succ u2, succ u3} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u2, succ u3} α β) f))
but is expected to have type
  forall {G : Type.{u3}} {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u3} G] [_inst_2 : MulAction.{u3, u2} G β (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_1))] (g : G) (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{max (succ u1) (succ u2)} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) ᾰ) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.{succ u1, succ u2} α β) (instHSMul.{u3, max u1 u2} G (Function.Embedding.{succ u1, succ u2} α β) (Function.Embedding.smul.{u3, u1, u2} G α β _inst_1 _inst_2)) g f)) (HSMul.hSMul.{u3, max u1 u2, max u1 u2} G (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) ᾰ) (instHSMul.{u3, max u1 u2} G (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (Pi.instSMul.{u1, u2, u3} α G (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (fun (i : α) => MulAction.toSMul.{u3, u2} G ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) i) (DivInvMonoid.toMonoid.{u3} G (Group.toDivInvMonoid.{u3} G _inst_1)) _inst_2))) g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (Function.Embedding.{succ u1, succ u2} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u1, succ u2} α β)) f))
Case conversion may be inaccurate. Consider using '#align function.embedding.coe_smul Function.Embedding.coe_smulₓ'. -/
@[to_additive]
theorem coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • f :=
  rfl
#align function.embedding.coe_smul Function.Embedding.coe_smul
#align function.embedding.coe_vadd Function.Embedding.coe_vadd

instance [Group G] [Group G'] [SMul G G'] [MulAction G β] [MulAction G' β] [IsScalarTower G G' β] :
    IsScalarTower G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]
instance [Group G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
    SMulCommClass G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

instance [Group G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
    IsCentralScalar G (α ↪ β) :=
  ⟨fun r m => Function.Embedding.ext fun i => op_smul_eq_smul _ _⟩

@[to_additive]
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  FunLike.coe_injective.MulAction _ coe_smul

end Function.Embedding

