/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module order.rel_iso.group
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Order.RelIso.Basic

/-!
# Relation isomorphisms form a group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _} {r : α → α → Prop}

namespace RelIso

instance : Group (r ≃r r) where
  one := RelIso.refl r
  mul f₁ f₂ := f₂.trans f₁
  inv := RelIso.symm
  mul_assoc f₁ f₂ f₃ := rfl
  one_mul f := ext fun _ => rfl
  mul_one f := ext fun _ => rfl
  mul_left_inv f := ext f.symm_apply_apply

/- warning: rel_iso.coe_one -> RelIso.coe_one is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) (OfNat.ofNat.{u1} (RelIso.{u1, u1} α α r r) 1 (OfNat.mk.{u1} (RelIso.{u1, u1} α α r r) 1 (One.one.{u1} (RelIso.{u1, u1} α α r r) (MulOneClass.toHasOne.{u1} (RelIso.{u1, u1} α α r r) (Monoid.toMulOneClass.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.group.{u1} α r))))))))) (id.{succ u1} α)
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop}, Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (OfNat.ofNat.{u1} (RelIso.{u1, u1} α α r r) 1 (One.toOfNat1.{u1} (RelIso.{u1, u1} α α r r) (RightCancelMonoid.toOne.{u1} (RelIso.{u1, u1} α α r r) (CancelMonoid.toRightCancelMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toCancelMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r))))))))) (id.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_one RelIso.coe_oneₓ'. -/
@[simp]
theorem coe_one : ⇑(1 : r ≃r r) = id :=
  rfl
#align rel_iso.coe_one RelIso.coe_one

/- warning: rel_iso.coe_mul -> RelIso.coe_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e₁ : RelIso.{u1, u1} α α r r) (e₂ : RelIso.{u1, u1} α α r r), Eq.{succ u1} (α -> α) (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) (HMul.hMul.{u1, u1, u1} (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (instHMul.{u1} (RelIso.{u1, u1} α α r r) (MulOneClass.toHasMul.{u1} (RelIso.{u1, u1} α α r r) (Monoid.toMulOneClass.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.group.{u1} α r)))))) e₁ e₂)) (Function.comp.{succ u1, succ u1, succ u1} α α α (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e₁) (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e₂))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e₁ : RelIso.{u1, u1} α α r r) (e₂ : RelIso.{u1, u1} α α r r), Eq.{succ u1} (forall (ᾰ : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) ᾰ) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (HMul.hMul.{u1, u1, u1} (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (instHMul.{u1} (RelIso.{u1, u1} α α r r) (MulOneClass.toMul.{u1} (RelIso.{u1, u1} α α r r) (Monoid.toMulOneClass.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r)))))) e₁ e₂)))) (Function.comp.{succ u1, succ u1, succ u1} α α α (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e₁))) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e₂))))
Case conversion may be inaccurate. Consider using '#align rel_iso.coe_mul RelIso.coe_mulₓ'. -/
@[simp]
theorem coe_mul (e₁ e₂ : r ≃r r) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl
#align rel_iso.coe_mul RelIso.coe_mul

/- warning: rel_iso.mul_apply -> RelIso.mul_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e₁ : RelIso.{u1, u1} α α r r) (e₂ : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) (HMul.hMul.{u1, u1, u1} (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (instHMul.{u1} (RelIso.{u1, u1} α α r r) (MulOneClass.toHasMul.{u1} (RelIso.{u1, u1} α α r r) (Monoid.toMulOneClass.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.group.{u1} α r)))))) e₁ e₂) x) (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e₁ (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e₂ x))
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e₁ : RelIso.{u1, u1} α α r r) (e₂ : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) x) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (HMul.hMul.{u1, u1, u1} (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (RelIso.{u1, u1} α α r r) (instHMul.{u1} (RelIso.{u1, u1} α α r r) (MulOneClass.toMul.{u1} (RelIso.{u1, u1} α α r r) (Monoid.toMulOneClass.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toMonoid.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r)))))) e₁ e₂))) x) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e₁)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e₂)) x))
Case conversion may be inaccurate. Consider using '#align rel_iso.mul_apply RelIso.mul_applyₓ'. -/
theorem mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) :=
  rfl
#align rel_iso.mul_apply RelIso.mul_apply

/- warning: rel_iso.inv_apply_self -> RelIso.inv_apply_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) (Inv.inv.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toHasInv.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.group.{u1} α r))) e) (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e x)) x
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e)) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (Inv.inv.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toInv.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r))) e))) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e)) x)) x
Case conversion may be inaccurate. Consider using '#align rel_iso.inv_apply_self RelIso.inv_apply_selfₓ'. -/
@[simp]
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x
#align rel_iso.inv_apply_self RelIso.inv_apply_self

/- warning: rel_iso.apply_inv_self -> RelIso.apply_inv_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} α (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) e (coeFn.{succ u1, succ u1} (RelIso.{u1, u1} α α r r) (fun (_x : RelIso.{u1, u1} α α r r) => α -> α) (RelIso.hasCoeToFun.{u1, u1} α α r r) (Inv.inv.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toHasInv.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.group.{u1} α r))) e) x)) x
but is expected to have type
  forall {α : Type.{u1}} {r : α -> α -> Prop} (e : RelIso.{u1, u1} α α r r) (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) a) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (Inv.inv.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toInv.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r))) e))) x)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r e)) (FunLike.coe.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => α) _x) (EmbeddingLike.toFunLike.{succ u1, succ u1, succ u1} (Function.Embedding.{succ u1, succ u1} α α) α α (Function.instEmbeddingLikeEmbedding.{succ u1, succ u1} α α)) (RelEmbedding.toEmbedding.{u1, u1} α α r r (RelIso.toRelEmbedding.{u1, u1} α α r r (Inv.inv.{u1} (RelIso.{u1, u1} α α r r) (DivInvMonoid.toInv.{u1} (RelIso.{u1, u1} α α r r) (Group.toDivInvMonoid.{u1} (RelIso.{u1, u1} α α r r) (RelIso.instGroupRelIso.{u1} α r))) e))) x)) x
Case conversion may be inaccurate. Consider using '#align rel_iso.apply_inv_self RelIso.apply_inv_selfₓ'. -/
@[simp]
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x
#align rel_iso.apply_inv_self RelIso.apply_inv_self

end RelIso

