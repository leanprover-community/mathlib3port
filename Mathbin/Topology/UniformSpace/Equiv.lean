/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker

! This file was ported from Lean 3 source module topology.uniform_space.equiv
! leanprover-community/mathlib commit 48085f140e684306f9e7da907cd5932056d1aded
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.Pi

/-!
# Uniform isomorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

# Main definitions

* `uniform_equiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/


open Set Filter

universe u v

variable {α : Type u} {β : Type _} {γ : Type _} {δ : Type _}

#print UniformEquiv /-
-- not all spaces are homeomorphic to each other
/-- Uniform isomorphism between `α` and `β` -/
@[nolint has_nonempty_instance]
structure UniformEquiv (α : Type _) (β : Type _) [UniformSpace α] [UniformSpace β] extends
  α ≃ β where
  uniformContinuous_toFun : UniformContinuous to_fun
  uniformContinuous_invFun : UniformContinuous inv_fun
#align uniform_equiv UniformEquiv
-/

-- mathport name: «expr ≃ᵤ »
infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

instance : CoeFun (α ≃ᵤ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

/- warning: uniform_equiv.uniform_equiv_mk_coe -> UniformEquiv.uniformEquiv_mk_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (a : Equiv.{succ u1, succ u2} α β) (b : UniformContinuous.{u1, u2} α β _inst_1 _inst_2 (Equiv.toFun.{succ u1, succ u2} α β a)) (c : UniformContinuous.{u2, u1} β α _inst_2 _inst_1 (Equiv.invFun.{succ u1, succ u2} α β a)), Eq.{max (succ u1) (succ u2)} ((fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.mk.{u1, u2} α β _inst_1 _inst_2 a b c)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) (UniformEquiv.mk.{u1, u2} α β _inst_1 _inst_2 a b c)) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) a)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (a : Equiv.{succ u2, succ u1} α β) (b : UniformContinuous.{u2, u1} α β _inst_1 _inst_2 (Equiv.toFun.{succ u2, succ u1} α β a)) (c : UniformContinuous.{u1, u2} β α _inst_2 _inst_1 (Equiv.invFun.{succ u2, succ u1} α β a)), Eq.{max (succ u2) (succ u1)} (forall (a : α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) (UniformEquiv.mk.{u2, u1} α β _inst_1 _inst_2 a b c)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) a)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_equiv_mk_coe UniformEquiv.uniformEquiv_mk_coeₓ'. -/
@[simp]
theorem uniformEquiv_mk_coe (a : Equiv α β) (b c) : (UniformEquiv.mk a b c : α → β) = a :=
  rfl
#align uniform_equiv.uniform_equiv_mk_coe UniformEquiv.uniformEquiv_mk_coe

#print UniformEquiv.symm /-
/-- Inverse of a uniform isomorphism. -/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α
    where
  uniformContinuous_toFun := h.uniformContinuous_invFun
  uniformContinuous_invFun := h.uniformContinuous_toFun
  toEquiv := h.toEquiv.symm
#align uniform_equiv.symm UniformEquiv.symm
-/

#print UniformEquiv.Simps.apply /-
/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h
#align uniform_equiv.simps.apply UniformEquiv.Simps.apply
-/

#print UniformEquiv.Simps.symm_apply /-
/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵤ β) : β → α :=
  h.symm
#align uniform_equiv.simps.symm_apply UniformEquiv.Simps.symm_apply
-/

initialize_simps_projections UniformEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun → symm_apply,
  -toEquiv)

/- warning: uniform_equiv.coe_to_equiv -> UniformEquiv.coe_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (α -> β) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} α β) (fun (_x : Equiv.{succ u1, succ u2} α β) => α -> β) (Equiv.hasCoeToFun.{succ u1, succ u2} α β) (UniformEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 h)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : α), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : α) => β) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} α β) (UniformEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2 h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.coe_to_equiv UniformEquiv.coe_toEquivₓ'. -/
@[simp]
theorem coe_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl
#align uniform_equiv.coe_to_equiv UniformEquiv.coe_toEquiv

/- warning: uniform_equiv.coe_symm_to_equiv -> UniformEquiv.coe_symm_toEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (β -> α) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β (UniformEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2 h))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : β), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β (UniformEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2 h))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.coe_symm_to_equiv UniformEquiv.coe_symm_toEquivₓ'. -/
@[simp]
theorem coe_symm_toEquiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl
#align uniform_equiv.coe_symm_to_equiv UniformEquiv.coe_symm_toEquiv

/- warning: uniform_equiv.to_equiv_injective -> UniformEquiv.toEquiv_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Function.Injective.{max (succ u1) (succ u2), max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (Equiv.{succ u1, succ u2} α β) (UniformEquiv.toEquiv.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β], Function.Injective.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) (Equiv.{succ u2, succ u1} α β) (UniformEquiv.toEquiv.{u2, u1} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.to_equiv_injective UniformEquiv.toEquiv_injectiveₓ'. -/
theorem toEquiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl
#align uniform_equiv.to_equiv_injective UniformEquiv.toEquiv_injective

/- warning: uniform_equiv.ext -> UniformEquiv.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] {h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2} {h' : UniformEquiv.{u1, u2} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h' x)) -> (Eq.{max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) h h')
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] {h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2} {h' : UniformEquiv.{u2, u1} α β _inst_1 _inst_2}, (forall (x : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h x) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h' x)) -> (Eq.{max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) h h')
Case conversion may be inaccurate. Consider using '#align uniform_equiv.ext UniformEquiv.extₓ'. -/
@[ext]
theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
  toEquiv_injective <| Equiv.ext H
#align uniform_equiv.ext UniformEquiv.ext

#print UniformEquiv.refl /-
/-- Identity map as a uniform isomorphism. -/
@[simps (config := { fullyApplied := false }) apply]
protected def refl (α : Type _) [UniformSpace α] : α ≃ᵤ α
    where
  uniformContinuous_toFun := uniformContinuous_id
  uniformContinuous_invFun := uniformContinuous_id
  toEquiv := Equiv.refl α
#align uniform_equiv.refl UniformEquiv.refl
-/

#print UniformEquiv.trans /-
/-- Composition of two uniform isomorphisms. -/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ
    where
  uniformContinuous_toFun := h₂.uniformContinuous_toFun.comp h₁.uniformContinuous_toFun
  uniformContinuous_invFun := h₁.uniformContinuous_invFun.comp h₂.uniformContinuous_invFun
  toEquiv := Equiv.trans h₁.toEquiv h₂.toEquiv
#align uniform_equiv.trans UniformEquiv.trans
-/

/- warning: uniform_equiv.trans_apply -> UniformEquiv.trans_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] (h₁ : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u2, u3} β γ _inst_2 _inst_3) (a : α), Eq.{succ u3} γ (coeFn.{max (succ u1) (succ u3), max (succ u1) (succ u3)} (UniformEquiv.{u1, u3} α γ _inst_1 _inst_3) (fun (_x : UniformEquiv.{u1, u3} α γ _inst_1 _inst_3) => α -> γ) (UniformEquiv.hasCoeToFun.{u1, u3} α γ _inst_1 _inst_3) (UniformEquiv.trans.{u1, u2, u3} α β γ _inst_1 _inst_2 _inst_3 h₁ h₂) a) (coeFn.{max (succ u2) (succ u3), max (succ u2) (succ u3)} (UniformEquiv.{u2, u3} β γ _inst_2 _inst_3) (fun (_x : UniformEquiv.{u2, u3} β γ _inst_2 _inst_3) => β -> γ) (UniformEquiv.hasCoeToFun.{u2, u3} β γ _inst_2 _inst_3) h₂ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h₁ a))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : UniformSpace.{u3} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u1} γ] (h₁ : UniformEquiv.{u3, u2} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u2, u1} β γ _inst_2 _inst_3) (a : α), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) a) (FunLike.coe.{max (succ u3) (succ u1), succ u3, succ u1} (UniformEquiv.{u3, u1} α γ _inst_1 _inst_3) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u1), succ u3, succ u1} (UniformEquiv.{u3, u1} α γ _inst_1 _inst_3) α γ (EquivLike.toEmbeddingLike.{max (succ u3) (succ u1), succ u3, succ u1} (UniformEquiv.{u3, u1} α γ _inst_1 _inst_3) α γ (UniformEquiv.instEquivLikeUniformEquiv.{u3, u1} α γ _inst_1 _inst_3))) (UniformEquiv.trans.{u3, u2, u1} α β γ _inst_1 _inst_2 _inst_3 h₁ h₂) a) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} β γ _inst_2 _inst_3) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} β γ _inst_2 _inst_3) β γ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} β γ _inst_2 _inst_3) β γ (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} β γ _inst_2 _inst_3))) h₂ (FunLike.coe.{max (succ u3) (succ u2), succ u3, succ u2} (UniformEquiv.{u3, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u2), succ u3, succ u2} (UniformEquiv.{u3, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u3) (succ u2), succ u3, succ u2} (UniformEquiv.{u3, u2} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u3, u2} α β _inst_1 _inst_2))) h₁ a))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.trans_apply UniformEquiv.trans_applyₓ'. -/
@[simp]
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl
#align uniform_equiv.trans_apply UniformEquiv.trans_apply

/- warning: uniform_equiv.uniform_equiv_mk_coe_symm -> UniformEquiv.uniformEquiv_mk_coe_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (a : Equiv.{succ u1, succ u2} α β) (b : UniformContinuous.{u1, u2} α β _inst_1 _inst_2 (Equiv.toFun.{succ u1, succ u2} α β a)) (c : UniformContinuous.{u2, u1} β α _inst_2 _inst_1 (Equiv.invFun.{succ u1, succ u2} α β a)), Eq.{max (succ u2) (succ u1)} ((fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 (UniformEquiv.mk.{u1, u2} α β _inst_1 _inst_2 a b c))) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 (UniformEquiv.mk.{u1, u2} α β _inst_1 _inst_2 a b c))) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} β α) (fun (_x : Equiv.{succ u2, succ u1} β α) => β -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} β α) (Equiv.symm.{succ u1, succ u2} α β a))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (a : Equiv.{succ u2, succ u1} α β) (b : UniformContinuous.{u2, u1} α β _inst_1 _inst_2 (Equiv.toFun.{succ u2, succ u1} α β a)) (c : UniformContinuous.{u1, u2} β α _inst_2 _inst_1 (Equiv.invFun.{succ u2, succ u1} α β a)), Eq.{max (succ u2) (succ u1)} (forall (a : β), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 (UniformEquiv.mk.{u2, u1} α β _inst_1 _inst_2 a b c))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} β α) β (fun (_x : β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : β) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} β α) (Equiv.symm.{succ u2, succ u1} α β a))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_equiv_mk_coe_symm UniformEquiv.uniformEquiv_mk_coe_symmₓ'. -/
@[simp]
theorem uniformEquiv_mk_coe_symm (a : Equiv α β) (b c) :
    ((UniformEquiv.mk a b c).symm : β → α) = a.symm :=
  rfl
#align uniform_equiv.uniform_equiv_mk_coe_symm UniformEquiv.uniformEquiv_mk_coe_symm

#print UniformEquiv.refl_symm /-
@[simp]
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl
#align uniform_equiv.refl_symm UniformEquiv.refl_symm
-/

/- warning: uniform_equiv.uniform_continuous -> UniformEquiv.uniformContinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), UniformContinuous.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), UniformContinuous.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_continuous UniformEquiv.uniformContinuousₓ'. -/
protected theorem uniformContinuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniformContinuous_toFun
#align uniform_equiv.uniform_continuous UniformEquiv.uniformContinuous

/- warning: uniform_equiv.continuous -> UniformEquiv.continuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Continuous.{u1, u2} α β (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Continuous.{u2, u1} α β (UniformSpace.toTopologicalSpace.{u2} α _inst_1) (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.continuous UniformEquiv.continuousₓ'. -/
@[continuity]
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.UniformContinuous.Continuous
#align uniform_equiv.continuous UniformEquiv.continuous

/- warning: uniform_equiv.uniform_continuous_symm -> UniformEquiv.uniformContinuous_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), UniformContinuous.{u2, u1} β α _inst_2 _inst_1 (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), UniformContinuous.{u1, u2} β α _inst_2 _inst_1 (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_continuous_symm UniformEquiv.uniformContinuous_symmₓ'. -/
protected theorem uniformContinuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniformContinuous_invFun
#align uniform_equiv.uniform_continuous_symm UniformEquiv.uniformContinuous_symm

/- warning: uniform_equiv.continuous_symm -> UniformEquiv.continuous_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Continuous.{u2, u1} β α (UniformSpace.toTopologicalSpace.{u2} β _inst_2) (UniformSpace.toTopologicalSpace.{u1} α _inst_1) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Continuous.{u1, u2} β α (UniformSpace.toTopologicalSpace.{u1} β _inst_2) (UniformSpace.toTopologicalSpace.{u2} α _inst_1) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.continuous_symm UniformEquiv.continuous_symmₓ'. -/
-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniformContinuous_symm.Continuous
#align uniform_equiv.continuous_symm UniformEquiv.continuous_symm

#print UniformEquiv.toHomeomorph /-
/-- A uniform isomorphism as a homeomorphism. -/
@[simps]
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with
    continuous_toFun := e.Continuous
    continuous_invFun := e.continuous_symm }
#align uniform_equiv.to_homeomorph UniformEquiv.toHomeomorph
-/

/- warning: uniform_equiv.apply_symm_apply -> UniformEquiv.apply_symm_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (x : β), Eq.{succ u2} β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h) x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2) (x : β), Eq.{succ u1} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (a : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h) x)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h) x)) x
Case conversion may be inaccurate. Consider using '#align uniform_equiv.apply_symm_apply UniformEquiv.apply_symm_applyₓ'. -/
@[simp]
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x
#align uniform_equiv.apply_symm_apply UniformEquiv.apply_symm_apply

/- warning: uniform_equiv.symm_apply_apply -> UniformEquiv.symm_apply_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (x : α), Eq.{succ u1} α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h x)) x
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2) (x : α), Eq.{succ u2} ((fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h x)) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h x)) x
Case conversion may be inaccurate. Consider using '#align uniform_equiv.symm_apply_apply UniformEquiv.symm_apply_applyₓ'. -/
@[simp]
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align uniform_equiv.symm_apply_apply UniformEquiv.symm_apply_apply

/- warning: uniform_equiv.bijective -> UniformEquiv.bijective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Bijective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Bijective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.bijective UniformEquiv.bijectiveₓ'. -/
protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.Bijective
#align uniform_equiv.bijective UniformEquiv.bijective

/- warning: uniform_equiv.injective -> UniformEquiv.injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Injective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Injective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.injective UniformEquiv.injectiveₓ'. -/
protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.Injective
#align uniform_equiv.injective UniformEquiv.injective

/- warning: uniform_equiv.surjective -> UniformEquiv.surjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Function.Surjective.{succ u1, succ u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Function.Surjective.{succ u2, succ u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.surjective UniformEquiv.surjectiveₓ'. -/
protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.Surjective
#align uniform_equiv.surjective UniformEquiv.surjective

/- warning: uniform_equiv.change_inv -> UniformEquiv.changeInv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (f : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (g : β -> α), (Function.RightInverse.{succ u1, succ u2} α β g (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) f)) -> (UniformEquiv.{u1, u2} α β _inst_1 _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (f : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (g : β -> α), (Function.RightInverse.{succ u1, succ u2} α β g (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} α β _inst_1 _inst_2))) f)) -> (UniformEquiv.{u1, u2} α β _inst_1 _inst_2)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.change_inv UniformEquiv.changeInvₓ'. -/
/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
  have : g = f.symm :=
    funext fun x =>
      calc
        g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
        _ = f.symm x := by rw [hg x]
        
  { toFun := f
    invFun := g
    left_inv := by convert f.left_inv
    right_inv := by convert f.right_inv
    uniformContinuous_toFun := f.UniformContinuous
    uniformContinuous_invFun := by convert f.symm.uniform_continuous }
#align uniform_equiv.change_inv UniformEquiv.changeInv

/- warning: uniform_equiv.symm_comp_self -> UniformEquiv.symm_comp_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (α -> α) (Function.comp.{succ u1, succ u2, succ u1} α β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h)) (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)) (id.{succ u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (α -> α) (Function.comp.{succ u2, succ u1, succ u2} α β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h)) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)) (id.{succ u2} α)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.symm_comp_self UniformEquiv.symm_comp_selfₓ'. -/
@[simp]
theorem symm_comp_self (h : α ≃ᵤ β) : ⇑h.symm ∘ ⇑h = id :=
  funext h.symm_apply_apply
#align uniform_equiv.symm_comp_self UniformEquiv.symm_comp_self

/- warning: uniform_equiv.self_comp_symm -> UniformEquiv.self_comp_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (β -> β) (Function.comp.{succ u2, succ u1, succ u2} β α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))) (id.{succ u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (β -> β) (Function.comp.{succ u1, succ u2, succ u1} β α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))) (id.{succ u1} β)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.self_comp_symm UniformEquiv.self_comp_symmₓ'. -/
@[simp]
theorem self_comp_symm (h : α ≃ᵤ β) : ⇑h ∘ ⇑h.symm = id :=
  funext h.apply_symm_apply
#align uniform_equiv.self_comp_symm UniformEquiv.self_comp_symm

/- warning: uniform_equiv.range_coe -> UniformEquiv.range_coe is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u2} (Set.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u1} (Set.{u1} β) (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)) (Set.univ.{u1} β)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.range_coe UniformEquiv.range_coeₓ'. -/
@[simp]
theorem range_coe (h : α ≃ᵤ β) : range h = univ :=
  h.Surjective.range_eq
#align uniform_equiv.range_coe UniformEquiv.range_coe

/- warning: uniform_equiv.image_symm -> UniformEquiv.image_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u2} β) -> (Set.{u1} α)) (Set.image.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u1} β) -> (Set.{u2} α)) (Set.image.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.image_symm UniformEquiv.image_symmₓ'. -/
theorem image_symm (h : α ≃ᵤ β) : image h.symm = preimage h :=
  funext h.symm.toEquiv.image_eq_preimage
#align uniform_equiv.image_symm UniformEquiv.image_symm

/- warning: uniform_equiv.preimage_symm -> UniformEquiv.preimage_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} ((Set.{u1} α) -> (Set.{u2} β)) (Set.preimage.{u2, u1} β α (coeFn.{max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{u2, u1} β α _inst_2 _inst_1) (fun (_x : UniformEquiv.{u2, u1} β α _inst_2 _inst_1) => β -> α) (UniformEquiv.hasCoeToFun.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h))) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} ((Set.{u2} α) -> (Set.{u1} β)) (Set.preimage.{u1, u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β (fun (_x : β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : β) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u1, succ u2} (UniformEquiv.{u1, u2} β α _inst_2 _inst_1) β α (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} β α _inst_2 _inst_1))) (UniformEquiv.symm.{u2, u1} α β _inst_1 _inst_2 h))) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.preimage_symm UniformEquiv.preimage_symmₓ'. -/
theorem preimage_symm (h : α ≃ᵤ β) : preimage h.symm = image h :=
  (funext h.toEquiv.image_eq_preimage).symm
#align uniform_equiv.preimage_symm UniformEquiv.preimage_symm

/- warning: uniform_equiv.image_preimage -> UniformEquiv.image_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) s)) s
Case conversion may be inaccurate. Consider using '#align uniform_equiv.image_preimage UniformEquiv.image_preimageₓ'. -/
@[simp]
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s
#align uniform_equiv.image_preimage UniformEquiv.image_preimage

/- warning: uniform_equiv.preimage_image -> UniformEquiv.preimage_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.preimage.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) s)) s
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2) (s : Set.{u2} α), Eq.{succ u2} (Set.{u2} α) (Set.preimage.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) (Set.image.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) s)) s
Case conversion may be inaccurate. Consider using '#align uniform_equiv.preimage_image UniformEquiv.preimage_imageₓ'. -/
@[simp]
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s
#align uniform_equiv.preimage_image UniformEquiv.preimage_image

/- warning: uniform_equiv.uniform_inducing -> UniformEquiv.uniformInducing is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), UniformInducing.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), UniformInducing.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_inducing UniformEquiv.uniformInducingₓ'. -/
protected theorem uniformInducing (h : α ≃ᵤ β) : UniformInducing h :=
  uniformInducing_of_compose h.UniformContinuous h.symm.UniformContinuous <| by
    simp only [symm_comp_self, uniformInducing_id]
#align uniform_equiv.uniform_inducing UniformEquiv.uniformInducing

/- warning: uniform_equiv.comap_eq -> UniformEquiv.comap_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), Eq.{succ u1} (UniformSpace.{u1} α) (UniformSpace.comap.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h) _inst_2) _inst_1
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), Eq.{succ u2} (UniformSpace.{u2} α) (UniformSpace.comap.{u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h) _inst_2) _inst_1
Case conversion may be inaccurate. Consider using '#align uniform_equiv.comap_eq UniformEquiv.comap_eqₓ'. -/
theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› := by
  ext : 1 <;> exact h.uniform_inducing.comap_uniformity
#align uniform_equiv.comap_eq UniformEquiv.comap_eq

/- warning: uniform_equiv.uniform_embedding -> UniformEquiv.uniformEmbedding is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (h : UniformEquiv.{u1, u2} α β _inst_1 _inst_2), UniformEmbedding.{u1, u2} α β _inst_1 _inst_2 (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β] (h : UniformEquiv.{u2, u1} α β _inst_1 _inst_2), UniformEmbedding.{u2, u1} α β _inst_1 _inst_2 (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} α β _inst_1 _inst_2))) h)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.uniform_embedding UniformEquiv.uniformEmbeddingₓ'. -/
protected theorem uniformEmbedding (h : α ≃ᵤ β) : UniformEmbedding h :=
  ⟨h.UniformInducing, h.Injective⟩
#align uniform_equiv.uniform_embedding UniformEquiv.uniformEmbedding

#print UniformEquiv.ofUniformEmbedding /-
/-- Uniform equiv given a uniform embedding. -/
noncomputable def ofUniformEmbedding (f : α → β) (hf : UniformEmbedding f) : α ≃ᵤ Set.range f
    where
  uniformContinuous_toFun := hf.to_uniformInducing.UniformContinuous.subtype_mk _
  uniformContinuous_invFun := by
    simp [hf.to_uniform_inducing.uniform_continuous_iff, uniformContinuous_subtype_val]
  toEquiv := Equiv.ofInjective f hf.inj
#align uniform_equiv.of_uniform_embedding UniformEquiv.ofUniformEmbedding
-/

#print UniformEquiv.setCongr /-
/-- If two sets are equal, then they are uniformly equivalent. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t
    where
  uniformContinuous_toFun := uniformContinuous_subtype_val.subtype_mk _
  uniformContinuous_invFun := uniformContinuous_subtype_val.subtype_mk _
  toEquiv := Equiv.setCongr h
#align uniform_equiv.set_congr UniformEquiv.setCongr
-/

/- warning: uniform_equiv.prod_congr -> UniformEquiv.prodCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ], (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) -> (UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4) -> (UniformEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ], (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) -> (UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4) -> (UniformEquiv.{max u3 u1, max u4 u2} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (instUniformSpaceProd.{u1, u3} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u2, u4} β δ _inst_2 _inst_4))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_congr UniformEquiv.prodCongrₓ'. -/
/-- Product of two uniform isomorphisms. -/
def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ
    where
  uniformContinuous_toFun :=
    (h₁.UniformContinuous.comp uniformContinuous_fst).prod_mk
      (h₂.UniformContinuous.comp uniformContinuous_snd)
  uniformContinuous_invFun :=
    (h₁.symm.UniformContinuous.comp uniformContinuous_fst).prod_mk
      (h₂.symm.UniformContinuous.comp uniformContinuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv
#align uniform_equiv.prod_congr UniformEquiv.prodCongr

/- warning: uniform_equiv.prod_congr_symm -> UniformEquiv.prodCongr_symm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ] (h₁ : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ (max u2 u4)) (succ (max u1 u3))} (UniformEquiv.{max u2 u4, max u1 u3} (Prod.{u2, u4} β δ) (Prod.{u1, u3} α γ) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3)) (UniformEquiv.symm.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4) (UniformEquiv.prodCongr.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (UniformEquiv.prodCongr.{u2, u1, u4, u3} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (UniformEquiv.symm.{u1, u2} α β _inst_1 _inst_2 h₁) (UniformEquiv.symm.{u3, u4} γ δ _inst_3 _inst_4 h₂))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : UniformSpace.{u4} α] [_inst_2 : UniformSpace.{u3} β] [_inst_3 : UniformSpace.{u2} γ] [_inst_4 : UniformSpace.{u1} δ] (h₁ : UniformEquiv.{u4, u3} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u2, u1} γ δ _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (UniformEquiv.{max u3 u1, max u4 u2} (Prod.{u3, u1} β δ) (Prod.{u4, u2} α γ) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3)) (UniformEquiv.symm.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4) (UniformEquiv.prodCongr.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (UniformEquiv.prodCongr.{u3, u4, u1, u2} β α δ γ _inst_2 _inst_1 _inst_4 _inst_3 (UniformEquiv.symm.{u4, u3} α β _inst_1 _inst_2 h₁) (UniformEquiv.symm.{u2, u1} γ δ _inst_3 _inst_4 h₂))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_congr_symm UniformEquiv.prodCongr_symmₓ'. -/
@[simp]
theorem prodCongr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl
#align uniform_equiv.prod_congr_symm UniformEquiv.prodCongr_symm

/- warning: uniform_equiv.coe_prod_congr -> UniformEquiv.coe_prodCongr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} {δ : Type.{u4}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ] [_inst_4 : UniformSpace.{u4} δ] (h₁ : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4), Eq.{max (succ (max u1 u3)) (succ (max u2 u4))} ((Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (coeFn.{max (succ (max u1 u3)) (succ (max u2 u4)), max (succ (max u1 u3)) (succ (max u2 u4))} (UniformEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4)) (fun (_x : UniformEquiv.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4)) => (Prod.{u1, u3} α γ) -> (Prod.{u2, u4} β δ)) (UniformEquiv.hasCoeToFun.{max u1 u3, max u2 u4} (Prod.{u1, u3} α γ) (Prod.{u2, u4} β δ) (Prod.uniformSpace.{u1, u3} α γ _inst_1 _inst_3) (Prod.uniformSpace.{u2, u4} β δ _inst_2 _inst_4)) (UniformEquiv.prodCongr.{u1, u2, u3, u4} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Prod.map.{u1, u2, u3, u4} α β γ δ (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) h₁) (coeFn.{max (succ u3) (succ u4), max (succ u3) (succ u4)} (UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4) (fun (_x : UniformEquiv.{u3, u4} γ δ _inst_3 _inst_4) => γ -> δ) (UniformEquiv.hasCoeToFun.{u3, u4} γ δ _inst_3 _inst_4) h₂))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {γ : Type.{u2}} {δ : Type.{u1}} [_inst_1 : UniformSpace.{u4} α] [_inst_2 : UniformSpace.{u3} β] [_inst_3 : UniformSpace.{u2} γ] [_inst_4 : UniformSpace.{u1} δ] (h₁ : UniformEquiv.{u4, u3} α β _inst_1 _inst_2) (h₂ : UniformEquiv.{u2, u1} γ δ _inst_3 _inst_4), Eq.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1)} (forall (ᾰ : Prod.{u4, u2} α γ), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u4, u2} α γ) => Prod.{u3, u1} β δ) ᾰ) (FunLike.coe.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (succ u4) (succ u2), max (succ u3) (succ u1)} (UniformEquiv.{max u2 u4, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (fun (_x : Prod.{u4, u2} α γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u4, u2} α γ) => Prod.{u3, u1} β δ) _x) (EmbeddingLike.toFunLike.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (succ u4) (succ u2), max (succ u3) (succ u1)} (UniformEquiv.{max u2 u4, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (EquivLike.toEmbeddingLike.{max (max (max (succ u4) (succ u3)) (succ u2)) (succ u1), max (succ u4) (succ u2), max (succ u3) (succ u1)} (UniformEquiv.{max u2 u4, max u1 u3} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4)) (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (UniformEquiv.instEquivLikeUniformEquiv.{max u4 u2, max u3 u1} (Prod.{u4, u2} α γ) (Prod.{u3, u1} β δ) (instUniformSpaceProd.{u4, u2} α γ _inst_1 _inst_3) (instUniformSpaceProd.{u3, u1} β δ _inst_2 _inst_4)))) (UniformEquiv.prodCongr.{u4, u3, u2, u1} α β γ δ _inst_1 _inst_2 _inst_3 _inst_4 h₁ h₂)) (Prod.map.{u4, u3, u2, u1} α β γ δ (FunLike.coe.{max (succ u4) (succ u3), succ u4, succ u3} (UniformEquiv.{u4, u3} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u4) (succ u3), succ u4, succ u3} (UniformEquiv.{u4, u3} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u4) (succ u3), succ u4, succ u3} (UniformEquiv.{u4, u3} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u4, u3} α β _inst_1 _inst_2))) h₁) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} γ δ _inst_3 _inst_4) γ (fun (_x : γ) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : γ) => δ) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} γ δ _inst_3 _inst_4) γ δ (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), succ u2, succ u1} (UniformEquiv.{u2, u1} γ δ _inst_3 _inst_4) γ δ (UniformEquiv.instEquivLikeUniformEquiv.{u2, u1} γ δ _inst_3 _inst_4))) h₂))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.coe_prod_congr UniformEquiv.coe_prodCongrₓ'. -/
@[simp]
theorem coe_prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl
#align uniform_equiv.coe_prod_congr UniformEquiv.coe_prodCongr

section

variable (α β γ)

/- warning: uniform_equiv.prod_comm -> UniformEquiv.prodComm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1)
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], UniformEquiv.{max u2 u1, max u1 u2} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) (instUniformSpaceProd.{u2, u1} β α _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_comm UniformEquiv.prodCommₓ'. -/
/-- `α × β` is uniformly isomorphic to `β × α`. -/
def prodComm : α × β ≃ᵤ β × α
    where
  uniformContinuous_toFun := uniformContinuous_snd.prod_mk uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_snd.prod_mk uniformContinuous_fst
  toEquiv := Equiv.prodComm α β
#align uniform_equiv.prod_comm UniformEquiv.prodComm

/- warning: uniform_equiv.prod_comm_symm -> UniformEquiv.prodComm_symm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ (max u2 u1)) (succ (max u1 u2))} (UniformEquiv.{max u2 u1, max u1 u2} (Prod.{u2, u1} β α) (Prod.{u1, u2} α β) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2)) (UniformEquiv.symm.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1) (UniformEquiv.prodComm.{u1, u2} α β _inst_1 _inst_2)) (UniformEquiv.prodComm.{u2, u1} β α _inst_2 _inst_1)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (UniformEquiv.{max u2 u1, max u2 u1} (Prod.{u1, u2} β α) (Prod.{u2, u1} α β) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2)) (UniformEquiv.symm.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1) (UniformEquiv.prodComm.{u2, u1} α β _inst_1 _inst_2)) (UniformEquiv.prodComm.{u1, u2} β α _inst_2 _inst_1)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_comm_symm UniformEquiv.prodComm_symmₓ'. -/
@[simp]
theorem prodComm_symm : (prodComm α β).symm = prodComm β α :=
  rfl
#align uniform_equiv.prod_comm_symm UniformEquiv.prodComm_symm

/- warning: uniform_equiv.coe_prod_comm -> UniformEquiv.coe_prodComm is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β], Eq.{max (succ (max u1 u2)) (succ (max u2 u1))} ((Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (coeFn.{max (succ (max u1 u2)) (succ (max u2 u1)), max (succ (max u1 u2)) (succ (max u2 u1))} (UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1)) (fun (_x : UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1)) => (Prod.{u1, u2} α β) -> (Prod.{u2, u1} β α)) (UniformEquiv.hasCoeToFun.{max u1 u2, max u2 u1} (Prod.{u1, u2} α β) (Prod.{u2, u1} β α) (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) (Prod.uniformSpace.{u2, u1} β α _inst_2 _inst_1)) (UniformEquiv.prodComm.{u1, u2} α β _inst_1 _inst_2)) (Prod.swap.{u1, u2} α β)
but is expected to have type
  forall (α : Type.{u2}) (β : Type.{u1}) [_inst_1 : UniformSpace.{u2} α] [_inst_2 : UniformSpace.{u1} β], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u2, u1} α β), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (fun (_x : Prod.{u2, u1} α β) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u2, u1} α β) => Prod.{u1, u2} β α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), max (succ u2) (succ u1)} (UniformEquiv.{max u1 u2, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1)) (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (UniformEquiv.instEquivLikeUniformEquiv.{max u2 u1, max u2 u1} (Prod.{u2, u1} α β) (Prod.{u1, u2} β α) (instUniformSpaceProd.{u2, u1} α β _inst_1 _inst_2) (instUniformSpaceProd.{u1, u2} β α _inst_2 _inst_1)))) (UniformEquiv.prodComm.{u2, u1} α β _inst_1 _inst_2)) (Prod.swap.{u2, u1} α β)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.coe_prod_comm UniformEquiv.coe_prodCommₓ'. -/
@[simp]
theorem coe_prodComm : ⇑(prodComm α β) = Prod.swap :=
  rfl
#align uniform_equiv.coe_prod_comm UniformEquiv.coe_prodComm

/- warning: uniform_equiv.prod_assoc -> UniformEquiv.prodAssoc is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) (β : Type.{u2}) (γ : Type.{u3}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ], UniformEquiv.{max (max u1 u2) u3, max u1 u2 u3} (Prod.{max u1 u2, u3} (Prod.{u1, u2} α β) γ) (Prod.{u1, max u2 u3} α (Prod.{u2, u3} β γ)) (Prod.uniformSpace.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (Prod.uniformSpace.{u1, u2} α β _inst_1 _inst_2) _inst_3) (Prod.uniformSpace.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (Prod.uniformSpace.{u2, u3} β γ _inst_2 _inst_3))
but is expected to have type
  forall (α : Type.{u1}) (β : Type.{u2}) (γ : Type.{u3}) [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] [_inst_3 : UniformSpace.{u3} γ], UniformEquiv.{max u3 u2 u1, max (max u3 u2) u1} (Prod.{max u2 u1, u3} (Prod.{u1, u2} α β) γ) (Prod.{u1, max u3 u2} α (Prod.{u2, u3} β γ)) (instUniformSpaceProd.{max u1 u2, u3} (Prod.{u1, u2} α β) γ (instUniformSpaceProd.{u1, u2} α β _inst_1 _inst_2) _inst_3) (instUniformSpaceProd.{u1, max u2 u3} α (Prod.{u2, u3} β γ) _inst_1 (instUniformSpaceProd.{u2, u3} β γ _inst_2 _inst_3))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_assoc UniformEquiv.prodAssocₓ'. -/
/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ
    where
  uniformContinuous_toFun :=
    (uniformContinuous_fst.comp uniformContinuous_fst).prod_mk
      ((uniformContinuous_snd.comp uniformContinuous_fst).prod_mk uniformContinuous_snd)
  uniformContinuous_invFun :=
    (uniformContinuous_fst.prod_mk (uniformContinuous_fst.comp uniformContinuous_snd)).prod_mk
      (uniformContinuous_snd.comp uniformContinuous_snd)
  toEquiv := Equiv.prodAssoc α β γ
#align uniform_equiv.prod_assoc UniformEquiv.prodAssoc

/- warning: uniform_equiv.prod_punit -> UniformEquiv.prodPunit is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{max u1 u2, u1} (Prod.{u1, u2} α PUnit.{succ u2}) α (Prod.uniformSpace.{u1, u2} α PUnit.{succ u2} _inst_1 PUnit.uniformSpace.{u2}) _inst_1
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{max u2 u1, u1} (Prod.{u1, u2} α PUnit.{succ u2}) α (instUniformSpaceProd.{u1, u2} α PUnit.{succ u2} _inst_1 instUniformSpacePUnit.{u2}) _inst_1
Case conversion may be inaccurate. Consider using '#align uniform_equiv.prod_punit UniformEquiv.prodPunitₓ'. -/
/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps (config := { fullyApplied := false }) apply]
def prodPunit : α × PUnit ≃ᵤ α where
  toEquiv := Equiv.prodPUnit α
  uniformContinuous_toFun := uniformContinuous_fst
  uniformContinuous_invFun := uniformContinuous_id.prod_mk uniformContinuous_const
#align uniform_equiv.prod_punit UniformEquiv.prodPunit

/- warning: uniform_equiv.punit_prod -> UniformEquiv.punitProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.uniformSpace.{u2, u1} PUnit.{succ u2} α PUnit.uniformSpace.{u2} _inst_1) _inst_1
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{max u1 u2, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (instUniformSpaceProd.{u2, u1} PUnit.{succ u2} α instUniformSpacePUnit.{u2} _inst_1) _inst_1
Case conversion may be inaccurate. Consider using '#align uniform_equiv.punit_prod UniformEquiv.punitProdₓ'. -/
/-- `{*} × α` is uniformly isomorphic to `α`. -/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPunit _)
#align uniform_equiv.punit_prod UniformEquiv.punitProd

/- warning: uniform_equiv.coe_punit_prod -> UniformEquiv.coe_punitProd is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], Eq.{max (succ (max u2 u1)) (succ u1)} ((Prod.{u2, u1} PUnit.{succ u2} α) -> α) (coeFn.{max (succ (max u2 u1)) (succ u1), max (succ (max u2 u1)) (succ u1)} (UniformEquiv.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.uniformSpace.{u2, u1} PUnit.{succ u2} α PUnit.uniformSpace.{u2} _inst_1) _inst_1) (fun (_x : UniformEquiv.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.uniformSpace.{u2, u1} PUnit.{succ u2} α PUnit.uniformSpace.{u2} _inst_1) _inst_1) => (Prod.{u2, u1} PUnit.{succ u2} α) -> α) (UniformEquiv.hasCoeToFun.{max u2 u1, u1} (Prod.{u2, u1} PUnit.{succ u2} α) α (Prod.uniformSpace.{u2, u1} PUnit.{succ u2} α PUnit.uniformSpace.{u2} _inst_1) _inst_1) (UniformEquiv.punitProd.{u1, u2} α _inst_1)) (Prod.snd.{u2, u1} PUnit.{succ u2} α)
but is expected to have type
  forall (α : Type.{u2}) [_inst_1 : UniformSpace.{u2} α], Eq.{max (succ u2) (succ u1)} (forall (ᾰ : Prod.{u1, u2} PUnit.{succ u1} α), (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u1, u2} PUnit.{succ u1} α) => α) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u2} (UniformEquiv.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instUniformSpaceProd.{u1, u2} PUnit.{succ u1} α instUniformSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) (fun (_x : Prod.{u1, u2} PUnit.{succ u1} α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Prod.{u1, u2} PUnit.{succ u1} α) => α) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u2} (UniformEquiv.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instUniformSpaceProd.{u1, u2} PUnit.{succ u1} α instUniformSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) α (EquivLike.toEmbeddingLike.{max (succ u2) (succ u1), max (succ u2) (succ u1), succ u2} (UniformEquiv.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instUniformSpaceProd.{u1, u2} PUnit.{succ u1} α instUniformSpacePUnit.{u1} _inst_1) _inst_1) (Prod.{u1, u2} PUnit.{succ u1} α) α (UniformEquiv.instEquivLikeUniformEquiv.{max u2 u1, u2} (Prod.{u1, u2} PUnit.{succ u1} α) α (instUniformSpaceProd.{u1, u2} PUnit.{succ u1} α instUniformSpacePUnit.{u1} _inst_1) _inst_1))) (UniformEquiv.punitProd.{u2, u1} α _inst_1)) (Prod.snd.{u1, u2} PUnit.{succ u1} α)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.coe_punit_prod UniformEquiv.coe_punitProdₓ'. -/
@[simp]
theorem coe_punitProd : ⇑(punitProd α) = Prod.snd :=
  rfl
#align uniform_equiv.coe_punit_prod UniformEquiv.coe_punitProd

#print UniformEquiv.ulift /-
/-- Uniform equivalence between `ulift α` and `α`. -/
def ulift : ULift.{v, u} α ≃ᵤ α :=
  { Equiv.ulift with
    uniformContinuous_toFun := uniformContinuous_comap
    uniformContinuous_invFun :=
      by
      have hf : UniformInducing (@Equiv.ulift.{v, u} α).toFun := ⟨rfl⟩
      simp_rw [hf.uniform_continuous_iff]
      exact uniformContinuous_id }
#align uniform_equiv.ulift UniformEquiv.ulift
-/

end

#print UniformEquiv.funUnique /-
/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (ι α : Type _) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α
    where
  toEquiv := Equiv.funUnique ι α
  uniformContinuous_toFun := Pi.uniformContinuous_proj _ _
  uniformContinuous_invFun := uniformContinuous_pi.mpr fun _ => uniformContinuous_id
#align uniform_equiv.fun_unique UniformEquiv.funUnique
-/

/- warning: uniform_equiv.pi_fin_two -> UniformEquiv.piFinTwo is a dubious translation:
lean 3 declaration is
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> Type.{u1}) [_inst_5 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), UniformSpace.{u1} (α i)], UniformEquiv.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_2)))))) (Pi.uniformSpace.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => α i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_5 i)) (Prod.uniformSpace.{u1, u1} (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_1))))) (α (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_2))))) (_inst_5 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 0 (Zero.zero.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasZeroOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_1))))) (_inst_5 (OfNat.ofNat.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (OfNat.mk.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) 1 (One.one.{0} (Fin (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))) (Fin.hasOneOfNeZero (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)) UniformEquiv.piFinTwo._proof_2))))))
but is expected to have type
  forall (α : (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> Type.{u1}) [_inst_5 : forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), UniformSpace.{u1} (α i)], UniformEquiv.{u1, u1} (forall (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))), α i) (Prod.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (Pi.uniformSpace.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => α i) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_5 i)) (instUniformSpaceProd.{u1, u1} (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (α (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_5 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 0 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 0 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (_inst_5 (OfNat.ofNat.{0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) 1 (Fin.instOfNatFin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)) 1 (NeZero.succ (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align uniform_equiv.pi_fin_two UniformEquiv.piFinTwoₓ'. -/
/-- Uniform isomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo (α : Fin 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1
    where
  toEquiv := piFinTwoEquiv α
  uniformContinuous_toFun := (Pi.uniformContinuous_proj _ 0).prod_mk (Pi.uniformContinuous_proj _ 1)
  uniformContinuous_invFun :=
    uniformContinuous_pi.mpr <| Fin.forall_fin_two.2 ⟨uniformContinuous_fst, uniformContinuous_snd⟩
#align uniform_equiv.pi_fin_two UniformEquiv.piFinTwo

/- warning: uniform_equiv.fin_two_arrow -> UniformEquiv.finTwoArrow is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{u1, u1} ((Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) -> α) (Prod.{u1, u1} α α) (Pi.uniformSpace.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => α) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) => _inst_1)) (Prod.uniformSpace.{u1, u1} α α _inst_1 _inst_1)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : UniformSpace.{u1} α], UniformEquiv.{u1, u1} ((Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) -> α) (Prod.{u1, u1} α α) (Pi.uniformSpace.{u1, 0} (Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (fun (ᾰ : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => α) (fun (i : Fin (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) => _inst_1)) (instUniformSpaceProd.{u1, u1} α α _inst_1 _inst_1)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.fin_two_arrow UniformEquiv.finTwoArrowₓ'. -/
/-- Uniform isomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Fin 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }
#align uniform_equiv.fin_two_arrow UniformEquiv.finTwoArrow

/- warning: uniform_equiv.image -> UniformEquiv.image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (e : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), UniformEquiv.{u1, u2} (coeSort.{succ u1, succ (succ u1)} (Set.{u1} α) Type.{u1} (Set.hasCoeToSort.{u1} α) s) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) (Subtype.uniformSpace.{u1} α (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) _inst_1) (Subtype.uniformSpace.{u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.image.{u1, u2} α β (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (fun (_x : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) => α -> β) (UniformEquiv.hasCoeToFun.{u1, u2} α β _inst_1 _inst_2) e) s)) _inst_2)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : UniformSpace.{u1} α] [_inst_2 : UniformSpace.{u2} β] (e : UniformEquiv.{u1, u2} α β _inst_1 _inst_2) (s : Set.{u1} α), UniformEquiv.{u1, u2} (Set.Elem.{u1} α s) (Set.Elem.{u2} β (Set.image.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} α β _inst_1 _inst_2))) e) s)) (instUniformSpaceSubtype.{u1} α (fun (x : α) => Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) _inst_1) (instUniformSpaceSubtype.{u2} β (fun (x : β) => Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (Set.image.{u1, u2} α β (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (EquivLike.toEmbeddingLike.{max (succ u1) (succ u2), succ u1, succ u2} (UniformEquiv.{u1, u2} α β _inst_1 _inst_2) α β (UniformEquiv.instEquivLikeUniformEquiv.{u1, u2} α β _inst_1 _inst_2))) e) s)) _inst_2)
Case conversion may be inaccurate. Consider using '#align uniform_equiv.image UniformEquiv.imageₓ'. -/
/-- A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s
    where
  uniformContinuous_toFun := (e.UniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  uniformContinuous_invFun :=
    (e.symm.UniformContinuous.comp uniformContinuous_subtype_val).subtype_mk _
  toEquiv := e.toEquiv.image s
#align uniform_equiv.image UniformEquiv.image

end UniformEquiv

#print Equiv.toUniformEquivOfUniformInducing /-
/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
@[simps]
def Equiv.toUniformEquivOfUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β)
    (hf : UniformInducing f) : α ≃ᵤ β :=
  { f with
    uniformContinuous_toFun := hf.UniformContinuous
    uniformContinuous_invFun := hf.uniformContinuous_iff.2 <| by simpa using uniformContinuous_id }
#align equiv.to_uniform_equiv_of_uniform_inducing Equiv.toUniformEquivOfUniformInducing
-/

