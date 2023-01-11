/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module group_theory.perm.via_embedding
! leanprover-community/mathlib commit a2d2e18906e2b62627646b5d5be856e6a642062f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Perm.Basic
import Mathbin.Logic.Equiv.Set

/-!
# `equiv.perm.via_embedding`, a noncomputable analogue of `equiv.perm.via_fintype_embedding`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

namespace Equiv

namespace Perm

variable (e : Perm α) (ι : α ↪ β)

open Classical

#print Equiv.Perm.viaEmbedding /-
/-- Noncomputable version of `equiv.perm.via_fintype_embedding` that does not assume `fintype` -/
noncomputable def viaEmbedding : Perm β :=
  extendDomain e (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding Equiv.Perm.viaEmbedding
-/

#print Equiv.Perm.viaEmbedding_apply /-
theorem viaEmbedding_apply (x : α) : e.viaEmbedding ι (ι x) = ι (e x) :=
  extendDomain_apply_image e (ofInjective ι.1 ι.2) x
#align equiv.perm.via_embedding_apply Equiv.Perm.viaEmbedding_apply
-/

#print Equiv.Perm.viaEmbedding_apply_of_not_mem /-
theorem viaEmbedding_apply_of_not_mem (x : β) (hx : x ∉ Set.range ι) : e.viaEmbedding ι x = x :=
  extendDomain_apply_not_subtype e (ofInjective ι.1 ι.2) hx
#align equiv.perm.via_embedding_apply_of_not_mem Equiv.Perm.viaEmbedding_apply_of_not_mem
-/

#print Equiv.Perm.viaEmbeddingHom /-
/-- `via_embedding` as a group homomorphism -/
noncomputable def viaEmbeddingHom : Perm α →* Perm β :=
  extendDomainHom (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom Equiv.Perm.viaEmbeddingHom
-/

/- warning: equiv.perm.via_embedding_hom_apply -> Equiv.Perm.viaEmbeddingHom_apply is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (ι : Function.Embedding.{succ u1, succ u2} α β), Eq.{succ u2} (Equiv.Perm.{succ u2} β) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (fun (_x : MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) => (Equiv.Perm.{succ u1} α) -> (Equiv.Perm.{succ u2} β)) (MonoidHom.hasCoeToFun.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.viaEmbeddingHom.{u1, u2} α β ι) e) (Equiv.Perm.viaEmbedding.{u1, u2} α β e ι)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (e : Equiv.Perm.{succ u1} α) (ι : Function.Embedding.{succ u1, succ u2} α β), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Equiv.Perm.{succ u1} α) => Equiv.Perm.{succ u2} β) e) (FunLike.coe.{max (succ u1) (succ u2), succ u1, succ u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (fun (_x : Equiv.Perm.{succ u1} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Equiv.Perm.{succ u1} α) => Equiv.Perm.{succ u2} β) _x) (MulHomClass.toFunLike.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} α) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α))))) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (MonoidHomClass.toMulHomClass.{max u1 u2, u1, u2} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))) (MonoidHom.monoidHomClass.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))))) (Equiv.Perm.viaEmbeddingHom.{u1, u2} α β ι) e) (Equiv.Perm.viaEmbedding.{u1, u2} α β e ι)
Case conversion may be inaccurate. Consider using '#align equiv.perm.via_embedding_hom_apply Equiv.Perm.viaEmbeddingHom_applyₓ'. -/
theorem viaEmbeddingHom_apply : viaEmbeddingHom ι e = viaEmbedding e ι :=
  rfl
#align equiv.perm.via_embedding_hom_apply Equiv.Perm.viaEmbeddingHom_apply

/- warning: equiv.perm.via_embedding_hom_injective -> Equiv.Perm.viaEmbeddingHom_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (ι : Function.Embedding.{succ u1, succ u2} α β), Function.Injective.{succ u1, succ u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (fun (_x : MonoidHom.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) => (Equiv.Perm.{succ u1} α) -> (Equiv.Perm.{succ u2} β)) (MonoidHom.hasCoeToFun.{u1, u2} (Equiv.Perm.{succ u1} α) (Equiv.Perm.{succ u2} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β))))) (Equiv.Perm.viaEmbeddingHom.{u1, u2} α β ι))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (ι : Function.Embedding.{succ u2, succ u1} α β), Function.Injective.{succ u2, succ u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Equiv.Perm.{succ u2} α) (fun (_x : Equiv.Perm.{succ u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2528 : Equiv.Perm.{succ u2} α) => Equiv.Perm.{succ u1} β) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} α) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (MonoidHom.monoidHomClass.{u2, u1} (Equiv.Perm.{succ u2} α) (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))))) (Equiv.Perm.viaEmbeddingHom.{u2, u1} α β ι))
Case conversion may be inaccurate. Consider using '#align equiv.perm.via_embedding_hom_injective Equiv.Perm.viaEmbeddingHom_injectiveₓ'. -/
theorem viaEmbeddingHom_injective : Function.Injective (viaEmbeddingHom ι) :=
  extendDomainHom_injective (ofInjective ι.1 ι.2)
#align equiv.perm.via_embedding_hom_injective Equiv.Perm.viaEmbeddingHom_injective

end Perm

end Equiv

