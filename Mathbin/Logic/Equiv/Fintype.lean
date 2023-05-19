/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module logic.equiv.fintype
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Perm.Sign
import Mathbin.Logic.Equiv.Defs

/-! # Equivalence between fintypes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some basic results on equivalences where one or both
sides of the equivalence are `fintype`s.

# Main definitions

 - `function.embedding.to_equiv_range`: computably turn an embedding of a
   fintype into an `equiv` of the domain to its range
 - `equiv.perm.via_fintype_embedding : perm α → (α ↪ β) → perm β` extends the domain of
   a permutation, fixing everything outside the range of the embedding

# Implementation details

 - `function.embedding.to_equiv_range` uses a computable inverse, but one that has poor
   computational performance, since it operates by exhaustive search over the input `fintype`s.
-/


variable {α β : Type _} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

#print Function.Embedding.toEquivRange /-
/-- Computably turn an embedding `f : α ↪ β` into an equiv `α ≃ set.range f`,
if `α` is a `fintype`. Has poor computational performance, due to exhaustive searching in
constructed inverse. When a better inverse is known, use `equiv.of_left_inverse'` or
`equiv.of_left_inverse` instead. This is the computable version of `equiv.of_injective`.
-/
def Function.Embedding.toEquivRange : α ≃ Set.range f :=
  ⟨fun a => ⟨f a, Set.mem_range_self a⟩, f.invOfMemRange, fun _ => by simp, fun _ => by simp⟩
#align function.embedding.to_equiv_range Function.Embedding.toEquivRange
-/

#print Function.Embedding.toEquivRange_apply /-
@[simp]
theorem Function.Embedding.toEquivRange_apply (a : α) :
    f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl
#align function.embedding.to_equiv_range_apply Function.Embedding.toEquivRange_apply
-/

/- warning: function.embedding.to_equiv_range_symm_apply_self -> Function.Embedding.toEquivRange_symm_apply_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β) (a : α), Eq.{succ u1} α (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) α) (fun (_x : Equiv.{succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) α) => (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) -> α) (Equiv.hasCoeToFun.{succ u2, succ u1} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) α) (Equiv.symm.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) (Function.Embedding.toEquivRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f)) (Subtype.mk.{succ u2} β (fun (x : β) => Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f))) (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f a) (Set.mem_range_self.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) a))) a
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β) (a : α), Eq.{succ u2} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) => α) (Subtype.mk.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Set.mem_range_self.{succ u2, u1} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) a))) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) α) (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (fun (_x : Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.812 : Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (a : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) a) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) => α) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) α) (Equiv.symm.{succ u2, succ u1} α (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (Function.Embedding.toEquivRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f)) (Subtype.mk.{succ u1} β (fun (x : β) => Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f))) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f a) (Set.mem_range_self.{succ u2, u1} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) a))) a
Case conversion may be inaccurate. Consider using '#align function.embedding.to_equiv_range_symm_apply_self Function.Embedding.toEquivRange_symm_apply_selfₓ'. -/
@[simp]
theorem Function.Embedding.toEquivRange_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by simp [Equiv.symm_apply_eq]
#align function.embedding.to_equiv_range_symm_apply_self Function.Embedding.toEquivRange_symm_apply_self

/- warning: function.embedding.to_equiv_range_eq_of_injective -> Function.Embedding.toEquivRange_eq_ofInjective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (f : Function.Embedding.{succ u1, succ u2} α β), Eq.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1)} (Equiv.{succ u1, succ u2} α (coeSort.{succ u2, succ (succ u2)} (Set.{u2} β) Type.{u2} (Set.hasCoeToSort.{u2} β) (Set.range.{u2, succ u1} β α (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f)))) (Function.Embedding.toEquivRange.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f) (Equiv.ofInjective.{succ u1, u2} α β (coeFn.{max 1 (succ u1) (succ u2), max (succ u1) (succ u2)} (Function.Embedding.{succ u1, succ u2} α β) (fun (_x : Function.Embedding.{succ u1, succ u2} α β) => α -> β) (Function.Embedding.hasCoeToFun.{succ u1, succ u2} α β) f) (Function.Embedding.injective.{succ u1, succ u2} α β f))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] (f : Function.Embedding.{succ u2, succ u1} α β), Eq.{max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} α (Set.Elem.{u1} β (Set.range.{u1, succ u2} β α (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f)))) (Function.Embedding.toEquivRange.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) f) (Equiv.ofInjective.{succ u2, u1} α β (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => β) _x) (EmbeddingLike.toFunLike.{max (succ u2) (succ u1), succ u2, succ u1} (Function.Embedding.{succ u2, succ u1} α β) α β (Function.instEmbeddingLikeEmbedding.{succ u2, succ u1} α β)) f) (Function.Embedding.injective.{succ u1, succ u2} α β f))
Case conversion may be inaccurate. Consider using '#align function.embedding.to_equiv_range_eq_of_injective Function.Embedding.toEquivRange_eq_ofInjectiveₓ'. -/
theorem Function.Embedding.toEquivRange_eq_ofInjective :
    f.toEquivRange = Equiv.ofInjective f f.Injective :=
  by
  ext
  simp
#align function.embedding.to_equiv_range_eq_of_injective Function.Embedding.toEquivRange_eq_ofInjective

#print Equiv.Perm.viaFintypeEmbedding /-
/-- Extend the domain of `e : equiv.perm α`, mapping it through `f : α ↪ β`.
Everything outside of `set.range f` is kept fixed. Has poor computational performance,
due to exhaustive searching in constructed inverse due to using `function.embedding.to_equiv_range`.
When a better `α ≃ set.range f` is known, use `equiv.perm.via_set_range`.
When `[fintype α]` is not available, a noncomputable version is available as
`equiv.perm.via_embedding`.
-/
def Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β :=
  e.extendDomain f.toEquivRange
#align equiv.perm.via_fintype_embedding Equiv.Perm.viaFintypeEmbedding
-/

#print Equiv.Perm.viaFintypeEmbedding_apply_image /-
@[simp]
theorem Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) :
    e.viaFintypeEmbedding f (f a) = f (e a) :=
  by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert Equiv.Perm.extendDomain_apply_image e _ _
#align equiv.perm.via_fintype_embedding_apply_image Equiv.Perm.viaFintypeEmbedding_apply_image
-/

#print Equiv.Perm.viaFintypeEmbedding_apply_mem_range /-
theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b ∈ Set.range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simpa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_subtype, h]
#align equiv.perm.via_fintype_embedding_apply_mem_range Equiv.Perm.viaFintypeEmbedding_apply_mem_range
-/

#print Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range /-
theorem Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]
#align equiv.perm.via_fintype_embedding_apply_not_mem_range Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range
-/

/- warning: equiv.perm.via_fintype_embedding_sign -> Equiv.Perm.viaFintypeEmbedding_sign is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Fintype.{u1} α] [_inst_2 : DecidableEq.{succ u2} β] (e : Equiv.Perm.{succ u1} α) (f : Function.Embedding.{succ u1, succ u2} α β) [_inst_3 : DecidableEq.{succ u1} α] [_inst_4 : Fintype.{u2} β], Eq.{1} (Units.{0} Int Int.monoid) (coeFn.{succ u2, succ u2} (MonoidHom.{u2, 0} (Equiv.Perm.{succ u2} β) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u2, 0} (Equiv.Perm.{succ u2} β) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u2} β) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u2, 0} (Equiv.Perm.{succ u2} β) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} β) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} β) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} β) (Equiv.Perm.permGroup.{u2} β)))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u2} β (fun (a : β) (b : β) => _inst_2 a b) _inst_4) (Equiv.Perm.viaFintypeEmbedding.{u1, u2} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) e f)) (coeFn.{succ u1, succ u1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (fun (_x : MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) => (Equiv.Perm.{succ u1} α) -> (Units.{0} Int Int.monoid)) (MonoidHom.hasCoeToFun.{u1, 0} (Equiv.Perm.{succ u1} α) (Units.{0} Int Int.monoid) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} α) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} α) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} α) (Equiv.Perm.permGroup.{u1} α)))) (Units.mulOneClass.{0} Int Int.monoid)) (Equiv.Perm.sign.{u1} α (fun (a : α) (b : α) => _inst_3 a b) _inst_1) e)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Fintype.{u2} α] [_inst_2 : DecidableEq.{succ u1} β] (e : Equiv.Perm.{succ u2} α) (f : Function.Embedding.{succ u2, succ u1} α β) [_inst_3 : DecidableEq.{succ u2} α] [_inst_4 : Fintype.{u1} β], Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Equiv.Perm.{succ u1} β) => Units.{0} Int Int.instMonoidInt) (Equiv.Perm.viaFintypeEmbedding.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) e f)) (FunLike.coe.{succ u1, succ u1, 1} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} β) (fun (_x : Equiv.Perm.{succ u1} β) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Equiv.Perm.{succ u1} β) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u1} (Equiv.Perm.{succ u1} β) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u1, u1, 0} (MonoidHom.{u1, 0} (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u1, 0} (Equiv.Perm.{succ u1} β) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u1} (Equiv.Perm.{succ u1} β) (DivInvMonoid.toMonoid.{u1} (Equiv.Perm.{succ u1} β) (Group.toDivInvMonoid.{u1} (Equiv.Perm.{succ u1} β) (Equiv.Perm.permGroup.{u1} β)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u1} β (fun (a : β) (b : β) => _inst_2 a b) _inst_4) (Equiv.Perm.viaFintypeEmbedding.{u2, u1} α β _inst_1 (fun (a : β) (b : β) => _inst_2 a b) e f)) (FunLike.coe.{succ u2, succ u2, 1} (MonoidHom.{u2, 0} (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u2} α) (fun (_x : Equiv.Perm.{succ u2} α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Equiv.Perm.{succ u2} α) => Units.{0} Int Int.instMonoidInt) _x) (MulHomClass.toFunLike.{u2, u2, 0} (MonoidHom.{u2, 0} (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} α) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α))))) (MulOneClass.toMul.{0} (Units.{0} Int Int.instMonoidInt) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (MonoidHomClass.toMulHomClass.{u2, u2, 0} (MonoidHom.{u2, 0} (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)) (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt) (MonoidHom.monoidHomClass.{u2, 0} (Equiv.Perm.{succ u2} α) (Units.{0} Int Int.instMonoidInt) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} α) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} α) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} α) (Equiv.Perm.permGroup.{u2} α)))) (Units.instMulOneClassUnits.{0} Int Int.instMonoidInt)))) (Equiv.Perm.sign.{u2} α (fun (a : α) (b : α) => _inst_3 a b) _inst_1) e)
Case conversion may be inaccurate. Consider using '#align equiv.perm.via_fintype_embedding_sign Equiv.Perm.viaFintypeEmbedding_signₓ'. -/
@[simp]
theorem Equiv.Perm.viaFintypeEmbedding_sign [DecidableEq α] [Fintype β] :
    Equiv.Perm.sign (e.viaFintypeEmbedding f) = Equiv.Perm.sign e := by
  simp [Equiv.Perm.viaFintypeEmbedding]
#align equiv.perm.via_fintype_embedding_sign Equiv.Perm.viaFintypeEmbedding_sign

namespace Equiv

variable {p q : α → Prop} [DecidablePred p] [DecidablePred q]

#print Equiv.toCompl /-
/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.to_compl`
is an equivalence between the complement of those subtypes.

See also `equiv.compl`, for a computable version when a term of type
`{e' : α ≃ α // ∀ x : {x // p x}, e' x = e x}` is known. -/
noncomputable def toCompl (e : { x // p x } ≃ { x // q x }) : { x // ¬p x } ≃ { x // ¬q x } :=
  Classical.choice
    (Fintype.card_eq.mp (Fintype.card_compl_eq_card_compl _ _ (Fintype.card_congr e)))
#align equiv.to_compl Equiv.toCompl
-/

#print Equiv.extendSubtype /-
/-- If `e` is an equivalence between two subtypes of a fintype `α`, `e.extend_subtype`
is a permutation of `α` acting like `e` on the subtypes and doing something arbitrary outside.

Note that when `p = q`, `equiv.perm.subtype_congr e (equiv.refl _)` can be used instead. -/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl
#align equiv.extend_subtype Equiv.extendSubtype
-/

#print Equiv.extendSubtype_apply_of_mem /-
theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ :=
  by
  dsimp only [extend_subtype]
  simp only [subtype_congr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sum_compl_apply_symm_of_pos _ _ hx, Sum.map_inl, sum_compl_apply_inl]
#align equiv.extend_subtype_apply_of_mem Equiv.extendSubtype_apply_of_mem
-/

#print Equiv.extendSubtype_mem /-
theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) := by
  convert(e ⟨x, hx⟩).2
  rw [e.extend_subtype_apply_of_mem _ hx, Subtype.val_eq_coe]
#align equiv.extend_subtype_mem Equiv.extendSubtype_mem
-/

#print Equiv.extendSubtype_apply_of_not_mem /-
theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ :=
  by
  dsimp only [extend_subtype]
  simp only [subtype_congr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sum_compl_apply_symm_of_neg _ _ hx, Sum.map_inr, sum_compl_apply_inr]
#align equiv.extend_subtype_apply_of_not_mem Equiv.extendSubtype_apply_of_not_mem
-/

#print Equiv.extendSubtype_not_mem /-
theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) := by
  convert(e.to_compl ⟨x, hx⟩).2
  rw [e.extend_subtype_apply_of_not_mem _ hx, Subtype.val_eq_coe]
#align equiv.extend_subtype_not_mem Equiv.extendSubtype_not_mem
-/

end Equiv

