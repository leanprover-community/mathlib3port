/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez

! This file was ported from Lean 3 source module logic.equiv.embedding
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Logic.Embedding.Set

/-!
# Equivalences on embeddings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/


open Function.Embedding

namespace Equiv

#print Equiv.sumEmbeddingEquivProdEmbeddingDisjoint /-
/-- Embeddings from a sum type are equivalent to two separate embeddings with disjoint ranges. -/
def sumEmbeddingEquivProdEmbeddingDisjoint {α β γ : Type _} :
    (Sum α β ↪ γ) ≃ { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) }
    where
  toFun f :=
    ⟨(inl.trans f, inr.trans f), by
      rw [Set.disjoint_left]
      rintro _ ⟨a, h⟩ ⟨b, rfl⟩
      simp only [trans_apply, inl_apply, inr_apply] at h
      have : Sum.inl a = Sum.inr b := f.injective h
      simp only at this
      assumption⟩
  invFun := fun ⟨⟨f, g⟩, disj⟩ =>
    ⟨fun x =>
      match x with
      | Sum.inl a => f a
      | Sum.inr b => g b,
      by
      rintro (a₁ | b₁) (a₂ | b₂) f_eq <;>
        simp only [Equiv.coeFn_symm_mk, Sum.elim_inl, Sum.elim_inr] at f_eq
      · rw [f.injective f_eq]
      · simp! only at f_eq
        exfalso
        exact disj.le_bot ⟨⟨a₁, by simp⟩, ⟨b₂, by simp [f_eq]⟩⟩
      · simp! only at f_eq
        exfalso
        exact disj.le_bot ⟨⟨a₂, by simp⟩, ⟨b₁, by simp [f_eq]⟩⟩
      · rw [g.injective f_eq]⟩
  left_inv f := by
    dsimp only
    ext
    cases x <;> simp!
  right_inv := fun ⟨⟨f, g⟩, _⟩ => by
    simp only [Prod.mk.inj_iff]
    constructor <;> ext <;> simp!
#align equiv.sum_embedding_equiv_prod_embedding_disjoint Equiv.sumEmbeddingEquivProdEmbeddingDisjoint
-/

#print Equiv.codRestrict /-
/-- Embeddings whose range lies within a set are equivalent to embeddings to that set.
This is `function.embedding.cod_restrict` as an equiv. -/
def codRestrict (α : Type _) {β : Type _} (bs : Set β) : { f : α ↪ β // ∀ a, f a ∈ bs } ≃ (α ↪ bs)
    where
  toFun f := (f : α ↪ β).codRestrict bs f.Prop
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).Prop⟩
  left_inv x := by ext <;> rfl
  right_inv x := by ext <;> rfl
#align equiv.cod_restrict Equiv.codRestrict
-/

#print Equiv.prodEmbeddingDisjointEquivSigmaEmbeddingRestricted /-
/-- Pairs of embeddings with disjoint ranges are equivalent to a dependent sum of embeddings,
in which the second embedding cannot take values in the range of the first. -/
def prodEmbeddingDisjointEquivSigmaEmbeddingRestricted {α β γ : Type _} :
    { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) } ≃
      Σf : α ↪ γ, β ↪ ↥(Set.range fᶜ) :=
  (subtype_prod_equiv_sigma_subtype fun (a : α ↪ γ) (b : β ↪ _) =>
        Disjoint (Set.range a) (Set.range b)).trans <|
    Equiv.sigmaCongrRight fun a =>
      (subtype_equiv_prop <| by
            ext f
            rw [← Set.range_subset_iff, Set.subset_compl_iff_disjoint_right, disjoint_comm]).trans
        (codRestrict _ _)
#align equiv.prod_embedding_disjoint_equiv_sigma_embedding_restricted Equiv.prodEmbeddingDisjointEquivSigmaEmbeddingRestricted
-/

/- warning: equiv.sum_embedding_equiv_sigma_embedding_restricted -> Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}}, Equiv.{max 1 (max (succ u1) (succ u2)) (succ u3), max (succ (max u1 u3)) (succ (max u2 u3))} (Function.Embedding.{max (succ u1) (succ u2), succ u3} (Sum.{u1, u2} α β) γ) (Sigma.{max u1 u3, max u2 u3} (Function.Embedding.{succ u1, succ u3} α γ) (fun (f : Function.Embedding.{succ u1, succ u3} α γ) => Function.Embedding.{succ u2, succ u3} β (coeSort.{succ u3, succ (succ u3)} (Set.{u3} γ) Type.{u3} (Set.hasCoeToSort.{u3} γ) (HasCompl.compl.{u3} (Set.{u3} γ) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} γ) (Set.booleanAlgebra.{u3} γ)) (Set.range.{u3, succ u1} γ α (coeFn.{max 1 (succ u1) (succ u3), max (succ u1) (succ u3)} (Function.Embedding.{succ u1, succ u3} α γ) (fun (_x : Function.Embedding.{succ u1, succ u3} α γ) => α -> γ) (Function.Embedding.hasCoeToFun.{succ u1, succ u3} α γ) f))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}}, Equiv.{max (succ u3) (succ u2) (succ u1), max (succ (max u2 u3)) (succ (max u1 u3))} (Function.Embedding.{max (succ u2) (succ u1), succ u3} (Sum.{u1, u2} α β) γ) (Sigma.{max u1 u3, max u2 u3} (Function.Embedding.{succ u1, succ u3} α γ) (fun (f : Function.Embedding.{succ u1, succ u3} α γ) => Function.Embedding.{succ u2, succ u3} β (Set.Elem.{u3} γ (HasCompl.compl.{u3} (Set.{u3} γ) (BooleanAlgebra.toHasCompl.{u3} (Set.{u3} γ) (Set.instBooleanAlgebraSet.{u3} γ)) (Set.range.{u3, succ u1} γ α (FunLike.coe.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α γ) α (fun (_x : α) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : α) => γ) _x) (EmbeddingLike.toFunLike.{max (succ u1) (succ u3), succ u1, succ u3} (Function.Embedding.{succ u1, succ u3} α γ) α γ (Function.instEmbeddingLikeEmbedding.{succ u1, succ u3} α γ)) f))))))
Case conversion may be inaccurate. Consider using '#align equiv.sum_embedding_equiv_sigma_embedding_restricted Equiv.sumEmbeddingEquivSigmaEmbeddingRestrictedₓ'. -/
/-- A combination of the above results, allowing us to turn one embedding over a sum type
into two dependent embeddings, the second of which avoids any members of the range
of the first. This is helpful for constructing larger embeddings out of smaller ones. -/
def sumEmbeddingEquivSigmaEmbeddingRestricted {α β γ : Type _} :
    (Sum α β ↪ γ) ≃ Σf : α ↪ γ, β ↪ ↥(Set.range fᶜ) :=
  Equiv.trans sumEmbeddingEquivProdEmbeddingDisjoint
    prodEmbeddingDisjointEquivSigmaEmbeddingRestricted
#align equiv.sum_embedding_equiv_sigma_embedding_restricted Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

#print Equiv.uniqueEmbeddingEquivResult /-
/-- Embeddings from a single-member type are equivalent to members of the target type. -/
def uniqueEmbeddingEquivResult {α β : Type _} [Unique α] : (α ↪ β) ≃ β
    where
  toFun f := f default
  invFun x := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  left_inv _ := by
    ext
    simp_rw [Function.Embedding.coeFn_mk]
    congr
  right_inv _ := by simp
#align equiv.unique_embedding_equiv_result Equiv.uniqueEmbeddingEquivResult
-/

end Equiv

