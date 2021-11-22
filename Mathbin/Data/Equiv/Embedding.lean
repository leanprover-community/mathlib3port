import Mathbin.Logic.Embedding 
import Mathbin.Data.Set.Lattice

/-!
# Equivalences on embeddings

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/


open Function.Embedding

namespace Equiv

/-- Embeddings from a sum type are equivalent to two separate embeddings with disjoint ranges. -/
def sum_embedding_equiv_prod_embedding_disjoint {α β γ : Type _} :
  (Sum α β ↪ γ) ≃ { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.Range f.1) (Set.Range f.2) } :=
  { toFun :=
      fun f =>
        ⟨(inl.trans f, inr.trans f),
          by 
            rintro _ ⟨⟨a, h⟩, ⟨b, rfl⟩⟩
            simp only [trans_apply, inl_apply, inr_apply] at h 
            have  : Sum.inl a = Sum.inr b := f.injective h 
            simp only  at this 
            assumption⟩,
    invFun :=
      fun ⟨⟨f, g⟩, disj⟩ =>
        ⟨fun x =>
            match x with 
            | Sum.inl a => f a
            | Sum.inr b => g b,
          by 
            rintro (a₁ | b₁) (a₂ | b₂) f_eq <;> simp only [Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr] at f_eq
            ·
              rw [f.injective f_eq]
            ·
              simp only  at f_eq 
              exFalso 
              exact
                disj
                  ⟨⟨a₁,
                      by 
                        simp ⟩,
                    ⟨b₂,
                      by 
                        simp [f_eq]⟩⟩
            ·
              simp only  at f_eq 
              exFalso 
              exact
                disj
                  ⟨⟨a₂,
                      by 
                        simp ⟩,
                    ⟨b₁,
                      by 
                        simp [f_eq]⟩⟩
            ·
              rw [g.injective f_eq]⟩,
    left_inv :=
      fun f =>
        by 
          dsimp only 
          ext 
          cases x <;> simp ,
    right_inv :=
      fun ⟨⟨f, g⟩, _⟩ =>
        by 
          simp only [Prod.mk.inj_iffₓ]
          split  <;> ext <;> simp  }

/-- Embeddings whose range lies within a set are equivalent to embeddings to that set.
This is `function.embedding.cod_restrict` as an equiv. -/
def cod_restrict (α : Type _) {β : Type _} (bs : Set β) : { f : α ↪ β // ∀ a, f a ∈ bs } ≃ (α ↪ bs) :=
  { toFun := fun f => (f : α ↪ β).codRestrict bs f.prop,
    invFun := fun f => ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).Prop⟩,
    left_inv :=
      fun x =>
        by 
          ext <;> rfl,
    right_inv :=
      fun x =>
        by 
          ext <;> rfl }

/-- Pairs of embeddings with disjoint ranges are equivalent to a dependent sum of embeddings,
in which the second embedding cannot take values in the range of the first. -/
def prod_embedding_disjoint_equiv_sigma_embedding_restricted {α β γ : Type _} :
  { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.Range f.1) (Set.Range f.2) } ≃
    Σf : α ↪ γ, β ↪ «expr↥ » («expr ᶜ» (Set.Range f)) :=
  (subtype_prod_equiv_sigma_subtype$ fun a : α ↪ γ b : β ↪ _ => Disjoint (Set.Range a) (Set.Range b)).trans$
    Equiv.sigmaCongrRight$
      fun a =>
        (subtype_equiv_prop
              (by 
                ext f 
                rw [←Set.range_subset_iff, Set.subset_compl_iff_disjoint]
                exact disjoint.comm.trans disjoint_iff)).trans
          (cod_restrict _ _)

/-- A combination of the above results, allowing us to turn one embedding over a sum type
into two dependent embeddings, the second of which avoids any members of the range
of the first. This is helpful for constructing larger embeddings out of smaller ones. -/
def sum_embedding_equiv_sigma_embedding_restricted {α β γ : Type _} :
  (Sum α β ↪ γ) ≃ Σf : α ↪ γ, β ↪ «expr↥ » («expr ᶜ» (Set.Range f)) :=
  Equiv.trans sum_embedding_equiv_prod_embedding_disjoint prod_embedding_disjoint_equiv_sigma_embedding_restricted

/-- Embeddings from a single-member type are equivalent to members of the target type. -/
def unique_embedding_equiv_result {α β : Type _} [Unique α] : (α ↪ β) ≃ β :=
  { toFun := fun f => f (default α), invFun := fun x => ⟨fun _ => x, fun _ _ _ => Subsingleton.elimₓ _ _⟩,
    left_inv :=
      fun _ =>
        by 
          ext 
          simpRw [Function.Embedding.coe_fn_mk]
          congr,
    right_inv :=
      fun _ =>
        by 
          simp  }

end Equiv

