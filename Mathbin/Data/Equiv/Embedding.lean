import Mathbin.Logic.Embedding

/-!
# Equivalences on embeddings

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/


open Function.Embedding

namespace Equiv

-- error in Data.Equiv.Embedding: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Embeddings from a sum type are equivalent to two separate embeddings with disjoint ranges. -/
def sum_embedding_equiv_prod_embedding_disjoint
{α
 β
 γ : Type*} : «expr ≃ »(«expr ↪ »(«expr ⊕ »(α, β), γ), {f : «expr × »(«expr ↪ »(α, γ), «expr ↪ »(β, γ)) // disjoint (set.range f.1) (set.range f.2)}) :=
{ to_fun := λ
  f, ⟨(inl.trans f, inr.trans f), begin
     rintros ["_", "⟨", "⟨", ident a, ",", ident h, "⟩", ",", "⟨", ident b, ",", ident rfl, "⟩", "⟩"],
     simp [] [] ["only"] ["[", expr trans_apply, ",", expr inl_apply, ",", expr inr_apply, "]"] [] ["at", ident h],
     have [] [":", expr «expr = »(sum.inl a, sum.inr b)] [":=", expr f.injective h],
     simp [] [] ["only"] [] [] ["at", ident this],
     assumption
   end⟩,
  inv_fun := λ ⟨⟨f, g⟩, disj⟩, ⟨λ x, match x with
   | sum.inl a := f a
   | sum.inr b := g b
   end, begin
     rintros ["(", ident a₁, "|", ident b₁, ")", "(", ident a₂, "|", ident b₂, ")", ident f_eq]; simp [] [] ["only"] ["[", expr equiv.coe_fn_symm_mk, ",", expr sum.elim_inl, ",", expr sum.elim_inr, "]"] [] ["at", ident f_eq],
     { rw [expr f.injective f_eq] [] },
     { simp ["!"] [] ["only"] [] [] ["at", ident f_eq],
       exfalso,
       exact [expr disj ⟨⟨a₁, by simp [] [] [] [] [] []⟩, ⟨b₂, by simp [] [] [] ["[", expr f_eq, "]"] [] []⟩⟩] },
     { simp ["!"] [] ["only"] [] [] ["at", ident f_eq],
       exfalso,
       exact [expr disj ⟨⟨a₂, by simp [] [] [] [] [] []⟩, ⟨b₁, by simp [] [] [] ["[", expr f_eq, "]"] [] []⟩⟩] },
     { rw [expr g.injective f_eq] [] }
   end⟩,
  left_inv := λ f, by { dsimp ["only"] [] [] [],
    ext [] [] [],
    cases [expr x] []; simp ["!"] [] [] [] [] [] },
  right_inv := λ ⟨⟨f, g⟩, _⟩, by { simp [] [] ["only"] ["[", expr prod.mk.inj_iff, "]"] [] [],
    split; ext [] [] []; simp ["!"] [] [] [] [] [] } }

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

