/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Order.RelIso.Basic
import Mathbin.Logic.Embedding.Set

#align_import order.rel_iso.set from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

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

#print RelHomClass.map_inf /-
theorem map_inf [SemilatticeInf α] [LinearOrder β]
    [RelHomClass F ((· < ·) : β → β → Prop) ((· < ·) : α → α → Prop)] (a : F) (m n : β) :
    a (m ⊓ n) = a m ⊓ a n :=
  (StrictMono.monotone fun x y => map_rel a).map_inf m n
#align rel_hom_class.map_inf RelHomClass.map_inf
-/

#print RelHomClass.map_sup /-
theorem map_sup [SemilatticeSup α] [LinearOrder β]
    [RelHomClass F ((· > ·) : β → β → Prop) ((· > ·) : α → α → Prop)] (a : F) (m n : β) :
    a (m ⊔ n) = a m ⊔ a n :=
  @map_inf αᵒᵈ βᵒᵈ _ _ _ _ _ _ _
#align rel_hom_class.map_sup RelHomClass.map_sup
-/

end RelHomClass

namespace RelIso

#print RelIso.range_eq /-
@[simp]
theorem range_eq (e : r ≃r s) : Set.range e = Set.univ :=
  e.Surjective.range_eq
#align rel_iso.range_eq RelIso.range_eq
-/

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

#print Subrel.relEmbedding_apply /-
@[simp]
theorem relEmbedding_apply (r : α → α → Prop) (p a) : Subrel.relEmbedding r p a = a.1 :=
  rfl
#align subrel.rel_embedding_apply Subrel.relEmbedding_apply
-/

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

#print RelEmbedding.codRestrict /-
/-- Restrict the codomain of a relation embedding. -/
def RelEmbedding.codRestrict (p : Set β) (f : r ↪r s) (H : ∀ a, f a ∈ p) : r ↪r Subrel s p :=
  ⟨f.toEmbedding.codRestrict p H, fun _ _ => f.map_rel_iff'⟩
#align rel_embedding.cod_restrict RelEmbedding.codRestrict
-/

#print RelEmbedding.codRestrict_apply /-
@[simp]
theorem RelEmbedding.codRestrict_apply (p) (f : r ↪r s) (H a) :
    RelEmbedding.codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl
#align rel_embedding.cod_restrict_apply RelEmbedding.codRestrict_apply
-/

