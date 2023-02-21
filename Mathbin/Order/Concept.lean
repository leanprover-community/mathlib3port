/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.concept
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Lattice

/-!
# Formal concept analysis

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : set α` and `t : set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## TODO

Prove the fundamental theorem of concept lattices.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]

## Tags

concept, formal concept analysis, intent, extend, attribute
-/


open Function OrderDual Set

variable {ι : Sort _} {α β γ : Type _} {κ : ι → Sort _} (r : α → β → Prop) {s s₁ s₂ : Set α}
  {t t₁ t₂ : Set β}

/-! ### Intent and extent -/


#print intentClosure /-
/-- The intent closure of `s : set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def intentClosure (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }
#align intent_closure intentClosure
-/

#print extentClosure /-
/-- The extent closure of `t : set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def extentClosure (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }
#align extent_closure extentClosure
-/

variable {r}

#print subset_intentClosure_iff_subset_extentClosure /-
theorem subset_intentClosure_iff_subset_extentClosure :
    t ⊆ intentClosure r s ↔ s ⊆ extentClosure r t :=
  ⟨fun h a ha b hb => h hb ha, fun h b hb a ha => h ha hb⟩
#align subset_intent_closure_iff_subset_extent_closure subset_intentClosure_iff_subset_extentClosure
-/

variable (r)

/- warning: gc_intent_closure_extent_closure -> gc_intentClosure_extentClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop), GaloisConnection.{u1, u2} (Set.{u1} α) (OrderDual.{u2} (Set.{u2} β)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (OrderDual.preorder.{u2} (Set.{u2} β) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β)))))))) (Function.comp.{succ u1, succ u2, succ u2} (Set.{u1} α) (Set.{u2} β) (OrderDual.{u2} (Set.{u2} β)) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (Set.{u2} β) (OrderDual.{u2} (Set.{u2} β))) (fun (_x : Equiv.{succ u2, succ u2} (Set.{u2} β) (OrderDual.{u2} (Set.{u2} β))) => (Set.{u2} β) -> (OrderDual.{u2} (Set.{u2} β))) (Equiv.hasCoeToFun.{succ u2, succ u2} (Set.{u2} β) (OrderDual.{u2} (Set.{u2} β))) (OrderDual.toDual.{u2} (Set.{u2} β))) (intentClosure.{u1, u2} α β r)) (Function.comp.{succ u2, succ u2, succ u1} (OrderDual.{u2} (Set.{u2} β)) (Set.{u2} β) (Set.{u1} α) (extentClosure.{u1, u2} α β r) (coeFn.{succ u2, succ u2} (Equiv.{succ u2, succ u2} (OrderDual.{u2} (Set.{u2} β)) (Set.{u2} β)) (fun (_x : Equiv.{succ u2, succ u2} (OrderDual.{u2} (Set.{u2} β)) (Set.{u2} β)) => (OrderDual.{u2} (Set.{u2} β)) -> (Set.{u2} β)) (Equiv.hasCoeToFun.{succ u2, succ u2} (OrderDual.{u2} (Set.{u2} β)) (Set.{u2} β)) (OrderDual.ofDual.{u2} (Set.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop), GaloisConnection.{u2, u1} (Set.{u2} α) (OrderDual.{u1} (Set.{u1} β)) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (OrderDual.preorder.{u1} (Set.{u1} β) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β)))))))) (Function.comp.{succ u2, succ u1, succ u1} (Set.{u2} α) (Set.{u1} β) (OrderDual.{u1} (Set.{u1} β)) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (Set.{u1} β) (OrderDual.{u1} (Set.{u1} β))) (Set.{u1} β) (fun (_x : Set.{u1} β) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : Set.{u1} β) => OrderDual.{u1} (Set.{u1} β)) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (Set.{u1} β) (OrderDual.{u1} (Set.{u1} β))) (OrderDual.toDual.{u1} (Set.{u1} β))) (intentClosure.{u2, u1} α β r)) (Function.comp.{succ u1, succ u1, succ u2} (OrderDual.{u1} (Set.{u1} β)) (Set.{u1} β) (Set.{u2} α) (extentClosure.{u2, u1} α β r) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} β)) (Set.{u1} β)) (OrderDual.{u1} (Set.{u1} β)) (fun (_x : OrderDual.{u1} (Set.{u1} β)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : OrderDual.{u1} (Set.{u1} β)) => Set.{u1} β) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (OrderDual.{u1} (Set.{u1} β)) (Set.{u1} β)) (OrderDual.ofDual.{u1} (Set.{u1} β))))
Case conversion may be inaccurate. Consider using '#align gc_intent_closure_extent_closure gc_intentClosure_extentClosureₓ'. -/
theorem gc_intentClosure_extentClosure :
    GaloisConnection (toDual ∘ intentClosure r) (extentClosure r ∘ ofDual) := fun s t =>
  subset_intentClosure_iff_subset_extentClosure
#align gc_intent_closure_extent_closure gc_intentClosure_extentClosure

#print intentClosure_swap /-
theorem intentClosure_swap (t : Set β) : intentClosure (swap r) t = extentClosure r t :=
  rfl
#align intent_closure_swap intentClosure_swap
-/

/- warning: extent_closure_swap -> extentClosure_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (extentClosure.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) s) (intentClosure.{u1, u2} α β r s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (extentClosure.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) s) (intentClosure.{u2, u1} α β r s)
Case conversion may be inaccurate. Consider using '#align extent_closure_swap extentClosure_swapₓ'. -/
theorem extentClosure_swap (s : Set α) : extentClosure (swap r) s = intentClosure r s :=
  rfl
#align extent_closure_swap extentClosure_swap

#print intentClosure_empty /-
@[simp]
theorem intentClosure_empty : intentClosure r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim
#align intent_closure_empty intentClosure_empty
-/

/- warning: extent_closure_empty -> extentClosure_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop), Eq.{succ u1} (Set.{u1} α) (extentClosure.{u1, u2} α β r (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop), Eq.{succ u2} (Set.{u2} α) (extentClosure.{u2, u1} α β r (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align extent_closure_empty extentClosure_emptyₓ'. -/
@[simp]
theorem extentClosure_empty : extentClosure r ∅ = univ :=
  intentClosure_empty _
#align extent_closure_empty extentClosure_empty

/- warning: intent_closure_union -> intentClosure_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (intentClosure.{u1, u2} α β r (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (intentClosure.{u1, u2} α β r s₁) (intentClosure.{u1, u2} α β r s₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s₁ : Set.{u2} α) (s₂ : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (intentClosure.{u2, u1} α β r (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) s₁ s₂)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (intentClosure.{u2, u1} α β r s₁) (intentClosure.{u2, u1} α β r s₂))
Case conversion may be inaccurate. Consider using '#align intent_closure_union intentClosure_unionₓ'. -/
@[simp]
theorem intentClosure_union (s₁ s₂ : Set α) :
    intentClosure r (s₁ ∪ s₂) = intentClosure r s₁ ∩ intentClosure r s₂ :=
  Set.ext fun _ => ball_or_left
#align intent_closure_union intentClosure_union

/- warning: extent_closure_union -> extentClosure_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (t₁ : Set.{u2} β) (t₂ : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (extentClosure.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (extentClosure.{u1, u2} α β r t₁) (extentClosure.{u1, u2} α β r t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (t₁ : Set.{u2} β) (t₂ : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (extentClosure.{u1, u2} α β r (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (extentClosure.{u1, u2} α β r t₁) (extentClosure.{u1, u2} α β r t₂))
Case conversion may be inaccurate. Consider using '#align extent_closure_union extentClosure_unionₓ'. -/
@[simp]
theorem extentClosure_union (t₁ t₂ : Set β) :
    extentClosure r (t₁ ∪ t₂) = extentClosure r t₁ ∩ extentClosure r t₂ :=
  intentClosure_union _ _ _
#align extent_closure_union extentClosure_union

/- warning: intent_closure_Union -> intentClosure_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {β : Type.{u3}} (r : α -> β -> Prop) (f : ι -> (Set.{u2} α)), Eq.{succ u3} (Set.{u3} β) (intentClosure.{u2, u3} α β r (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => f i))) (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => intentClosure.{u2, u3} α β r (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} {α : Type.{u3}} {β : Type.{u2}} (r : α -> β -> Prop) (f : ι -> (Set.{u3} α)), Eq.{succ u2} (Set.{u2} β) (intentClosure.{u3, u2} α β r (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => f i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => intentClosure.{u3, u2} α β r (f i)))
Case conversion may be inaccurate. Consider using '#align intent_closure_Union intentClosure_unionᵢₓ'. -/
@[simp]
theorem intentClosure_unionᵢ (f : ι → Set α) :
    intentClosure r (⋃ i, f i) = ⋂ i, intentClosure r (f i) :=
  (gc_intentClosure_extentClosure r).l_supᵢ
#align intent_closure_Union intentClosure_unionᵢ

#print extentClosure_unionᵢ /-
@[simp]
theorem extentClosure_unionᵢ (f : ι → Set β) :
    extentClosure r (⋃ i, f i) = ⋂ i, extentClosure r (f i) :=
  intentClosure_unionᵢ _ _
#align extent_closure_Union extentClosure_unionᵢ
-/

/- warning: intent_closure_Union₂ -> intentClosure_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {β : Type.{u3}} {κ : ι -> Sort.{u4}} (r : α -> β -> Prop) (f : forall (i : ι), (κ i) -> (Set.{u2} α)), Eq.{succ u3} (Set.{u3} β) (intentClosure.{u2, u3} α β r (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => Set.unionᵢ.{u2, u4} α (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => Set.interᵢ.{u3, u4} β (κ i) (fun (j : κ i) => intentClosure.{u2, u3} α β r (f i j))))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u4}} {β : Type.{u3}} {κ : ι -> Sort.{u1}} (r : α -> β -> Prop) (f : forall (i : ι), (κ i) -> (Set.{u4} α)), Eq.{succ u3} (Set.{u3} β) (intentClosure.{u4, u3} α β r (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => intentClosure.{u4, u3} α β r (f i j))))
Case conversion may be inaccurate. Consider using '#align intent_closure_Union₂ intentClosure_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem intentClosure_unionᵢ₂ (f : ∀ i, κ i → Set α) :
    intentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), intentClosure r (f i j) :=
  (gc_intentClosure_extentClosure r).l_supᵢ₂
#align intent_closure_Union₂ intentClosure_unionᵢ₂

/- warning: extent_closure_Union₂ -> extentClosure_Union₂ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {α : Type.{u2}} {β : Type.{u3}} {κ : ι -> Sort.{u4}} (r : α -> β -> Prop) (f : forall (i : ι), (κ i) -> (Set.{u3} β)), Eq.{succ u2} (Set.{u2} α) (extentClosure.{u2, u3} α β r (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => Set.unionᵢ.{u3, u4} β (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => Set.interᵢ.{u2, u4} α (κ i) (fun (j : κ i) => extentClosure.{u2, u3} α β r (f i j))))
but is expected to have type
  forall {ι : Sort.{u2}} {α : Type.{u3}} {β : Type.{u4}} {κ : ι -> Sort.{u1}} (r : α -> β -> Prop) (f : forall (i : ι), (κ i) -> (Set.{u4} β)), Eq.{succ u3} (Set.{u3} α) (extentClosure.{u3, u4} α β r (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => f i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => extentClosure.{u3, u4} α β r (f i j))))
Case conversion may be inaccurate. Consider using '#align extent_closure_Union₂ extentClosure_Union₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem extentClosure_Union₂ (f : ∀ i, κ i → Set β) :
    extentClosure r (⋃ (i) (j), f i j) = ⋂ (i) (j), extentClosure r (f i j) :=
  intentClosure_unionᵢ₂ _ _
#align extent_closure_Union₂ extentClosure_Union₂

/- warning: subset_extent_closure_intent_closure -> subset_extentClosure_intentClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (extentClosure.{u1, u2} α β r (intentClosure.{u1, u2} α β r s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s : Set.{u2} α), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (extentClosure.{u2, u1} α β r (intentClosure.{u2, u1} α β r s))
Case conversion may be inaccurate. Consider using '#align subset_extent_closure_intent_closure subset_extentClosure_intentClosureₓ'. -/
theorem subset_extentClosure_intentClosure (s : Set α) : s ⊆ extentClosure r (intentClosure r s) :=
  (gc_intentClosure_extentClosure r).le_u_l _
#align subset_extent_closure_intent_closure subset_extentClosure_intentClosure

#print subset_intentClosure_extentClosure /-
theorem subset_intentClosure_extentClosure (t : Set β) : t ⊆ intentClosure r (extentClosure r t) :=
  subset_extentClosure_intentClosure _ t
#align subset_intent_closure_extent_closure subset_intentClosure_extentClosure
-/

/- warning: intent_closure_extent_closure_intent_closure -> intentClosure_extentClosure_intentClosure is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop) (s : Set.{u1} α), Eq.{succ u2} (Set.{u2} β) (intentClosure.{u1, u2} α β r (extentClosure.{u1, u2} α β r (intentClosure.{u1, u2} α β r s))) (intentClosure.{u1, u2} α β r s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop) (s : Set.{u2} α), Eq.{succ u1} (Set.{u1} β) (intentClosure.{u2, u1} α β r (extentClosure.{u2, u1} α β r (intentClosure.{u2, u1} α β r s))) (intentClosure.{u2, u1} α β r s)
Case conversion may be inaccurate. Consider using '#align intent_closure_extent_closure_intent_closure intentClosure_extentClosure_intentClosureₓ'. -/
@[simp]
theorem intentClosure_extentClosure_intentClosure (s : Set α) :
    intentClosure r (extentClosure r <| intentClosure r s) = intentClosure r s :=
  (gc_intentClosure_extentClosure r).l_u_l_eq_l _
#align intent_closure_extent_closure_intent_closure intentClosure_extentClosure_intentClosure

#print extentClosure_intentClosure_extentClosure /-
@[simp]
theorem extentClosure_intentClosure_extentClosure (t : Set β) :
    extentClosure r (intentClosure r <| extentClosure r t) = extentClosure r t :=
  intentClosure_extentClosure_intentClosure _ t
#align extent_closure_intent_closure_extent_closure extentClosure_intentClosure_extentClosure
-/

/- warning: intent_closure_anti -> intentClosure_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop), Antitone.{u1, u2} (Set.{u1} α) (Set.{u2} β) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (intentClosure.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} (r : α -> β -> Prop), Antitone.{u2, u1} (Set.{u2} α) (Set.{u1} β) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (intentClosure.{u2, u1} α β r)
Case conversion may be inaccurate. Consider using '#align intent_closure_anti intentClosure_antiₓ'. -/
theorem intentClosure_anti : Antitone (intentClosure r) :=
  (gc_intentClosure_extentClosure r).monotone_l
#align intent_closure_anti intentClosure_anti

/- warning: extent_closure_anti -> extentClosure_anti is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop), Antitone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (extentClosure.{u1, u2} α β r)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} (r : α -> β -> Prop), Antitone.{u2, u1} (Set.{u2} β) (Set.{u1} α) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α))))))) (extentClosure.{u1, u2} α β r)
Case conversion may be inaccurate. Consider using '#align extent_closure_anti extentClosure_antiₓ'. -/
theorem extentClosure_anti : Antitone (extentClosure r) :=
  intentClosure_anti _
#align extent_closure_anti extentClosure_anti

/-! ### Concepts -/


variable (α β)

#print Concept /-
/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept extends Set α × Set β where
  closure_fst : intentClosure r fst = snd
  closure_snd : extentClosure r snd = fst
#align concept Concept
-/

namespace Concept

variable {r α β} {c d : Concept α β r}

attribute [simp] closure_fst closure_snd

/- warning: concept.ext -> Concept.ext is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, (Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) -> (Eq.{max (succ u1) (succ u2)} (Concept.{u1, u2} α β r) c d)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {c : Concept.{u2, u1} α β r} {d : Concept.{u2, u1} α β r}, (Eq.{succ u2} (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d))) -> (Eq.{max (succ u2) (succ u1)} (Concept.{u2, u1} α β r) c d)
Case conversion may be inaccurate. Consider using '#align concept.ext Concept.extₓ'. -/
@[ext]
theorem ext (h : c.fst = d.fst) : c = d :=
  by
  obtain ⟨⟨s₁, t₁⟩, h₁, _⟩ := c
  obtain ⟨⟨s₂, t₂⟩, h₂, _⟩ := d
  dsimp at h₁ h₂ h
  subst h
  subst h₁
  subst h₂
#align concept.ext Concept.ext

#print Concept.ext' /-
theorem ext' (h : c.snd = d.snd) : c = d :=
  by
  obtain ⟨⟨s₁, t₁⟩, _, h₁⟩ := c
  obtain ⟨⟨s₂, t₂⟩, _, h₂⟩ := d
  dsimp at h₁ h₂ h
  subst h
  subst h₁
  subst h₂
#align concept.ext' Concept.ext'
-/

/- warning: concept.fst_injective -> Concept.fst_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), succ u1} (Concept.{u1, u2} α β r) (Set.{u1} α) (fun (c : Concept.{u1, u2} α β r) => Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), succ u2} (Concept.{u2, u1} α β r) (Set.{u2} α) (fun (c : Concept.{u2, u1} α β r) => Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c))
Case conversion may be inaccurate. Consider using '#align concept.fst_injective Concept.fst_injectiveₓ'. -/
theorem fst_injective : Injective fun c : Concept α β r => c.fst := fun c d => ext
#align concept.fst_injective Concept.fst_injective

/- warning: concept.snd_injective -> Concept.snd_injective is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Function.Injective.{max (succ u1) (succ u2), succ u2} (Concept.{u1, u2} α β r) (Set.{u2} β) (fun (c : Concept.{u1, u2} α β r) => Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, Function.Injective.{max (succ u2) (succ u1), succ u1} (Concept.{u2, u1} α β r) (Set.{u1} β) (fun (c : Concept.{u2, u1} α β r) => Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c))
Case conversion may be inaccurate. Consider using '#align concept.snd_injective Concept.snd_injectiveₓ'. -/
theorem snd_injective : Injective fun c : Concept α β r => c.snd := fun c d => ext'
#align concept.snd_injective Concept.snd_injective

instance : HasSup (Concept α β r) :=
  ⟨fun c d =>
    { fst := extentClosure r (c.snd ∩ d.snd)
      snd := c.snd ∩ d.snd
      closure_fst := by
        rw [← c.closure_fst, ← d.closure_fst, ← intentClosure_union,
          intentClosure_extentClosure_intentClosure]
      closure_snd := rfl }⟩

instance : HasInf (Concept α β r) :=
  ⟨fun c d =>
    { fst := c.fst ∩ d.fst
      snd := intentClosure r (c.fst ∩ d.fst)
      closure_fst := rfl
      closure_snd := by
        rw [← c.closure_snd, ← d.closure_snd, ← extentClosure_union,
          extentClosure_intentClosure_extentClosure] }⟩

instance : SemilatticeInf (Concept α β r) :=
  fst_injective.SemilatticeInf _ fun _ _ => rfl

/- warning: concept.fst_subset_fst_iff -> Concept.fst_subset_fst_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LE.le.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r)))) c d)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {c : Concept.{u2, u1} α β r} {d : Concept.{u2, u1} α β r}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d))) (LE.le.{max u2 u1} (Concept.{u2, u1} α β r) (Preorder.toLE.{max u2 u1} (Concept.{u2, u1} α β r) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (SemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instSemilatticeInfConcept.{u2, u1} α β r)))) c d)
Case conversion may be inaccurate. Consider using '#align concept.fst_subset_fst_iff Concept.fst_subset_fst_iffₓ'. -/
@[simp]
theorem fst_subset_fst_iff : c.fst ⊆ d.fst ↔ c ≤ d :=
  Iff.rfl
#align concept.fst_subset_fst_iff Concept.fst_subset_fst_iff

/- warning: concept.fst_ssubset_fst_iff -> Concept.fst_ssubset_fst_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LT.lt.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLT.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r)))) c d)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {c : Concept.{u2, u1} α β r} {d : Concept.{u2, u1} α β r}, Iff (HasSSubset.SSubset.{u2} (Set.{u2} α) (Set.instHasSSubsetSet.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d))) (LT.lt.{max u2 u1} (Concept.{u2, u1} α β r) (Preorder.toLT.{max u2 u1} (Concept.{u2, u1} α β r) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (SemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instSemilatticeInfConcept.{u2, u1} α β r)))) c d)
Case conversion may be inaccurate. Consider using '#align concept.fst_ssubset_fst_iff Concept.fst_ssubset_fst_iffₓ'. -/
@[simp]
theorem fst_ssubset_fst_iff : c.fst ⊂ d.fst ↔ c < d :=
  Iff.rfl
#align concept.fst_ssubset_fst_iff Concept.fst_ssubset_fst_iff

/- warning: concept.snd_subset_snd_iff -> Concept.snd_subset_snd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LE.le.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r)))) d c)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LE.le.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instSemilatticeInfConcept.{u1, u2} α β r)))) d c)
Case conversion may be inaccurate. Consider using '#align concept.snd_subset_snd_iff Concept.snd_subset_snd_iffₓ'. -/
@[simp]
theorem snd_subset_snd_iff : c.snd ⊆ d.snd ↔ d ≤ c :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rw [← fst_subset_fst_iff, ← c.closure_snd, ← d.closure_snd]
    exact extentClosure_anti _ h
  · rw [← c.closure_fst, ← d.closure_fst]
    exact intentClosure_anti _ h
#align concept.snd_subset_snd_iff Concept.snd_subset_snd_iff

/- warning: concept.snd_ssubset_snd_iff -> Concept.snd_ssubset_snd_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSSubset.SSubset.{u2} (Set.{u2} β) (Set.hasSsubset.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LT.lt.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLT.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r)))) d c)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (HasSSubset.SSubset.{u2} (Set.{u2} β) (Set.instHasSSubsetSet.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))) (LT.lt.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLT.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instSemilatticeInfConcept.{u1, u2} α β r)))) d c)
Case conversion may be inaccurate. Consider using '#align concept.snd_ssubset_snd_iff Concept.snd_ssubset_snd_iffₓ'. -/
@[simp]
theorem snd_ssubset_snd_iff : c.snd ⊂ d.snd ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_le, snd_subset_snd_iff, snd_subset_snd_iff]
#align concept.snd_ssubset_snd_iff Concept.snd_ssubset_snd_iff

/- warning: concept.strict_mono_fst -> Concept.strictMono_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, StrictMono.{max u1 u2, u1} (Concept.{u1, u2} α β r) (Set.{u1} α) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r))) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α))))))) (Function.comp.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u1} (Concept.{u1, u2} α β r) (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Concept.toProd.{u1, u2} α β r))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, StrictMono.{max u2 u1, u2} (Concept.{u2, u1} α β r) (Set.{u2} α) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (SemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instSemilatticeInfConcept.{u2, u1} α β r))) (PartialOrder.toPreorder.{u2} (Set.{u2} α) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} α) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} α) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} α) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} α) (Set.instCompleteBooleanAlgebraSet.{u2} α))))))) (Function.comp.{max (succ u2) (succ u1), max (succ u1) (succ u2), succ u2} (Concept.{u2, u1} α β r) (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Concept.toProd.{u2, u1} α β r))
Case conversion may be inaccurate. Consider using '#align concept.strict_mono_fst Concept.strictMono_fstₓ'. -/
theorem strictMono_fst : StrictMono (Prod.fst ∘ toProd : Concept α β r → Set α) := fun c d =>
  fst_ssubset_fst_iff.2
#align concept.strict_mono_fst Concept.strictMono_fst

/- warning: concept.strict_anti_snd -> Concept.strictAnti_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, StrictAnti.{max u1 u2, u2} (Concept.{u1, u2} α β r) (Set.{u2} β) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (SemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.semilatticeInf.{u1, u2} α β r))) (PartialOrder.toPreorder.{u2} (Set.{u2} β) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (Function.comp.{max (succ u1) (succ u2), max (succ u1) (succ u2), succ u2} (Concept.{u1, u2} α β r) (Prod.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β)) (Concept.toProd.{u1, u2} α β r))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, StrictAnti.{max u2 u1, u1} (Concept.{u2, u1} α β r) (Set.{u1} β) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (SemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instSemilatticeInfConcept.{u2, u1} α β r))) (PartialOrder.toPreorder.{u1} (Set.{u1} β) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (Function.comp.{max (succ u2) (succ u1), max (succ u1) (succ u2), succ u1} (Concept.{u2, u1} α β r) (Prod.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Set.{u1} β) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β)) (Concept.toProd.{u2, u1} α β r))
Case conversion may be inaccurate. Consider using '#align concept.strict_anti_snd Concept.strictAnti_sndₓ'. -/
theorem strictAnti_snd : StrictAnti (Prod.snd ∘ toProd : Concept α β r → Set β) := fun c d =>
  snd_ssubset_snd_iff.2
#align concept.strict_anti_snd Concept.strictAnti_snd

instance : Lattice (Concept α β r) :=
  { Concept.semilatticeInf with
    sup := (· ⊔ ·)
    le_sup_left := fun c d => snd_subset_snd_iff.1 <| inter_subset_left _ _
    le_sup_right := fun c d => snd_subset_snd_iff.1 <| inter_subset_right _ _
    sup_le := fun c d e => by
      simp_rw [← snd_subset_snd_iff]
      exact subset_inter }

instance : BoundedOrder (Concept α β r)
    where
  top := ⟨⟨univ, intentClosure r univ⟩, rfl, eq_univ_of_forall fun a b hb => hb trivial⟩
  le_top _ := subset_univ _
  bot := ⟨⟨extentClosure r univ, univ⟩, eq_univ_of_forall fun b a ha => ha trivial, rfl⟩
  bot_le _ := snd_subset_snd_iff.1 <| subset_univ _

instance : SupSet (Concept α β r) :=
  ⟨fun S =>
    { fst := extentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd)
      snd := ⋂ c ∈ S, (c : Concept _ _ _).snd
      closure_fst := by
        simp_rw [← closure_fst, ← intentClosure_unionᵢ₂, intentClosure_extentClosure_intentClosure]
      closure_snd := rfl }⟩

instance : InfSet (Concept α β r) :=
  ⟨fun S =>
    { fst := ⋂ c ∈ S, (c : Concept _ _ _).fst
      snd := intentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst)
      closure_fst := rfl
      closure_snd := by
        simp_rw [← closure_snd, ← extentClosure_Union₂,
          extentClosure_intentClosure_extentClosure] }⟩

instance : CompleteLattice (Concept α β r) :=
  { Concept.lattice, Concept.boundedOrder with
    supₛ := supₛ
    le_sup := fun S c hc => snd_subset_snd_iff.1 <| binterᵢ_subset_of_mem hc
    sup_le := fun S c hc =>
      snd_subset_snd_iff.1 <| subset_interᵢ₂ fun d hd => snd_subset_snd_iff.2 <| hc d hd
    infₛ := infₛ
    inf_le := fun S c => binterᵢ_subset_of_mem
    le_inf := fun S c => subset_interᵢ₂ }

/- warning: concept.top_fst -> Concept.top_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Top.top.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toHasTop.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (Top.top.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteLattice.toTop.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instCompleteLatticeConcept.{u2, u1} α β r))))) (Set.univ.{u2} α)
Case conversion may be inaccurate. Consider using '#align concept.top_fst Concept.top_fstₓ'. -/
@[simp]
theorem top_fst : (⊤ : Concept α β r).fst = univ :=
  rfl
#align concept.top_fst Concept.top_fst

/- warning: concept.top_snd -> Concept.top_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Top.top.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toHasTop.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) (intentClosure.{u1, u2} α β r (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Top.top.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toTop.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instCompleteLatticeConcept.{u1, u2} α β r))))) (intentClosure.{u1, u2} α β r (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align concept.top_snd Concept.top_sndₓ'. -/
@[simp]
theorem top_snd : (⊤ : Concept α β r).snd = intentClosure r univ :=
  rfl
#align concept.top_snd Concept.top_snd

/- warning: concept.bot_fst -> Concept.bot_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Bot.bot.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toHasBot.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) (extentClosure.{u1, u2} α β r (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (Bot.bot.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteLattice.toBot.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instCompleteLatticeConcept.{u2, u1} α β r))))) (extentClosure.{u2, u1} α β r (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align concept.bot_fst Concept.bot_fstₓ'. -/
@[simp]
theorem bot_fst : (⊥ : Concept α β r).fst = extentClosure r univ :=
  rfl
#align concept.bot_fst Concept.bot_fst

/- warning: concept.bot_snd -> Concept.bot_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Bot.bot.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toHasBot.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) (Set.univ.{u2} β)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (Bot.bot.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toBot.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instCompleteLatticeConcept.{u1, u2} α β r))))) (Set.univ.{u2} β)
Case conversion may be inaccurate. Consider using '#align concept.bot_snd Concept.bot_sndₓ'. -/
@[simp]
theorem bot_snd : (⊥ : Concept α β r).snd = univ :=
  rfl
#align concept.bot_snd Concept.bot_snd

/- warning: concept.sup_fst -> Concept.sup_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (c : Concept.{u1, u2} α β r) (d : Concept.{u1, u2} α β r), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (HasSup.sup.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasSup.{u1, u2} α β r) c d))) (extentClosure.{u1, u2} α β r (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} (c : Concept.{u2, u1} α β r) (d : Concept.{u2, u1} α β r), Eq.{succ u2} (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (HasSup.sup.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instHasSupConcept.{u2, u1} α β r) c d))) (extentClosure.{u2, u1} α β r (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d))))
Case conversion may be inaccurate. Consider using '#align concept.sup_fst Concept.sup_fstₓ'. -/
@[simp]
theorem sup_fst (c d : Concept α β r) : (c ⊔ d).fst = extentClosure r (c.snd ∩ d.snd) :=
  rfl
#align concept.sup_fst Concept.sup_fst

/- warning: concept.sup_snd -> Concept.sup_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (c : Concept.{u1, u2} α β r) (d : Concept.{u1, u2} α β r), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (HasSup.sup.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasSup.{u1, u2} α β r) c d))) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} (c : Concept.{u2, u1} α β r) (d : Concept.{u2, u1} α β r), Eq.{succ u1} (Set.{u1} β) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (HasSup.sup.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instHasSupConcept.{u2, u1} α β r) c d))) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d)))
Case conversion may be inaccurate. Consider using '#align concept.sup_snd Concept.sup_sndₓ'. -/
@[simp]
theorem sup_snd (c d : Concept α β r) : (c ⊔ d).snd = c.snd ∩ d.snd :=
  rfl
#align concept.sup_snd Concept.sup_snd

/- warning: concept.inf_fst -> Concept.inf_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (c : Concept.{u1, u2} α β r) (d : Concept.{u1, u2} α β r), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (HasInf.inf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasInf.{u1, u2} α β r) c d))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} (c : Concept.{u2, u1} α β r) (d : Concept.{u2, u1} α β r), Eq.{succ u2} (Set.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (HasInf.inf.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instHasInfConcept.{u2, u1} α β r) c d))) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d)))
Case conversion may be inaccurate. Consider using '#align concept.inf_fst Concept.inf_fstₓ'. -/
@[simp]
theorem inf_fst (c d : Concept α β r) : (c ⊓ d).fst = c.fst ∩ d.fst :=
  rfl
#align concept.inf_fst Concept.inf_fst

/- warning: concept.inf_snd -> Concept.inf_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (c : Concept.{u1, u2} α β r) (d : Concept.{u1, u2} α β r), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (HasInf.inf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasInf.{u1, u2} α β r) c d))) (intentClosure.{u1, u2} α β r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r d))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} (c : Concept.{u2, u1} α β r) (d : Concept.{u2, u1} α β r), Eq.{succ u1} (Set.{u1} β) (Prod.snd.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r (HasInf.inf.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instHasInfConcept.{u2, u1} α β r) c d))) (intentClosure.{u2, u1} α β r (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r c)) (Prod.fst.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Concept.toProd.{u2, u1} α β r d))))
Case conversion may be inaccurate. Consider using '#align concept.inf_snd Concept.inf_sndₓ'. -/
@[simp]
theorem inf_snd (c d : Concept α β r) : (c ⊓ d).snd = intentClosure r (c.fst ∩ d.fst) :=
  rfl
#align concept.inf_snd Concept.inf_snd

/- warning: concept.Sup_fst -> Concept.supₛ_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u1 u2} (Concept.{u1, u2} α β r)), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (SupSet.supₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasSup.{u1, u2} α β r) S))) (extentClosure.{u1, u2} α β r (Set.interᵢ.{u2, succ (max u1 u2)} β (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u2, 0} β (Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u2 u1} (Concept.{u1, u2} α β r)), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (SupSet.supₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instSupSetConcept.{u1, u2} α β r) S))) (extentClosure.{u1, u2} α β r (Set.interᵢ.{u2, succ (max u1 u2)} β (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u2, 0} β (Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)))))
Case conversion may be inaccurate. Consider using '#align concept.Sup_fst Concept.supₛ_fstₓ'. -/
@[simp]
theorem supₛ_fst (S : Set (Concept α β r)) :
    (supₛ S).fst = extentClosure r (⋂ c ∈ S, (c : Concept _ _ _).snd) :=
  rfl
#align concept.Sup_fst Concept.supₛ_fst

/- warning: concept.Sup_snd -> Concept.supₛ_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u1 u2} (Concept.{u1, u2} α β r)), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (SupSet.supₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasSup.{u1, u2} α β r) S))) (Set.interᵢ.{u2, succ (max u1 u2)} β (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u2, 0} β (Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u2 u1} (Concept.{u1, u2} α β r)), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (SupSet.supₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instSupSetConcept.{u1, u2} α β r) S))) (Set.interᵢ.{u2, succ (max u1 u2)} β (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u2, 0} β (Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))))
Case conversion may be inaccurate. Consider using '#align concept.Sup_snd Concept.supₛ_sndₓ'. -/
@[simp]
theorem supₛ_snd (S : Set (Concept α β r)) : (supₛ S).snd = ⋂ c ∈ S, (c : Concept _ _ _).snd :=
  rfl
#align concept.Sup_snd Concept.supₛ_snd

/- warning: concept.Inf_fst -> Concept.infₛ_fst is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u1 u2} (Concept.{u1, u2} α β r)), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (InfSet.infₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasInf.{u1, u2} α β r) S))) (Set.interᵢ.{u1, succ (max u1 u2)} α (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u1, 0} α (Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u2 u1} (Concept.{u1, u2} α β r)), Eq.{succ u1} (Set.{u1} α) (Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (InfSet.infₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instInfSetConcept.{u1, u2} α β r) S))) (Set.interᵢ.{u1, succ (max u1 u2)} α (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u1, 0} α (Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c))))
Case conversion may be inaccurate. Consider using '#align concept.Inf_fst Concept.infₛ_fstₓ'. -/
@[simp]
theorem infₛ_fst (S : Set (Concept α β r)) : (infₛ S).fst = ⋂ c ∈ S, (c : Concept _ _ _).fst :=
  rfl
#align concept.Inf_fst Concept.infₛ_fst

/- warning: concept.Inf_snd -> Concept.infₛ_snd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u1 u2} (Concept.{u1, u2} α β r)), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (InfSet.infₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.hasInf.{u1, u2} α β r) S))) (intentClosure.{u1, u2} α β r (Set.interᵢ.{u1, succ (max u1 u2)} α (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u1, 0} α (Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.Mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u1 u2} (Concept.{u1, u2} α β r)) (Set.hasMem.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (S : Set.{max u2 u1} (Concept.{u1, u2} α β r)), Eq.{succ u2} (Set.{u2} β) (Prod.snd.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r (InfSet.infₛ.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instInfSetConcept.{u1, u2} α β r) S))) (intentClosure.{u1, u2} α β r (Set.interᵢ.{u1, succ (max u1 u2)} α (Concept.{u1, u2} α β r) (fun (c : Concept.{u1, u2} α β r) => Set.interᵢ.{u1, 0} α (Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) (fun (H : Membership.mem.{max u1 u2, max u1 u2} (Concept.{u1, u2} α β r) (Set.{max u2 u1} (Concept.{u1, u2} α β r)) (Set.instMembershipSet.{max u1 u2} (Concept.{u1, u2} α β r)) c S) => Prod.fst.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Concept.toProd.{u1, u2} α β r c)))))
Case conversion may be inaccurate. Consider using '#align concept.Inf_snd Concept.infₛ_sndₓ'. -/
@[simp]
theorem infₛ_snd (S : Set (Concept α β r)) :
    (infₛ S).snd = intentClosure r (⋂ c ∈ S, (c : Concept _ _ _).fst) :=
  rfl
#align concept.Inf_snd Concept.infₛ_snd

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

#print Concept.swap /-
/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.toProd.symm, c.closure_snd, c.closure_fst⟩
#align concept.swap Concept.swap
-/

/- warning: concept.swap_swap -> Concept.swap_swap is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} (c : Concept.{u1, u2} α β r), Eq.{max (succ u1) (succ u2)} (Concept.{u1, u2} α β (Function.swap.{succ u2, succ u1, 1} β α (fun (ᾰ : β) (ᾰ : α) => Prop) (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r))) (Concept.swap.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) (Concept.swap.{u1, u2} α β r c)) c
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} (c : Concept.{u2, u1} α β r), Eq.{max (succ u2) (succ u1)} (Concept.{u2, u1} α β (Function.swap.{succ u1, succ u2, 1} β α (fun (ᾰ : β) (ᾰ : α) => Prop) (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r))) (Concept.swap.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r) (Concept.swap.{u2, u1} α β r c)) c
Case conversion may be inaccurate. Consider using '#align concept.swap_swap Concept.swap_swapₓ'. -/
@[simp]
theorem swap_swap (c : Concept α β r) : c.symm.symm = c :=
  ext rfl
#align concept.swap_swap Concept.swap_swap

/- warning: concept.swap_le_swap_iff -> Concept.swap_le_swap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (LE.le.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Preorder.toLE.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.completeLattice.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)))))) (Concept.swap.{u1, u2} α β r c) (Concept.swap.{u1, u2} α β r d)) (LE.le.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) d c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {c : Concept.{u2, u1} α β r} {d : Concept.{u2, u1} α β r}, Iff (LE.le.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Preorder.toLE.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.instCompleteLatticeConcept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)))))) (Concept.swap.{u2, u1} α β r c) (Concept.swap.{u2, u1} α β r d)) (LE.le.{max u2 u1} (Concept.{u2, u1} α β r) (Preorder.toLE.{max u2 u1} (Concept.{u2, u1} α β r) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instCompleteLatticeConcept.{u2, u1} α β r))))) d c)
Case conversion may be inaccurate. Consider using '#align concept.swap_le_swap_iff Concept.swap_le_swap_iffₓ'. -/
@[simp]
theorem swap_le_swap_iff : c.symm ≤ d.symm ↔ d ≤ c :=
  snd_subset_snd_iff
#align concept.swap_le_swap_iff Concept.swap_le_swap_iff

/- warning: concept.swap_lt_swap_iff -> Concept.swap_lt_swap_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop} {c : Concept.{u1, u2} α β r} {d : Concept.{u1, u2} α β r}, Iff (LT.lt.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Preorder.toLT.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.completeLattice.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)))))) (Concept.swap.{u1, u2} α β r c) (Concept.swap.{u1, u2} α β r d)) (LT.lt.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLT.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r))))) d c)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {r : α -> β -> Prop} {c : Concept.{u2, u1} α β r} {d : Concept.{u2, u1} α β r}, Iff (LT.lt.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Preorder.toLT.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.instCompleteLatticeConcept.{u1, u2} β α (Function.swap.{succ u2, succ u1, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)))))) (Concept.swap.{u2, u1} α β r c) (Concept.swap.{u2, u1} α β r d)) (LT.lt.{max u2 u1} (Concept.{u2, u1} α β r) (Preorder.toLT.{max u2 u1} (Concept.{u2, u1} α β r) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u2, u1} α β r) (Concept.instCompleteLatticeConcept.{u2, u1} α β r))))) d c)
Case conversion may be inaccurate. Consider using '#align concept.swap_lt_swap_iff Concept.swap_lt_swap_iffₓ'. -/
@[simp]
theorem swap_lt_swap_iff : c.symm < d.symm ↔ d < c :=
  snd_ssubset_snd_iff
#align concept.swap_lt_swap_iff Concept.swap_lt_swap_iff

/- warning: concept.swap_equiv -> Concept.swapEquiv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, OrderIso.{max u1 u2, max u2 u1} (OrderDual.{max u1 u2} (Concept.{u1, u2} α β r)) (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (OrderDual.hasLe.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.completeLattice.{u1, u2} α β r)))))) (Preorder.toLE.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u2 u1} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.completeLattice.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r))))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} {r : α -> β -> Prop}, OrderIso.{max u2 u1, max u1 u2} (OrderDual.{max u2 u1} (Concept.{u1, u2} α β r)) (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (OrderDual.instLEOrderDual.{max u1 u2} (Concept.{u1, u2} α β r) (Preorder.toLE.{max u1 u2} (Concept.{u1, u2} α β r) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u1, u2} α β r) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Concept.{u1, u2} α β r) (Concept.instCompleteLatticeConcept.{u1, u2} α β r)))))) (Preorder.toLE.{max u1 u2} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (PartialOrder.toPreorder.{max u1 u2} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteSemilatticeInf.toPartialOrder.{max u1 u2} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (CompleteLattice.toCompleteSemilatticeInf.{max u1 u2} (Concept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r)) (Concept.instCompleteLatticeConcept.{u2, u1} β α (Function.swap.{succ u1, succ u2, 1} α β (fun (ᾰ : α) (ᾰ : β) => Prop) r))))))
Case conversion may be inaccurate. Consider using '#align concept.swap_equiv Concept.swapEquivₓ'. -/
/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r)
    where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' c d := swap_le_swap_iff
#align concept.swap_equiv Concept.swapEquiv

end Concept

