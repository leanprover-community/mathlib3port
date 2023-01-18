/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.set.basic
! leanprover-community/mathlib commit 008205aa645b3f194c1da47025c5f110c8406eab
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.SymmDiff
import Mathbin.Logic.Function.Iterate

/-!
# Basic properties of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coercion from `set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the file `set_theory/zfc.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : set α` and `s₁ s₂ : set α` are subsets of `α`

-  `t : set β` is a subset of `β`.

Definitions in the file:

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `nontrivial s : Prop` : the predicate saying that `s` has at least two distinct elements.

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

* For `s : set α`, do not use `subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, union, intersection, insert, singleton, complement, powerset

-/


/-! ### Set coercion to a type -/


open Function

universe u v w x

namespace Set

variable {α : Type _} {s t : Set α}

instance : LE (Set α) :=
  ⟨fun s t => ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

instance : HasSubset (Set α) :=
  ⟨(· ≤ ·)⟩

instance {α : Type _} : BooleanAlgebra (Set α) :=
  {
    (inferInstance :
      BooleanAlgebra (α →
          Prop)) with
    sup := fun s t => { x | x ∈ s ∨ x ∈ t }
    le := (· ≤ ·)
    lt := fun s t => s ⊆ t ∧ ¬t ⊆ s
    inf := fun s t => { x | x ∈ s ∧ x ∈ t }
    bot := ∅
    compl := fun s => { x | x ∉ s }
    top := univ
    sdiff := fun s t => { x | x ∈ s ∧ x ∉ t } }

instance : HasSSubset (Set α) :=
  ⟨(· < ·)⟩

instance : Union (Set α) :=
  ⟨(· ⊔ ·)⟩

instance : Inter (Set α) :=
  ⟨(· ⊓ ·)⟩

/- warning: set.top_eq_univ -> Set.top_eq_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (Top.top.{u1} (Set.{u1} α) (BooleanAlgebra.toHasTop.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (Top.top.{u1} (Set.{u1} α) (BooleanAlgebra.toTop.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.top_eq_univ Set.top_eq_univₓ'. -/
@[simp]
theorem top_eq_univ : (⊤ : Set α) = univ :=
  rfl
#align set.top_eq_univ Set.top_eq_univ

/- warning: set.bot_eq_empty -> Set.bot_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (Bot.bot.{u1} (Set.{u1} α) (BooleanAlgebra.toHasBot.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (Bot.bot.{u1} (Set.{u1} α) (BooleanAlgebra.toBot.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.bot_eq_empty Set.bot_eq_emptyₓ'. -/
@[simp]
theorem bot_eq_empty : (⊥ : Set α) = ∅ :=
  rfl
#align set.bot_eq_empty Set.bot_eq_empty

/- warning: set.sup_eq_union -> Set.sup_eq_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> (Set.{u1} α)) (HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> (Set.{u1} α)) (fun (x._@.Mathlib.Data.Set.Basic._hyg.336 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.338 : Set.{u1} α) => HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) x._@.Mathlib.Data.Set.Basic._hyg.336 x._@.Mathlib.Data.Set.Basic._hyg.338) (fun (x._@.Mathlib.Data.Set.Basic._hyg.351 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.353 : Set.{u1} α) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.351 x._@.Mathlib.Data.Set.Basic._hyg.353)
Case conversion may be inaccurate. Consider using '#align set.sup_eq_union Set.sup_eq_unionₓ'. -/
@[simp]
theorem sup_eq_union : ((· ⊔ ·) : Set α → Set α → Set α) = (· ∪ ·) :=
  rfl
#align set.sup_eq_union Set.sup_eq_union

/- warning: set.inf_eq_inter -> Set.inf_eq_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> (Set.{u1} α)) (HasInf.inf.{u1} (Set.{u1} α) (SemilatticeInf.toHasInf.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> (Set.{u1} α)) (fun (x._@.Mathlib.Data.Set.Basic._hyg.388 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.390 : Set.{u1} α) => HasInf.inf.{u1} (Set.{u1} α) (Lattice.toHasInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))) x._@.Mathlib.Data.Set.Basic._hyg.388 x._@.Mathlib.Data.Set.Basic._hyg.390) (fun (x._@.Mathlib.Data.Set.Basic._hyg.403 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.405 : Set.{u1} α) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.403 x._@.Mathlib.Data.Set.Basic._hyg.405)
Case conversion may be inaccurate. Consider using '#align set.inf_eq_inter Set.inf_eq_interₓ'. -/
@[simp]
theorem inf_eq_inter : ((· ⊓ ·) : Set α → Set α → Set α) = (· ∩ ·) :=
  rfl
#align set.inf_eq_inter Set.inf_eq_inter

#print Set.le_eq_subset /-
@[simp]
theorem le_eq_subset : ((· ≤ ·) : Set α → Set α → Prop) = (· ⊆ ·) :=
  rfl
#align set.le_eq_subset Set.le_eq_subset
-/

/- warning: set.lt_eq_ssubset -> Set.lt_eq_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> Prop) (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))))) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} ((Set.{u1} α) -> (Set.{u1} α) -> Prop) (fun (x._@.Mathlib.Data.Set.Basic._hyg.490 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.492 : Set.{u1} α) => LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) x._@.Mathlib.Data.Set.Basic._hyg.490 x._@.Mathlib.Data.Set.Basic._hyg.492) (fun (x._@.Mathlib.Data.Set.Basic._hyg.505 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.507 : Set.{u1} α) => HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.505 x._@.Mathlib.Data.Set.Basic._hyg.507)
Case conversion may be inaccurate. Consider using '#align set.lt_eq_ssubset Set.lt_eq_ssubsetₓ'. -/
@[simp]
theorem lt_eq_ssubset : ((· < ·) : Set α → Set α → Prop) = (· ⊂ ·) :=
  rfl
#align set.lt_eq_ssubset Set.lt_eq_ssubset

#print Set.le_iff_subset /-
theorem le_iff_subset : s ≤ t ↔ s ⊆ t :=
  Iff.rfl
#align set.le_iff_subset Set.le_iff_subset
-/

/- warning: set.lt_iff_ssubset -> Set.lt_iff_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))))) s t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) s t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.lt_iff_ssubset Set.lt_iff_ssubsetₓ'. -/
theorem lt_iff_ssubset : s < t ↔ s ⊂ t :=
  Iff.rfl
#align set.lt_iff_ssubset Set.lt_iff_ssubset

alias le_iff_subset ↔ _root_.has_le.le.subset _root_.has_subset.subset.le
#align has_le.le.subset LE.le.subset
#align has_subset.subset.le HasSubset.Subset.le

/- warning: has_lt.lt.ssubset -> LT.lt.ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))))) s t) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) s t) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align has_lt.lt.ssubset LT.lt.ssubsetₓ'. -/
/- warning: has_ssubset.ssubset.lt -> HasSSubset.SSubset.lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (LT.lt.{u1} (Set.{u1} α) (Preorder.toLT.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) s t)
Case conversion may be inaccurate. Consider using '#align has_ssubset.ssubset.lt HasSSubset.SSubset.ltₓ'. -/
alias lt_iff_ssubset ↔ _root_.has_lt.lt.ssubset _root_.has_ssubset.ssubset.lt
#align has_lt.lt.ssubset LT.lt.ssubset
#align has_ssubset.ssubset.lt HasSSubset.SSubset.lt

/-- Coercion from a set to the corresponding subtype. -/
instance {α : Type u} : CoeSort (Set α) (Type u) :=
  ⟨fun s => { x // x ∈ s }⟩

#print Set.PiSetCoe.canLift /-
instance PiSetCoe.canLift (ι : Type u) (α : ∀ i : ι, Type v) [ne : ∀ i, Nonempty (α i)]
    (s : Set ι) : CanLift (∀ i : s, α i) (∀ i, α i) (fun f i => f i) fun _ => True :=
  PiSubtype.canLift ι α s
#align set.pi_set_coe.can_lift Set.PiSetCoe.canLift
-/

#print Set.PiSetCoe.canLift' /-
instance PiSetCoe.canLift' (ι : Type u) (α : Type v) [ne : Nonempty α] (s : Set ι) :
    CanLift (s → α) (ι → α) (fun f i => f i) fun _ => True :=
  PiSetCoe.canLift ι (fun _ => α) s
#align set.pi_set_coe.can_lift' Set.PiSetCoe.canLift'
-/

end Set

section SetCoe

variable {α : Type u}

#print Set.coe_eq_subtype /-
theorem Set.coe_eq_subtype (s : Set α) : ↥s = { x // x ∈ s } :=
  rfl
#align set.coe_eq_subtype Set.coe_eq_subtype
-/

#print Set.coe_setOf /-
@[simp]
theorem Set.coe_setOf (p : α → Prop) : ↥{ x | p x } = { x // p x } :=
  rfl
#align set.coe_set_of Set.coe_setOf
-/

#print SetCoe.forall /-
@[simp]
theorem SetCoe.forall {s : Set α} {p : s → Prop} : (∀ x : s, p x) ↔ ∀ (x) (h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.forall
#align set_coe.forall SetCoe.forall
-/

#print SetCoe.exists /-
@[simp]
theorem SetCoe.exists {s : Set α} {p : s → Prop} :
    (∃ x : s, p x) ↔ ∃ (x : _)(h : x ∈ s), p ⟨x, h⟩ :=
  Subtype.exists
#align set_coe.exists SetCoe.exists
-/

#print SetCoe.exists' /-
theorem SetCoe.exists' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∃ (x : _)(h : x ∈ s), p x h) ↔ ∃ x : s, p x x.2 :=
  (@SetCoe.exists _ _ fun x => p x.1 x.2).symm
#align set_coe.exists' SetCoe.exists'
-/

#print SetCoe.forall' /-
theorem SetCoe.forall' {s : Set α} {p : ∀ x, x ∈ s → Prop} :
    (∀ (x) (h : x ∈ s), p x h) ↔ ∀ x : s, p x x.2 :=
  (@SetCoe.forall _ _ fun x => p x.1 x.2).symm
#align set_coe.forall' SetCoe.forall'
-/

#print set_coe_cast /-
@[simp]
theorem set_coe_cast :
    ∀ {s t : Set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
  | s, _, rfl, _, ⟨x, h⟩ => rfl
#align set_coe_cast set_coe_cast
-/

#print SetCoe.ext /-
theorem SetCoe.ext {s : Set α} {a b : s} : (↑a : α) = ↑b → a = b :=
  Subtype.eq
#align set_coe.ext SetCoe.ext
-/

#print SetCoe.ext_iff /-
theorem SetCoe.ext_iff {s : Set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
  Iff.intro SetCoe.ext fun h => h ▸ rfl
#align set_coe.ext_iff SetCoe.ext_iff
-/

end SetCoe

#print Subtype.mem /-
/-- See also `subtype.prop` -/
theorem Subtype.mem {α : Type _} {s : Set α} (p : s) : (p : α) ∈ s :=
  p.Prop
#align subtype.mem Subtype.mem
-/

#print Eq.subset /-
/-- Duplicate of `eq.subset'`, which currently has elaboration problems. -/
theorem Eq.subset {α} {s t : Set α} : s = t → s ⊆ t :=
  Eq.subset'
#align eq.subset Eq.subset
-/

namespace Set

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

instance : Inhabited (Set α) :=
  ⟨∅⟩

#print Set.ext /-
@[ext]
theorem ext {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
  funext fun x => propext (h x)
#align set.ext Set.ext
-/

#print Set.ext_iff /-
theorem ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
  ⟨fun h x => by rw [h], ext⟩
#align set.ext_iff Set.ext_iff
-/

#print Set.mem_of_mem_of_subset /-
@[trans]
theorem mem_of_mem_of_subset {x : α} {s t : Set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
  h hx
#align set.mem_of_mem_of_subset Set.mem_of_mem_of_subset
-/

#print Set.forall_in_swap /-
theorem forall_in_swap {p : α → β → Prop} : (∀ a ∈ s, ∀ (b), p a b) ↔ ∀ (b), ∀ a ∈ s, p a b := by
  tauto
#align set.forall_in_swap Set.forall_in_swap
-/

/-! ### Lemmas about `mem` and `set_of` -/


#print Set.mem_setOf /-
theorem mem_setOf {a : α} {p : α → Prop} : a ∈ { x | p x } ↔ p a :=
  Iff.rfl
#align set.mem_set_of Set.mem_setOf
-/

#print Membership.Mem.out /-
/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
theorem Membership.Mem.out {p : α → Prop} {a : α} (h : a ∈ { x | p x }) : p a :=
  h
#align has_mem.mem.out Membership.Mem.out
-/

#print Set.nmem_setOf_iff /-
theorem nmem_setOf_iff {a : α} {p : α → Prop} : a ∉ { x | p x } ↔ ¬p a :=
  Iff.rfl
#align set.nmem_set_of_iff Set.nmem_setOf_iff
-/

#print Set.setOf_mem_eq /-
@[simp]
theorem setOf_mem_eq {s : Set α} : { x | x ∈ s } = s :=
  rfl
#align set.set_of_mem_eq Set.setOf_mem_eq
-/

#print Set.setOf_set /-
theorem setOf_set {s : Set α} : setOf s = s :=
  rfl
#align set.set_of_set Set.setOf_set
-/

#print Set.setOf_app_iff /-
theorem setOf_app_iff {p : α → Prop} {x : α} : { x | p x } x ↔ p x :=
  Iff.rfl
#align set.set_of_app_iff Set.setOf_app_iff
-/

#print Set.mem_def /-
theorem mem_def {a : α} {s : Set α} : a ∈ s ↔ s a :=
  Iff.rfl
#align set.mem_def Set.mem_def
-/

#print Set.setOf_bijective /-
theorem setOf_bijective : Bijective (setOf : (α → Prop) → Set α) :=
  bijective_id
#align set.set_of_bijective Set.setOf_bijective
-/

#print Set.setOf_subset_setOf /-
@[simp]
theorem setOf_subset_setOf {p q : α → Prop} : { a | p a } ⊆ { a | q a } ↔ ∀ a, p a → q a :=
  Iff.rfl
#align set.set_of_subset_set_of Set.setOf_subset_setOf
-/

/- warning: set.set_of_and -> Set.setOf_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (a : α) => And (p a) (q a))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (setOf.{u1} α (fun (a : α) => p a)) (setOf.{u1} α (fun (a : α) => q a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (a : α) => And (p a) (q a))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (setOf.{u1} α (fun (a : α) => p a)) (setOf.{u1} α (fun (a : α) => q a)))
Case conversion may be inaccurate. Consider using '#align set.set_of_and Set.setOf_andₓ'. -/
theorem setOf_and {p q : α → Prop} : { a | p a ∧ q a } = { a | p a } ∩ { a | q a } :=
  rfl
#align set.set_of_and Set.setOf_and

/- warning: set.set_of_or -> Set.setOf_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (a : α) => Or (p a) (q a))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (setOf.{u1} α (fun (a : α) => p a)) (setOf.{u1} α (fun (a : α) => q a)))
but is expected to have type
  forall {α : Type.{u1}} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (a : α) => Or (p a) (q a))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (setOf.{u1} α (fun (a : α) => p a)) (setOf.{u1} α (fun (a : α) => q a)))
Case conversion may be inaccurate. Consider using '#align set.set_of_or Set.setOf_orₓ'. -/
theorem setOf_or {p q : α → Prop} : { a | p a ∨ q a } = { a | p a } ∪ { a | q a } :=
  rfl
#align set.set_of_or Set.setOf_or

/-! ### Subset and strict subset relations -/


instance : IsRefl (Set α) (· ⊆ ·) :=
  LE.le.is_refl

instance : IsTrans (Set α) (· ⊆ ·) :=
  LE.le.is_trans

instance : IsAntisymm (Set α) (· ⊆ ·) :=
  LE.le.is_antisymm

instance : IsIrrefl (Set α) (· ⊂ ·) :=
  LT.lt.is_irrefl

instance : IsTrans (Set α) (· ⊂ ·) :=
  LT.lt.is_trans

instance : IsAsymm (Set α) (· ⊂ ·) :=
  LT.lt.is_asymm

instance : IsNonstrictStrictOrder (Set α) (· ⊆ ·) (· ⊂ ·) :=
  ⟨fun _ _ => Iff.rfl⟩

#print Set.subset_def /-
-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t :=
  rfl
#align set.subset_def Set.subset_def
-/

/- warning: set.ssubset_def -> Set.ssubset_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{1} Prop (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{1} Prop (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)))
Case conversion may be inaccurate. Consider using '#align set.ssubset_def Set.ssubset_defₓ'. -/
theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ ¬t ⊆ s) :=
  rfl
#align set.ssubset_def Set.ssubset_def

#print Set.Subset.refl /-
@[refl]
theorem Subset.refl (a : Set α) : a ⊆ a := fun x => id
#align set.subset.refl Set.Subset.refl
-/

#print Set.Subset.rfl /-
theorem Subset.rfl {s : Set α} : s ⊆ s :=
  Subset.refl s
#align set.subset.rfl Set.Subset.rfl
-/

#print Set.Subset.trans /-
@[trans]
theorem Subset.trans {a b c : Set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c := fun x h => bc <| ab h
#align set.subset.trans Set.Subset.trans
-/

#print Set.mem_of_eq_of_mem /-
@[trans]
theorem mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
  hx.symm ▸ h
#align set.mem_of_eq_of_mem Set.mem_of_eq_of_mem
-/

#print Set.Subset.antisymm /-
theorem Subset.antisymm {a b : Set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
  Set.ext fun x => ⟨@h₁ _, @h₂ _⟩
#align set.subset.antisymm Set.Subset.antisymm
-/

#print Set.Subset.antisymm_iff /-
theorem Subset.antisymm_iff {a b : Set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
  ⟨fun e => ⟨e.Subset, e.symm.Subset⟩, fun ⟨h₁, h₂⟩ => Subset.antisymm h₁ h₂⟩
#align set.subset.antisymm_iff Set.Subset.antisymm_iff
-/

#print Set.eq_of_subset_of_subset /-
-- an alternative name
theorem eq_of_subset_of_subset {a b : Set α} : a ⊆ b → b ⊆ a → a = b :=
  subset.antisymm
#align set.eq_of_subset_of_subset Set.eq_of_subset_of_subset
-/

#print Set.mem_of_subset_of_mem /-
theorem mem_of_subset_of_mem {s₁ s₂ : Set α} {a : α} (h : s₁ ⊆ s₂) : a ∈ s₁ → a ∈ s₂ :=
  @h _
#align set.mem_of_subset_of_mem Set.mem_of_subset_of_mem
-/

#print Set.not_mem_subset /-
theorem not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s :=
  mt <| mem_of_subset_of_mem h
#align set.not_mem_subset Set.not_mem_subset
-/

/- warning: set.not_subset -> Set.not_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)) (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t))))
Case conversion may be inaccurate. Consider using '#align set.not_subset Set.not_subsetₓ'. -/
theorem not_subset : ¬s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by simp only [subset_def, not_forall]
#align set.not_subset Set.not_subset

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/


/- warning: set.eq_or_ssubset_of_subset -> Set.eq_or_ssubset_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Or (Eq.{succ u1} (Set.{u1} α) s t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Or (Eq.{succ u1} (Set.{u1} α) s t) (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.eq_or_ssubset_of_subset Set.eq_or_ssubset_of_subsetₓ'. -/
protected theorem eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t :=
  eq_or_lt_of_le h
#align set.eq_or_ssubset_of_subset Set.eq_or_ssubset_of_subset

/- warning: set.exists_of_ssubset -> Set.exists_of_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))))
Case conversion may be inaccurate. Consider using '#align set.exists_of_ssubset Set.exists_of_ssubsetₓ'. -/
theorem exists_of_ssubset {s t : Set α} (h : s ⊂ t) : ∃ x ∈ t, x ∉ s :=
  not_subset.1 h.2
#align set.exists_of_ssubset Set.exists_of_ssubset

/- warning: set.ssubset_iff_subset_ne -> Set.ssubset_iff_subset_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (Ne.{succ u1} (Set.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (Ne.{succ u1} (Set.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.ssubset_iff_subset_ne Set.ssubset_iff_subset_neₓ'. -/
protected theorem ssubset_iff_subset_ne {s t : Set α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
  @lt_iff_le_and_ne (Set α) _ s t
#align set.ssubset_iff_subset_ne Set.ssubset_iff_subset_ne

/- warning: set.ssubset_iff_of_subset -> Set.ssubset_iff_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)))))
Case conversion may be inaccurate. Consider using '#align set.ssubset_iff_of_subset Set.ssubset_iff_of_subsetₓ'. -/
theorem ssubset_iff_of_subset {s t : Set α} (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
  ⟨exists_of_ssubset, fun ⟨x, hxt, hxs⟩ => ⟨h, fun h => hxs <| h hxt⟩⟩
#align set.ssubset_iff_of_subset Set.ssubset_iff_of_subset

/- warning: set.ssubset_of_ssubset_of_subset -> Set.ssubset_of_ssubset_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s₃ : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ s₃) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s₁ s₃)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s₃ : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ s₃) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s₁ s₃)
Case conversion may be inaccurate. Consider using '#align set.ssubset_of_ssubset_of_subset Set.ssubset_of_ssubset_of_subsetₓ'. -/
protected theorem ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊂ s₂)
    (hs₂s₃ : s₂ ⊆ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂.1 hs₂s₃, fun hs₃s₁ => hs₁s₂.2 (Subset.trans hs₂s₃ hs₃s₁)⟩
#align set.ssubset_of_ssubset_of_subset Set.ssubset_of_ssubset_of_subset

/- warning: set.ssubset_of_subset_of_ssubset -> Set.ssubset_of_subset_of_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s₃ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s₂ s₃) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s₁ s₃)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s₃ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s₂ s₃) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s₁ s₃)
Case conversion may be inaccurate. Consider using '#align set.ssubset_of_subset_of_ssubset Set.ssubset_of_subset_of_ssubsetₓ'. -/
protected theorem ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : Set α} (hs₁s₂ : s₁ ⊆ s₂)
    (hs₂s₃ : s₂ ⊂ s₃) : s₁ ⊂ s₃ :=
  ⟨Subset.trans hs₁s₂ hs₂s₃.1, fun hs₃s₁ => hs₂s₃.2 (Subset.trans hs₃s₁ hs₁s₂)⟩
#align set.ssubset_of_subset_of_ssubset Set.ssubset_of_subset_of_ssubset

#print Set.not_mem_empty /-
theorem not_mem_empty (x : α) : ¬x ∈ (∅ : Set α) :=
  id
#align set.not_mem_empty Set.not_mem_empty
-/

#print Set.not_not_mem /-
@[simp]
theorem not_not_mem : ¬a ∉ s ↔ a ∈ s :=
  not_not
#align set.not_not_mem Set.not_not_mem
-/

/-! ### Non-empty sets -/


#print Set.Nonempty /-
/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def Nonempty (s : Set α) : Prop :=
  ∃ x, x ∈ s
#align set.nonempty Set.Nonempty
-/

#print Set.nonempty_coe_sort /-
@[simp]
theorem nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.Nonempty :=
  nonempty_subtype
#align set.nonempty_coe_sort Set.nonempty_coe_sort
-/

alias nonempty_coe_sort ↔ _ nonempty.coe_sort
#align set.nonempty.coe_sort Set.Nonempty.coe_sort

#print Set.nonempty_def /-
theorem nonempty_def : s.Nonempty ↔ ∃ x, x ∈ s :=
  Iff.rfl
#align set.nonempty_def Set.nonempty_def
-/

#print Set.nonempty_of_mem /-
theorem nonempty_of_mem {x} (h : x ∈ s) : s.Nonempty :=
  ⟨x, h⟩
#align set.nonempty_of_mem Set.nonempty_of_mem
-/

#print Set.Nonempty.not_subset_empty /-
theorem Nonempty.not_subset_empty : s.Nonempty → ¬s ⊆ ∅
  | ⟨x, hx⟩, hs => hs hx
#align set.nonempty.not_subset_empty Set.Nonempty.not_subset_empty
-/

#print Set.Nonempty.some /-
/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def Nonempty.some (h : s.Nonempty) : α :=
  Classical.choose h
#align set.nonempty.some Set.Nonempty.some
-/

#print Set.Nonempty.some_mem /-
protected theorem Nonempty.some_mem (h : s.Nonempty) : h.some ∈ s :=
  Classical.choose_spec h
#align set.nonempty.some_mem Set.Nonempty.some_mem
-/

#print Set.Nonempty.mono /-
theorem Nonempty.mono (ht : s ⊆ t) (hs : s.Nonempty) : t.Nonempty :=
  hs.imp ht
#align set.nonempty.mono Set.Nonempty.mono
-/

/- warning: set.nonempty_of_not_subset -> Set.nonempty_of_not_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)) -> (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)) -> (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty_of_not_subset Set.nonempty_of_not_subsetₓ'. -/
theorem nonempty_of_not_subset (h : ¬s ⊆ t) : (s \ t).Nonempty :=
  let ⟨x, xs, xt⟩ := not_subset.1 h
  ⟨x, xs, xt⟩
#align set.nonempty_of_not_subset Set.nonempty_of_not_subset

/- warning: set.nonempty_of_ssubset -> Set.nonempty_of_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))
Case conversion may be inaccurate. Consider using '#align set.nonempty_of_ssubset Set.nonempty_of_ssubsetₓ'. -/
theorem nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).Nonempty :=
  nonempty_of_not_subset ht.2
#align set.nonempty_of_ssubset Set.nonempty_of_ssubset

/- warning: set.nonempty.of_diff -> Set.Nonempty.of_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) -> (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_diff Set.Nonempty.of_diffₓ'. -/
theorem Nonempty.of_diff (h : (s \ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left
#align set.nonempty.of_diff Set.Nonempty.of_diff

/- warning: set.nonempty_of_ssubset' -> Set.nonempty_of_ssubset' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) -> (Set.Nonempty.{u1} α t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) -> (Set.Nonempty.{u1} α t)
Case conversion may be inaccurate. Consider using '#align set.nonempty_of_ssubset' Set.nonempty_of_ssubset'ₓ'. -/
theorem nonempty_of_ssubset' (ht : s ⊂ t) : t.Nonempty :=
  (nonempty_of_ssubset ht).of_diff
#align set.nonempty_of_ssubset' Set.nonempty_of_ssubset'

/- warning: set.nonempty.inl -> Set.Nonempty.inl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.inl Set.Nonempty.inlₓ'. -/
theorem Nonempty.inl (hs : s.Nonempty) : (s ∪ t).Nonempty :=
  hs.imp fun _ => Or.inl
#align set.nonempty.inl Set.Nonempty.inl

/- warning: set.nonempty.inr -> Set.Nonempty.inr is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α t) -> (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.inr Set.Nonempty.inrₓ'. -/
theorem Nonempty.inr (ht : t.Nonempty) : (s ∪ t).Nonempty :=
  ht.imp fun _ => Or.inr
#align set.nonempty.inr Set.Nonempty.inr

/- warning: set.union_nonempty -> Set.union_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Or (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Or (Set.Nonempty.{u1} α s) (Set.Nonempty.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.union_nonempty Set.union_nonemptyₓ'. -/
@[simp]
theorem union_nonempty : (s ∪ t).Nonempty ↔ s.Nonempty ∨ t.Nonempty :=
  exists_or
#align set.union_nonempty Set.union_nonempty

/- warning: set.nonempty.left -> Set.Nonempty.left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.left Set.Nonempty.leftₓ'. -/
theorem Nonempty.left (h : (s ∩ t).Nonempty) : s.Nonempty :=
  h.imp fun _ => And.left
#align set.nonempty.left Set.Nonempty.left

/- warning: set.nonempty.right -> Set.Nonempty.right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (Set.Nonempty.{u1} α t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (Set.Nonempty.{u1} α t)
Case conversion may be inaccurate. Consider using '#align set.nonempty.right Set.Nonempty.rightₓ'. -/
theorem Nonempty.right (h : (s ∩ t).Nonempty) : t.Nonempty :=
  h.imp fun _ => And.right
#align set.nonempty.right Set.Nonempty.right

/- warning: set.inter_nonempty -> Set.inter_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))
Case conversion may be inaccurate. Consider using '#align set.inter_nonempty Set.inter_nonemptyₓ'. -/
theorem inter_nonempty : (s ∩ t).Nonempty ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Iff.rfl
#align set.inter_nonempty Set.inter_nonempty

/- warning: set.inter_nonempty_iff_exists_left -> Set.inter_nonempty_iff_exists_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))
Case conversion may be inaccurate. Consider using '#align set.inter_nonempty_iff_exists_left Set.inter_nonempty_iff_exists_leftₓ'. -/
theorem inter_nonempty_iff_exists_left : (s ∩ t).Nonempty ↔ ∃ x ∈ s, x ∈ t := by
  simp_rw [inter_nonempty, exists_prop]
#align set.inter_nonempty_iff_exists_left Set.inter_nonempty_iff_exists_left

/- warning: set.inter_nonempty_iff_exists_right -> Set.inter_nonempty_iff_exists_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)))
Case conversion may be inaccurate. Consider using '#align set.inter_nonempty_iff_exists_right Set.inter_nonempty_iff_exists_rightₓ'. -/
theorem inter_nonempty_iff_exists_right : (s ∩ t).Nonempty ↔ ∃ x ∈ t, x ∈ s := by
  simp_rw [inter_nonempty, exists_prop, and_comm']
#align set.inter_nonempty_iff_exists_right Set.inter_nonempty_iff_exists_right

#print Set.nonempty_iff_univ_nonempty /-
theorem nonempty_iff_univ_nonempty : Nonempty α ↔ (univ : Set α).Nonempty :=
  ⟨fun ⟨x⟩ => ⟨x, trivial⟩, fun ⟨x, _⟩ => ⟨x⟩⟩
#align set.nonempty_iff_univ_nonempty Set.nonempty_iff_univ_nonempty
-/

#print Set.univ_nonempty /-
@[simp]
theorem univ_nonempty : ∀ [h : Nonempty α], (univ : Set α).Nonempty
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.univ_nonempty Set.univ_nonempty
-/

#print Set.Nonempty.to_subtype /-
theorem Nonempty.to_subtype : s.Nonempty → Nonempty s :=
  nonempty_subtype.2
#align set.nonempty.to_subtype Set.Nonempty.to_subtype
-/

#print Set.Nonempty.to_type /-
theorem Nonempty.to_type : s.Nonempty → Nonempty α := fun ⟨x, hx⟩ => ⟨x⟩
#align set.nonempty.to_type Set.Nonempty.to_type
-/

instance [Nonempty α] : Nonempty (Set.univ : Set α) :=
  Set.univ_nonempty.to_subtype

#print Set.nonempty_of_nonempty_subtype /-
theorem nonempty_of_nonempty_subtype [Nonempty s] : s.Nonempty :=
  nonempty_subtype.mp ‹_›
#align set.nonempty_of_nonempty_subtype Set.nonempty_of_nonempty_subtype
-/

/-! ### Lemmas about the empty set -/


/- warning: set.empty_def -> Set.empty_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (setOf.{u1} α (fun (x : α) => False))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ (succ u1)} Type.{u1} (Set.Elem.{u1} α (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Set.Elem.{u1} α (setOf.{u1} α (fun (_x : α) => False)))
Case conversion may be inaccurate. Consider using '#align set.empty_def Set.empty_defₓ'. -/
theorem empty_def : (∅ : Set α) = { x | False } :=
  rfl
#align set.empty_def Set.empty_def

#print Set.mem_empty_iff_false /-
@[simp]
theorem mem_empty_iff_false (x : α) : x ∈ (∅ : Set α) ↔ False :=
  Iff.rfl
#align set.mem_empty_iff_false Set.mem_empty_iff_false
-/

#print Set.setOf_false /-
@[simp]
theorem setOf_false : { a : α | False } = ∅ :=
  rfl
#align set.set_of_false Set.setOf_false
-/

#print Set.empty_subset /-
@[simp]
theorem empty_subset (s : Set α) : ∅ ⊆ s :=
  fun.
#align set.empty_subset Set.empty_subset
-/

#print Set.subset_empty_iff /-
theorem subset_empty_iff {s : Set α} : s ⊆ ∅ ↔ s = ∅ :=
  (Subset.antisymm_iff.trans <| and_iff_left (empty_subset _)).symm
#align set.subset_empty_iff Set.subset_empty_iff
-/

#print Set.eq_empty_iff_forall_not_mem /-
theorem eq_empty_iff_forall_not_mem {s : Set α} : s = ∅ ↔ ∀ x, x ∉ s :=
  subset_empty_iff.symm
#align set.eq_empty_iff_forall_not_mem Set.eq_empty_iff_forall_not_mem
-/

#print Set.eq_empty_of_forall_not_mem /-
theorem eq_empty_of_forall_not_mem (h : ∀ x, x ∉ s) : s = ∅ :=
  subset_empty_iff.1 h
#align set.eq_empty_of_forall_not_mem Set.eq_empty_of_forall_not_mem
-/

#print Set.eq_empty_of_subset_empty /-
theorem eq_empty_of_subset_empty {s : Set α} : s ⊆ ∅ → s = ∅ :=
  subset_empty_iff.1
#align set.eq_empty_of_subset_empty Set.eq_empty_of_subset_empty
-/

#print Set.eq_empty_of_isEmpty /-
theorem eq_empty_of_isEmpty [IsEmpty α] (s : Set α) : s = ∅ :=
  eq_empty_of_subset_empty fun x hx => isEmptyElim x
#align set.eq_empty_of_is_empty Set.eq_empty_of_isEmpty
-/

#print Set.uniqueEmpty /-
/-- There is exactly one set of a type that is empty. -/
instance uniqueEmpty [IsEmpty α] : Unique (Set α)
    where
  default := ∅
  uniq := eq_empty_of_isEmpty
#align set.unique_empty Set.uniqueEmpty
-/

#print Set.not_nonempty_iff_eq_empty /-
/-- See also `set.nonempty_iff_ne_empty`. -/
theorem not_nonempty_iff_eq_empty {s : Set α} : ¬s.Nonempty ↔ s = ∅ := by
  simp only [Set.Nonempty, eq_empty_iff_forall_not_mem, not_exists]
#align set.not_nonempty_iff_eq_empty Set.not_nonempty_iff_eq_empty
-/

#print Set.nonempty_iff_ne_empty /-
/-- See also `set.not_nonempty_iff_eq_empty`. -/
theorem nonempty_iff_ne_empty : s.Nonempty ↔ s ≠ ∅ :=
  not_nonempty_iff_eq_empty.not_right
#align set.nonempty_iff_ne_empty Set.nonempty_iff_ne_empty
-/

alias nonempty_iff_ne_empty ↔ nonempty.ne_empty _
#align set.nonempty.ne_empty Set.Nonempty.ne_empty

#print Set.not_nonempty_empty /-
@[simp]
theorem not_nonempty_empty : ¬(∅ : Set α).Nonempty := fun ⟨x, hx⟩ => hx
#align set.not_nonempty_empty Set.not_nonempty_empty
-/

#print Set.isEmpty_coe_sort /-
@[simp]
theorem isEmpty_coe_sort {s : Set α} : IsEmpty ↥s ↔ s = ∅ :=
  not_iff_not.1 <| by simpa using nonempty_iff_ne_empty
#align set.is_empty_coe_sort Set.isEmpty_coe_sort
-/

#print Set.eq_empty_or_nonempty /-
theorem eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.Nonempty :=
  or_iff_not_imp_left.2 nonempty_iff_ne_empty.2
#align set.eq_empty_or_nonempty Set.eq_empty_or_nonempty
-/

#print Set.subset_eq_empty /-
theorem subset_eq_empty {s t : Set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
  subset_empty_iff.1 <| e ▸ h
#align set.subset_eq_empty Set.subset_eq_empty
-/

#print Set.ball_empty_iff /-
theorem ball_empty_iff {p : α → Prop} : (∀ x ∈ (∅ : Set α), p x) ↔ True :=
  iff_true_intro fun x => False.elim
#align set.ball_empty_iff Set.ball_empty_iff
-/

instance (α : Type u) : IsEmpty.{u + 1} (∅ : Set α) :=
  ⟨fun x => x.2⟩

/- warning: set.empty_ssubset -> Set.empty_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s) (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s) (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.empty_ssubset Set.empty_ssubsetₓ'. -/
@[simp]
theorem empty_ssubset : ∅ ⊂ s ↔ s.Nonempty :=
  (@bot_lt_iff_ne_bot (Set α) _ _ _).trans nonempty_iff_ne_empty.symm
#align set.empty_ssubset Set.empty_ssubset

/- warning: set.nonempty.empty_ssubset -> Set.Nonempty.empty_ssubset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.empty_ssubset Set.Nonempty.empty_ssubsetₓ'. -/
alias empty_ssubset ↔ _ nonempty.empty_ssubset
#align set.nonempty.empty_ssubset Set.Nonempty.empty_ssubset

/-!

### Universal set.

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.

-/


#print Set.setOf_true /-
@[simp]
theorem setOf_true : { x : α | True } = univ :=
  rfl
#align set.set_of_true Set.setOf_true
-/

#print Set.mem_univ /-
@[simp]
theorem mem_univ (x : α) : x ∈ @univ α :=
  trivial
#align set.mem_univ Set.mem_univ
-/

#print Set.univ_eq_empty_iff /-
@[simp]
theorem univ_eq_empty_iff : (univ : Set α) = ∅ ↔ IsEmpty α :=
  eq_empty_iff_forall_not_mem.trans
    ⟨fun H => ⟨fun x => H x trivial⟩, fun H x _ => @IsEmpty.false α H x⟩
#align set.univ_eq_empty_iff Set.univ_eq_empty_iff
-/

#print Set.empty_ne_univ /-
theorem empty_ne_univ [Nonempty α] : (∅ : Set α) ≠ univ := fun e =>
  not_isEmpty_of_nonempty α <| univ_eq_empty_iff.1 e.symm
#align set.empty_ne_univ Set.empty_ne_univ
-/

#print Set.subset_univ /-
@[simp]
theorem subset_univ (s : Set α) : s ⊆ univ := fun x H => trivial
#align set.subset_univ Set.subset_univ
-/

#print Set.univ_subset_iff /-
theorem univ_subset_iff {s : Set α} : univ ⊆ s ↔ s = univ :=
  @top_le_iff _ _ _ s
#align set.univ_subset_iff Set.univ_subset_iff
-/

alias univ_subset_iff ↔ eq_univ_of_univ_subset _
#align set.eq_univ_of_univ_subset Set.eq_univ_of_univ_subset

#print Set.eq_univ_iff_forall /-
theorem eq_univ_iff_forall {s : Set α} : s = univ ↔ ∀ x, x ∈ s :=
  univ_subset_iff.symm.trans <| forall_congr' fun x => imp_iff_right trivial
#align set.eq_univ_iff_forall Set.eq_univ_iff_forall
-/

#print Set.eq_univ_of_forall /-
theorem eq_univ_of_forall {s : Set α} : (∀ x, x ∈ s) → s = univ :=
  eq_univ_iff_forall.2
#align set.eq_univ_of_forall Set.eq_univ_of_forall
-/

#print Set.Nonempty.eq_univ /-
theorem Nonempty.eq_univ [Subsingleton α] : s.Nonempty → s = univ :=
  by
  rintro ⟨x, hx⟩
  refine' eq_univ_of_forall fun y => by rwa [Subsingleton.elim y x]
#align set.nonempty.eq_univ Set.Nonempty.eq_univ
-/

#print Set.eq_univ_of_subset /-
theorem eq_univ_of_subset {s t : Set α} (h : s ⊆ t) (hs : s = univ) : t = univ :=
  eq_univ_of_univ_subset <| hs ▸ h
#align set.eq_univ_of_subset Set.eq_univ_of_subset
-/

#print Set.exists_mem_of_nonempty /-
theorem exists_mem_of_nonempty (α) : ∀ [Nonempty α], ∃ x : α, x ∈ (univ : Set α)
  | ⟨x⟩ => ⟨x, trivial⟩
#align set.exists_mem_of_nonempty Set.exists_mem_of_nonempty
-/

#print Set.ne_univ_iff_exists_not_mem /-
theorem ne_univ_iff_exists_not_mem {α : Type _} (s : Set α) : s ≠ univ ↔ ∃ a, a ∉ s := by
  rw [← not_forall, ← eq_univ_iff_forall]
#align set.ne_univ_iff_exists_not_mem Set.ne_univ_iff_exists_not_mem
-/

#print Set.not_subset_iff_exists_mem_not_mem /-
theorem not_subset_iff_exists_mem_not_mem {α : Type _} {s t : Set α} :
    ¬s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t := by simp [subset_def]
#align set.not_subset_iff_exists_mem_not_mem Set.not_subset_iff_exists_mem_not_mem
-/

#print Set.univ_unique /-
theorem univ_unique [Unique α] : @Set.univ α = {default} :=
  Set.ext fun x => iff_of_true trivial <| Subsingleton.elim x default
#align set.univ_unique Set.univ_unique
-/

/- warning: set.ssubset_univ_iff -> Set.ssubset_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s (Set.univ.{u1} α)) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Set.univ.{u1} α)) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.ssubset_univ_iff Set.ssubset_univ_iffₓ'. -/
theorem ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ :=
  lt_top_iff_ne_top
#align set.ssubset_univ_iff Set.ssubset_univ_iff

#print Set.nontrivial_of_nonempty /-
instance nontrivial_of_nonempty [Nonempty α] : Nontrivial (Set α) :=
  ⟨⟨∅, univ, empty_ne_univ⟩⟩
#align set.nontrivial_of_nonempty Set.nontrivial_of_nonempty
-/

/-! ### Lemmas about union -/


/- warning: set.union_def -> Set.union_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (setOf.{u1} α (fun (a : α) => Or (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s₁) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s₂)))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) (setOf.{u1} α (fun (a : α) => Or (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s₁) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s₂)))
Case conversion may be inaccurate. Consider using '#align set.union_def Set.union_defₓ'. -/
theorem union_def {s₁ s₂ : Set α} : s₁ ∪ s₂ = { a | a ∈ s₁ ∨ a ∈ s₂ } :=
  rfl
#align set.union_def Set.union_def

/- warning: set.mem_union_left -> Set.mem_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} (b : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} (b : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b))
Case conversion may be inaccurate. Consider using '#align set.mem_union_left Set.mem_union_leftₓ'. -/
theorem mem_union_left {x : α} {a : Set α} (b : Set α) : x ∈ a → x ∈ a ∪ b :=
  Or.inl
#align set.mem_union_left Set.mem_union_left

/- warning: set.mem_union_right -> Set.mem_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {b : Set.{u1} α} (a : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {b : Set.{u1} α} (a : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b))
Case conversion may be inaccurate. Consider using '#align set.mem_union_right Set.mem_union_rightₓ'. -/
theorem mem_union_right {x : α} {b : Set α} (a : Set α) : x ∈ b → x ∈ a ∪ b :=
  Or.inr
#align set.mem_union_right Set.mem_union_right

/- warning: set.mem_or_mem_of_mem_union -> Set.mem_or_mem_of_mem_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b)) -> (Or (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b)) -> (Or (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b))
Case conversion may be inaccurate. Consider using '#align set.mem_or_mem_of_mem_union Set.mem_or_mem_of_mem_unionₓ'. -/
theorem mem_or_mem_of_mem_union {x : α} {a b : Set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b :=
  H
#align set.mem_or_mem_of_mem_union Set.mem_or_mem_of_mem_union

/- warning: set.mem_union.elim -> Set.MemUnion.elim is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α} {P : Prop}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b)) -> ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) -> P) -> ((Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b) -> P) -> P
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α} {P : Prop}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b)) -> ((Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) -> P) -> ((Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b) -> P) -> P
Case conversion may be inaccurate. Consider using '#align set.mem_union.elim Set.MemUnion.elimₓ'. -/
theorem MemUnion.elim {x : α} {a b : Set α} {P : Prop} (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P)
    (H₃ : x ∈ b → P) : P :=
  Or.elim H₁ H₂ H₃
#align set.mem_union.elim Set.MemUnion.elim

/- warning: set.mem_union -> Set.mem_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (a : Set.{u1} α) (b : Set.{u1} α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b)) (Or (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (a : Set.{u1} α) (b : Set.{u1} α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b)) (Or (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b))
Case conversion may be inaccurate. Consider using '#align set.mem_union Set.mem_unionₓ'. -/
@[simp]
theorem mem_union (x : α) (a b : Set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b :=
  Iff.rfl
#align set.mem_union Set.mem_union

/- warning: set.union_self -> Set.union_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a a) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a a) a
Case conversion may be inaccurate. Consider using '#align set.union_self Set.union_selfₓ'. -/
@[simp]
theorem union_self (a : Set α) : a ∪ a = a :=
  ext fun x => or_self_iff _
#align set.union_self Set.union_self

/- warning: set.union_empty -> Set.union_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) a
Case conversion may be inaccurate. Consider using '#align set.union_empty Set.union_emptyₓ'. -/
@[simp]
theorem union_empty (a : Set α) : a ∪ ∅ = a :=
  ext fun x => or_false_iff _
#align set.union_empty Set.union_empty

/- warning: set.empty_union -> Set.empty_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) a) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) a) a
Case conversion may be inaccurate. Consider using '#align set.empty_union Set.empty_unionₓ'. -/
@[simp]
theorem empty_union (a : Set α) : ∅ ∪ a = a :=
  ext fun x => false_or_iff _
#align set.empty_union Set.empty_union

/- warning: set.union_comm -> Set.union_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) b a)
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) b a)
Case conversion may be inaccurate. Consider using '#align set.union_comm Set.union_commₓ'. -/
theorem union_comm (a b : Set α) : a ∪ b = b ∪ a :=
  ext fun x => or_comm
#align set.union_comm Set.union_comm

/- warning: set.union_assoc -> Set.union_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a b) c) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) b c))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a b) c) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) b c))
Case conversion may be inaccurate. Consider using '#align set.union_assoc Set.union_assocₓ'. -/
theorem union_assoc (a b c : Set α) : a ∪ b ∪ c = a ∪ (b ∪ c) :=
  ext fun x => or_assoc
#align set.union_assoc Set.union_assoc

/- warning: set.union_is_assoc -> Set.union_isAssoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, IsAssociative.{u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, IsAssociative.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Data.Set.Basic._hyg.8002 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.8004 : Set.{u1} α) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.8002 x._@.Mathlib.Data.Set.Basic._hyg.8004)
Case conversion may be inaccurate. Consider using '#align set.union_is_assoc Set.union_isAssocₓ'. -/
instance union_isAssoc : IsAssociative (Set α) (· ∪ ·) :=
  ⟨union_assoc⟩
#align set.union_is_assoc Set.union_isAssoc

/- warning: set.union_is_comm -> Set.union_isComm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, IsCommutative.{u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, IsCommutative.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Data.Set.Basic._hyg.8047 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.8049 : Set.{u1} α) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.8047 x._@.Mathlib.Data.Set.Basic._hyg.8049)
Case conversion may be inaccurate. Consider using '#align set.union_is_comm Set.union_isCommₓ'. -/
instance union_isComm : IsCommutative (Set α) (· ∪ ·) :=
  ⟨union_comm⟩
#align set.union_is_comm Set.union_isComm

/- warning: set.union_left_comm -> Set.union_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₂ s₃)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₂ (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₃))
but is expected to have type
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₂ s₃)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₂ (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₃))
Case conversion may be inaccurate. Consider using '#align set.union_left_comm Set.union_left_commₓ'. -/
theorem union_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
  ext fun x => or_left_comm
#align set.union_left_comm Set.union_left_comm

/- warning: set.union_right_comm -> Set.union_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) s₃) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₃) s₂)
but is expected to have type
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) s₃) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₃) s₂)
Case conversion may be inaccurate. Consider using '#align set.union_right_comm Set.union_right_commₓ'. -/
theorem union_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ s₃ ∪ s₂ :=
  ext fun x => or_right_comm
#align set.union_right_comm Set.union_right_comm

/- warning: set.union_eq_left_iff_subset -> Set.union_eq_left_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.union_eq_left_iff_subset Set.union_eq_left_iff_subsetₓ'. -/
@[simp]
theorem union_eq_left_iff_subset {s t : Set α} : s ∪ t = s ↔ t ⊆ s :=
  sup_eq_left
#align set.union_eq_left_iff_subset Set.union_eq_left_iff_subset

/- warning: set.union_eq_right_iff_subset -> Set.union_eq_right_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.union_eq_right_iff_subset Set.union_eq_right_iff_subsetₓ'. -/
@[simp]
theorem union_eq_right_iff_subset {s t : Set α} : s ∪ t = t ↔ s ⊆ t :=
  sup_eq_right
#align set.union_eq_right_iff_subset Set.union_eq_right_iff_subset

/- warning: set.union_eq_self_of_subset_left -> Set.union_eq_self_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t)
Case conversion may be inaccurate. Consider using '#align set.union_eq_self_of_subset_left Set.union_eq_self_of_subset_leftₓ'. -/
theorem union_eq_self_of_subset_left {s t : Set α} (h : s ⊆ t) : s ∪ t = t :=
  union_eq_right_iff_subset.mpr h
#align set.union_eq_self_of_subset_left Set.union_eq_self_of_subset_left

/- warning: set.union_eq_self_of_subset_right -> Set.union_eq_self_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align set.union_eq_self_of_subset_right Set.union_eq_self_of_subset_rightₓ'. -/
theorem union_eq_self_of_subset_right {s t : Set α} (h : t ⊆ s) : s ∪ t = s :=
  union_eq_left_iff_subset.mpr h
#align set.union_eq_self_of_subset_right Set.union_eq_self_of_subset_right

/- warning: set.subset_union_left -> Set.subset_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.subset_union_left Set.subset_union_leftₓ'. -/
@[simp]
theorem subset_union_left (s t : Set α) : s ⊆ s ∪ t := fun x => Or.inl
#align set.subset_union_left Set.subset_union_left

/- warning: set.subset_union_right -> Set.subset_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.subset_union_right Set.subset_union_rightₓ'. -/
@[simp]
theorem subset_union_right (s t : Set α) : t ⊆ s ∪ t := fun x => Or.inr
#align set.subset_union_right Set.subset_union_right

/- warning: set.union_subset -> Set.union_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) r)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t r) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) r)
Case conversion may be inaccurate. Consider using '#align set.union_subset Set.union_subsetₓ'. -/
theorem union_subset {s t r : Set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r := fun x =>
  Or.ndrec (@sr _) (@tr _)
#align set.union_subset Set.union_subset

/- warning: set.union_subset_iff -> Set.union_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_subset_iff Set.union_subset_iffₓ'. -/
@[simp]
theorem union_subset_iff {s t u : Set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
  (forall_congr' fun x => or_imp).trans forall_and
#align set.union_subset_iff Set.union_subset_iff

/- warning: set.union_subset_union -> Set.union_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₁ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ t₁) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₂ t₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t₁ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ t₁) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.union_subset_union Set.union_subset_unionₓ'. -/
theorem union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) :
    s₁ ∪ t₁ ⊆ s₂ ∪ t₂ := fun x => Or.imp (@h₁ _) (@h₂ _)
#align set.union_subset_union Set.union_subset_union

/- warning: set.union_subset_union_left -> Set.union_subset_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} (t : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} (t : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_subset_union_left Set.union_subset_union_leftₓ'. -/
theorem union_subset_union_left {s₁ s₂ : Set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
  union_subset_union h Subset.rfl
#align set.union_subset_union_left Set.union_subset_union_left

/- warning: set.union_subset_union_right -> Set.union_subset_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₁ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t₁) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t₂))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t₁ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t₁) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t₂))
Case conversion may be inaccurate. Consider using '#align set.union_subset_union_right Set.union_subset_union_rightₓ'. -/
theorem union_subset_union_right (s) {t₁ t₂ : Set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
  union_subset_union Subset.rfl h
#align set.union_subset_union_right Set.union_subset_union_right

/- warning: set.subset_union_of_subset_left -> Set.subset_union_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (forall (u : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.subset_union_of_subset_left Set.subset_union_of_subset_leftₓ'. -/
theorem subset_union_of_subset_left {s t : Set α} (h : s ⊆ t) (u : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_left t u)
#align set.subset_union_of_subset_left Set.subset_union_of_subset_left

/- warning: set.subset_union_of_subset_right -> Set.subset_union_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s u) -> (forall (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s u) -> (forall (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.subset_union_of_subset_right Set.subset_union_of_subset_rightₓ'. -/
theorem subset_union_of_subset_right {s u : Set α} (h : s ⊆ u) (t : Set α) : s ⊆ t ∪ u :=
  Subset.trans h (subset_union_right t u)
#align set.subset_union_of_subset_right Set.subset_union_of_subset_right

/- warning: set.union_congr_left -> Set.union_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (HasSup.sup.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) s u))
Case conversion may be inaccurate. Consider using '#align set.union_congr_left Set.union_congr_leftₓ'. -/
theorem union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u :=
  sup_congr_left ht hu
#align set.union_congr_left Set.union_congr_left

/- warning: set.union_congr_right -> Set.union_congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u)) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u)) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_congr_right Set.union_congr_rightₓ'. -/
theorem union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u :=
  sup_congr_right hs ht
#align set.union_congr_right Set.union_congr_right

/- warning: set.union_eq_union_iff_left -> Set.union_eq_union_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align set.union_eq_union_iff_left Set.union_eq_union_iff_leftₓ'. -/
theorem union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t :=
  sup_eq_sup_iff_left
#align set.union_eq_union_iff_left Set.union_eq_union_iff_left

/- warning: set.union_eq_union_iff_right -> Set.union_eq_union_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u)))
Case conversion may be inaccurate. Consider using '#align set.union_eq_union_iff_right Set.union_eq_union_iff_rightₓ'. -/
theorem union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u :=
  sup_eq_sup_iff_right
#align set.union_eq_union_iff_right Set.union_eq_union_iff_right

/- warning: set.union_empty_iff -> Set.union_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (And (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u1} (Set.{u1} α) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (And (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))
Case conversion may be inaccurate. Consider using '#align set.union_empty_iff Set.union_empty_iffₓ'. -/
@[simp]
theorem union_empty_iff {s t : Set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ := by
  simp only [← subset_empty_iff] <;> exact union_subset_iff
#align set.union_empty_iff Set.union_empty_iff

/- warning: set.union_univ -> Set.union_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Set.univ.{u1} α)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Set.univ.{u1} α)) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.union_univ Set.union_univₓ'. -/
@[simp]
theorem union_univ {s : Set α} : s ∪ univ = univ :=
  sup_top_eq
#align set.union_univ Set.union_univ

/- warning: set.univ_union -> Set.univ_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.univ.{u1} α) s) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.univ.{u1} α) s) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.univ_union Set.univ_unionₓ'. -/
@[simp]
theorem univ_union {s : Set α} : univ ∪ s = univ :=
  top_sup_eq
#align set.univ_union Set.univ_union

/-! ### Lemmas about intersection -/


/- warning: set.inter_def -> Set.inter_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (setOf.{u1} α (fun (a : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s₁) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s₂)))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (setOf.{u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s₁) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s₂)))
Case conversion may be inaccurate. Consider using '#align set.inter_def Set.inter_defₓ'. -/
theorem inter_def {s₁ s₂ : Set α} : s₁ ∩ s₂ = { a | a ∈ s₁ ∧ a ∈ s₂ } :=
  rfl
#align set.inter_def Set.inter_def

/- warning: set.mem_inter_iff -> Set.mem_inter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (a : Set.{u1} α) (b : Set.{u1} α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (a : Set.{u1} α) (b : Set.{u1} α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b)) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b))
Case conversion may be inaccurate. Consider using '#align set.mem_inter_iff Set.mem_inter_iffₓ'. -/
@[simp]
theorem mem_inter_iff (x : α) (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b :=
  Iff.rfl
#align set.mem_inter_iff Set.mem_inter_iff

/- warning: set.mem_inter -> Set.mem_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b))
Case conversion may be inaccurate. Consider using '#align set.mem_inter Set.mem_interₓ'. -/
theorem mem_inter {x : α} {a b : Set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
  ⟨ha, hb⟩
#align set.mem_inter Set.mem_inter

/- warning: set.mem_of_mem_inter_left -> Set.mem_of_mem_inter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x a)
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x a)
Case conversion may be inaccurate. Consider using '#align set.mem_of_mem_inter_left Set.mem_of_mem_inter_leftₓ'. -/
theorem mem_of_mem_inter_left {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ a :=
  h.left
#align set.mem_of_mem_inter_left Set.mem_of_mem_inter_left

/- warning: set.mem_of_mem_inter_right -> Set.mem_of_mem_inter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x b)
but is expected to have type
  forall {α : Type.{u1}} {x : α} {a : Set.{u1} α} {b : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x b)
Case conversion may be inaccurate. Consider using '#align set.mem_of_mem_inter_right Set.mem_of_mem_inter_rightₓ'. -/
theorem mem_of_mem_inter_right {x : α} {a b : Set α} (h : x ∈ a ∩ b) : x ∈ b :=
  h.right
#align set.mem_of_mem_inter_right Set.mem_of_mem_inter_right

/- warning: set.inter_self -> Set.inter_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a a) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a a) a
Case conversion may be inaccurate. Consider using '#align set.inter_self Set.inter_selfₓ'. -/
@[simp]
theorem inter_self (a : Set α) : a ∩ a = a :=
  ext fun x => and_self_iff _
#align set.inter_self Set.inter_self

/- warning: set.inter_empty -> Set.inter_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.inter_empty Set.inter_emptyₓ'. -/
@[simp]
theorem inter_empty (a : Set α) : a ∩ ∅ = ∅ :=
  ext fun x => and_false_iff _
#align set.inter_empty Set.inter_empty

/- warning: set.empty_inter -> Set.empty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) a) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) a) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.empty_inter Set.empty_interₓ'. -/
@[simp]
theorem empty_inter (a : Set α) : ∅ ∩ a = ∅ :=
  ext fun x => false_and_iff _
#align set.empty_inter Set.empty_inter

/- warning: set.inter_comm -> Set.inter_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) b a)
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) b a)
Case conversion may be inaccurate. Consider using '#align set.inter_comm Set.inter_commₓ'. -/
theorem inter_comm (a b : Set α) : a ∩ b = b ∩ a :=
  ext fun x => and_comm
#align set.inter_comm Set.inter_comm

/- warning: set.inter_assoc -> Set.inter_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b) c) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) b c))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b) c) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) b c))
Case conversion may be inaccurate. Consider using '#align set.inter_assoc Set.inter_assocₓ'. -/
theorem inter_assoc (a b c : Set α) : a ∩ b ∩ c = a ∩ (b ∩ c) :=
  ext fun x => and_assoc
#align set.inter_assoc Set.inter_assoc

/- warning: set.inter_is_assoc -> Set.inter_isAssoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, IsAssociative.{u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, IsAssociative.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Data.Set.Basic._hyg.9710 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.9712 : Set.{u1} α) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.9710 x._@.Mathlib.Data.Set.Basic._hyg.9712)
Case conversion may be inaccurate. Consider using '#align set.inter_is_assoc Set.inter_isAssocₓ'. -/
instance inter_isAssoc : IsAssociative (Set α) (· ∩ ·) :=
  ⟨inter_assoc⟩
#align set.inter_is_assoc Set.inter_isAssoc

/- warning: set.inter_is_comm -> Set.inter_isComm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, IsCommutative.{u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, IsCommutative.{u1} (Set.{u1} α) (fun (x._@.Mathlib.Data.Set.Basic._hyg.9755 : Set.{u1} α) (x._@.Mathlib.Data.Set.Basic._hyg.9757 : Set.{u1} α) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) x._@.Mathlib.Data.Set.Basic._hyg.9755 x._@.Mathlib.Data.Set.Basic._hyg.9757)
Case conversion may be inaccurate. Consider using '#align set.inter_is_comm Set.inter_isCommₓ'. -/
instance inter_isComm : IsCommutative (Set α) (· ∩ ·) :=
  ⟨inter_comm⟩
#align set.inter_is_comm Set.inter_isComm

/- warning: set.inter_left_comm -> Set.inter_left_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ s₃)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₃))
but is expected to have type
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₂ s₃)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₂ (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₃))
Case conversion may be inaccurate. Consider using '#align set.inter_left_comm Set.inter_left_commₓ'. -/
theorem inter_left_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
  ext fun x => and_left_comm
#align set.inter_left_comm Set.inter_left_comm

/- warning: set.inter_right_comm -> Set.inter_right_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) s₃) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₃) s₂)
but is expected to have type
  forall {α : Type.{u1}} (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₃ : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) s₃) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₃) s₂)
Case conversion may be inaccurate. Consider using '#align set.inter_right_comm Set.inter_right_commₓ'. -/
theorem inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ ∩ s₂ ∩ s₃ = s₁ ∩ s₃ ∩ s₂ :=
  ext fun x => and_right_comm
#align set.inter_right_comm Set.inter_right_comm

/- warning: set.inter_subset_left -> Set.inter_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) s
Case conversion may be inaccurate. Consider using '#align set.inter_subset_left Set.inter_subset_leftₓ'. -/
@[simp]
theorem inter_subset_left (s t : Set α) : s ∩ t ⊆ s := fun x => And.left
#align set.inter_subset_left Set.inter_subset_left

/- warning: set.inter_subset_right -> Set.inter_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) t
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) t
Case conversion may be inaccurate. Consider using '#align set.inter_subset_right Set.inter_subset_rightₓ'. -/
@[simp]
theorem inter_subset_right (s t : Set α) : s ∩ t ⊆ t := fun x => And.right
#align set.inter_subset_right Set.inter_subset_right

/- warning: set.subset_inter -> Set.subset_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.subset_inter Set.subset_interₓ'. -/
theorem subset_inter {s t r : Set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t := fun x h =>
  ⟨rs h, rt h⟩
#align set.subset_inter Set.subset_inter

/- warning: set.subset_inter_iff -> Set.subset_inter_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) r t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {r : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) r t))
Case conversion may be inaccurate. Consider using '#align set.subset_inter_iff Set.subset_inter_iffₓ'. -/
@[simp]
theorem subset_inter_iff {s t r : Set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
  (forall_congr' fun x => imp_and).trans forall_and
#align set.subset_inter_iff Set.subset_inter_iff

/- warning: set.inter_eq_left_iff_subset -> Set.inter_eq_left_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.inter_eq_left_iff_subset Set.inter_eq_left_iff_subsetₓ'. -/
@[simp]
theorem inter_eq_left_iff_subset {s t : Set α} : s ∩ t = s ↔ s ⊆ t :=
  inf_eq_left
#align set.inter_eq_left_iff_subset Set.inter_eq_left_iff_subset

/- warning: set.inter_eq_right_iff_subset -> Set.inter_eq_right_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.inter_eq_right_iff_subset Set.inter_eq_right_iff_subsetₓ'. -/
@[simp]
theorem inter_eq_right_iff_subset {s t : Set α} : s ∩ t = t ↔ t ⊆ s :=
  inf_eq_right
#align set.inter_eq_right_iff_subset Set.inter_eq_right_iff_subset

/- warning: set.inter_eq_self_of_subset_left -> Set.inter_eq_self_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) s)
Case conversion may be inaccurate. Consider using '#align set.inter_eq_self_of_subset_left Set.inter_eq_self_of_subset_leftₓ'. -/
theorem inter_eq_self_of_subset_left {s t : Set α} : s ⊆ t → s ∩ t = s :=
  inter_eq_left_iff_subset.mpr
#align set.inter_eq_self_of_subset_left Set.inter_eq_self_of_subset_left

/- warning: set.inter_eq_self_of_subset_right -> Set.inter_eq_self_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) t)
Case conversion may be inaccurate. Consider using '#align set.inter_eq_self_of_subset_right Set.inter_eq_self_of_subset_rightₓ'. -/
theorem inter_eq_self_of_subset_right {s t : Set α} : t ⊆ s → s ∩ t = t :=
  inter_eq_right_iff_subset.mpr
#align set.inter_eq_self_of_subset_right Set.inter_eq_self_of_subset_right

/- warning: set.inter_congr_left -> Set.inter_congr_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.inter_congr_left Set.inter_congr_leftₓ'. -/
theorem inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u :=
  inf_congr_left ht hu
#align set.inter_congr_left Set.inter_congr_left

/- warning: set.inter_congr_right -> Set.inter_congr_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u) s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_congr_right Set.inter_congr_rightₓ'. -/
theorem inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u :=
  inf_congr_right hs ht
#align set.inter_congr_right Set.inter_congr_right

/- warning: set.inter_eq_inter_iff_left -> Set.inter_eq_inter_iff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u))
Case conversion may be inaccurate. Consider using '#align set.inter_eq_inter_iff_left Set.inter_eq_inter_iff_leftₓ'. -/
theorem inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u :=
  inf_eq_inf_iff_left
#align set.inter_eq_inter_iff_left Set.inter_eq_inter_iff_left

/- warning: set.inter_eq_inter_iff_right -> Set.inter_eq_inter_iff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t))
Case conversion may be inaccurate. Consider using '#align set.inter_eq_inter_iff_right Set.inter_eq_inter_iff_rightₓ'. -/
theorem inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t :=
  inf_eq_inf_iff_right
#align set.inter_eq_inter_iff_right Set.inter_eq_inter_iff_right

/- warning: set.inter_univ -> Set.inter_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a (Set.univ.{u1} α)) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a (Set.univ.{u1} α)) a
Case conversion may be inaccurate. Consider using '#align set.inter_univ Set.inter_univₓ'. -/
@[simp]
theorem inter_univ (a : Set α) : a ∩ univ = a :=
  inf_top_eq
#align set.inter_univ Set.inter_univ

/- warning: set.univ_inter -> Set.univ_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.univ.{u1} α) a) a
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.univ.{u1} α) a) a
Case conversion may be inaccurate. Consider using '#align set.univ_inter Set.univ_interₓ'. -/
@[simp]
theorem univ_inter (a : Set α) : univ ∩ a = a :=
  top_inf_eq
#align set.univ_inter Set.univ_inter

/- warning: set.inter_subset_inter -> Set.inter_subset_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₂ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t₁ t₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₂ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t₁ t₂))
Case conversion may be inaccurate. Consider using '#align set.inter_subset_inter Set.inter_subset_interₓ'. -/
theorem inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) :
    s₁ ∩ s₂ ⊆ t₁ ∩ t₂ := fun x => And.imp (@h₁ _) (@h₂ _)
#align set.inter_subset_inter Set.inter_subset_inter

/- warning: set.inter_subset_inter_left -> Set.inter_subset_inter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_subset_inter_left Set.inter_subset_inter_leftₓ'. -/
theorem inter_subset_inter_left {s t : Set α} (u : Set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  inter_subset_inter H Subset.rfl
#align set.inter_subset_inter_left Set.inter_subset_inter_left

/- warning: set.inter_subset_inter_right -> Set.inter_subset_inter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u t))
Case conversion may be inaccurate. Consider using '#align set.inter_subset_inter_right Set.inter_subset_inter_rightₓ'. -/
theorem inter_subset_inter_right {s t : Set α} (u : Set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
  inter_subset_inter Subset.rfl H
#align set.inter_subset_inter_right Set.inter_subset_inter_right

/- warning: set.union_inter_cancel_left -> Set.union_inter_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s) s
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s) s
Case conversion may be inaccurate. Consider using '#align set.union_inter_cancel_left Set.union_inter_cancel_leftₓ'. -/
theorem union_inter_cancel_left {s t : Set α} : (s ∪ t) ∩ s = s :=
  inter_eq_self_of_subset_right <| subset_union_left _ _
#align set.union_inter_cancel_left Set.union_inter_cancel_left

/- warning: set.union_inter_cancel_right -> Set.union_inter_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t) t
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t) t
Case conversion may be inaccurate. Consider using '#align set.union_inter_cancel_right Set.union_inter_cancel_rightₓ'. -/
theorem union_inter_cancel_right {s t : Set α} : (s ∪ t) ∩ t = t :=
  inter_eq_self_of_subset_right <| subset_union_right _ _
#align set.union_inter_cancel_right Set.union_inter_cancel_right

/-! ### Distributivity laws -/


/- warning: set.inter_distrib_left -> Set.inter_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.inter_distrib_left Set.inter_distrib_leftₓ'. -/
theorem inter_distrib_left (s t u : Set α) : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align set.inter_distrib_left Set.inter_distrib_left

/- warning: set.inter_union_distrib_left -> Set.inter_union_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.inter_union_distrib_left Set.inter_union_distrib_leftₓ'. -/
theorem inter_union_distrib_left {s t u : Set α} : s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u :=
  inf_sup_left
#align set.inter_union_distrib_left Set.inter_union_distrib_left

/- warning: set.inter_distrib_right -> Set.inter_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_distrib_right Set.inter_distrib_rightₓ'. -/
theorem inter_distrib_right (s t u : Set α) : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align set.inter_distrib_right Set.inter_distrib_right

/- warning: set.union_inter_distrib_right -> Set.union_inter_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_inter_distrib_right Set.union_inter_distrib_rightₓ'. -/
theorem union_inter_distrib_right {s t u : Set α} : (s ∪ t) ∩ u = s ∩ u ∪ t ∩ u :=
  inf_sup_right
#align set.union_inter_distrib_right Set.union_inter_distrib_right

/- warning: set.union_distrib_left -> Set.union_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_left Set.union_distrib_leftₓ'. -/
theorem union_distrib_left (s t u : Set α) : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align set.union_distrib_left Set.union_distrib_left

/- warning: set.union_inter_distrib_left -> Set.union_inter_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.union_inter_distrib_left Set.union_inter_distrib_leftₓ'. -/
theorem union_inter_distrib_left {s t u : Set α} : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) :=
  sup_inf_left
#align set.union_inter_distrib_left Set.union_inter_distrib_left

/- warning: set.union_distrib_right -> Set.union_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_distrib_right Set.union_distrib_rightₓ'. -/
theorem union_distrib_right (s t u : Set α) : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align set.union_distrib_right Set.union_distrib_right

/- warning: set.inter_union_distrib_right -> Set.inter_union_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_union_distrib_right Set.inter_union_distrib_rightₓ'. -/
theorem inter_union_distrib_right {s t u : Set α} : s ∩ t ∪ u = (s ∪ u) ∩ (t ∪ u) :=
  sup_inf_right
#align set.inter_union_distrib_right Set.inter_union_distrib_right

/- warning: set.union_union_distrib_left -> Set.union_union_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.union_union_distrib_left Set.union_union_distrib_leftₓ'. -/
theorem union_union_distrib_left (s t u : Set α) : s ∪ (t ∪ u) = s ∪ t ∪ (s ∪ u) :=
  sup_sup_distrib_left _ _ _
#align set.union_union_distrib_left Set.union_union_distrib_left

/- warning: set.union_union_distrib_right -> Set.union_union_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_union_distrib_right Set.union_union_distrib_rightₓ'. -/
theorem union_union_distrib_right (s t u : Set α) : s ∪ t ∪ u = s ∪ u ∪ (t ∪ u) :=
  sup_sup_distrib_right _ _ _
#align set.union_union_distrib_right Set.union_union_distrib_right

/- warning: set.inter_inter_distrib_left -> Set.inter_inter_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.inter_inter_distrib_left Set.inter_inter_distrib_leftₓ'. -/
theorem inter_inter_distrib_left (s t u : Set α) : s ∩ (t ∩ u) = s ∩ t ∩ (s ∩ u) :=
  inf_inf_distrib_left _ _ _
#align set.inter_inter_distrib_left Set.inter_inter_distrib_left

/- warning: set.inter_inter_distrib_right -> Set.inter_inter_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_inter_distrib_right Set.inter_inter_distrib_rightₓ'. -/
theorem inter_inter_distrib_right (s t u : Set α) : s ∩ t ∩ u = s ∩ u ∩ (t ∩ u) :=
  inf_inf_distrib_right _ _ _
#align set.inter_inter_distrib_right Set.inter_inter_distrib_right

/- warning: set.union_union_union_comm -> Set.union_union_union_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α) (v : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) u v)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t v))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α) (v : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) u v)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t v))
Case conversion may be inaccurate. Consider using '#align set.union_union_union_comm Set.union_union_union_commₓ'. -/
theorem union_union_union_comm (s t u v : Set α) : s ∪ t ∪ (u ∪ v) = s ∪ u ∪ (t ∪ v) :=
  sup_sup_sup_comm _ _ _ _
#align set.union_union_union_comm Set.union_union_union_comm

/- warning: set.inter_inter_inter_comm -> Set.inter_inter_inter_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α) (v : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u v)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t v))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α) (v : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u v)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t v))
Case conversion may be inaccurate. Consider using '#align set.inter_inter_inter_comm Set.inter_inter_inter_commₓ'. -/
theorem inter_inter_inter_comm (s t u v : Set α) : s ∩ t ∩ (u ∩ v) = s ∩ u ∩ (t ∩ v) :=
  inf_inf_inf_comm _ _ _ _
#align set.inter_inter_inter_comm Set.inter_inter_inter_comm

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/


#print Set.insert_def /-
theorem insert_def (x : α) (s : Set α) : insert x s = { y | y = x ∨ y ∈ s } :=
  rfl
#align set.insert_def Set.insert_def
-/

#print Set.subset_insert /-
@[simp]
theorem subset_insert (x : α) (s : Set α) : s ⊆ insert x s := fun y => Or.inr
#align set.subset_insert Set.subset_insert
-/

#print Set.mem_insert /-
theorem mem_insert (x : α) (s : Set α) : x ∈ insert x s :=
  Or.inl rfl
#align set.mem_insert Set.mem_insert
-/

#print Set.mem_insert_of_mem /-
theorem mem_insert_of_mem {x : α} {s : Set α} (y : α) : x ∈ s → x ∈ insert y s :=
  Or.inr
#align set.mem_insert_of_mem Set.mem_insert_of_mem
-/

#print Set.eq_or_mem_of_mem_insert /-
theorem eq_or_mem_of_mem_insert {x a : α} {s : Set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
  id
#align set.eq_or_mem_of_mem_insert Set.eq_or_mem_of_mem_insert
-/

#print Set.mem_of_mem_insert_of_ne /-
theorem mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s :=
  Or.resolve_left
#align set.mem_of_mem_insert_of_ne Set.mem_of_mem_insert_of_ne
-/

#print Set.eq_of_not_mem_of_mem_insert /-
theorem eq_of_not_mem_of_mem_insert : b ∈ insert a s → b ∉ s → b = a :=
  Or.resolve_right
#align set.eq_of_not_mem_of_mem_insert Set.eq_of_not_mem_of_mem_insert
-/

#print Set.mem_insert_iff /-
@[simp]
theorem mem_insert_iff {x a : α} {s : Set α} : x ∈ insert a s ↔ x = a ∨ x ∈ s :=
  Iff.rfl
#align set.mem_insert_iff Set.mem_insert_iff
-/

#print Set.insert_eq_of_mem /-
@[simp]
theorem insert_eq_of_mem {a : α} {s : Set α} (h : a ∈ s) : insert a s = s :=
  ext fun x => or_iff_right_of_imp fun e => e.symm ▸ h
#align set.insert_eq_of_mem Set.insert_eq_of_mem
-/

#print Set.ne_insert_of_not_mem /-
theorem ne_insert_of_not_mem {s : Set α} (t : Set α) {a : α} : a ∉ s → s ≠ insert a t :=
  mt fun e => e.symm ▸ mem_insert _ _
#align set.ne_insert_of_not_mem Set.ne_insert_of_not_mem
-/

#print Set.insert_eq_self /-
@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert _ _, insert_eq_of_mem⟩
#align set.insert_eq_self Set.insert_eq_self
-/

#print Set.insert_ne_self /-
theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.Not
#align set.insert_ne_self Set.insert_ne_self
-/

#print Set.insert_subset /-
theorem insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_def, or_imp, forall_and, forall_eq, mem_insert_iff]
#align set.insert_subset Set.insert_subset
-/

#print Set.insert_subset_insert /-
theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := fun x => Or.imp_right (@h _)
#align set.insert_subset_insert Set.insert_subset_insert
-/

#print Set.insert_subset_insert_iff /-
theorem insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t :=
  by
  refine' ⟨fun h x hx => _, insert_subset_insert⟩
  rcases h (subset_insert _ _ hx) with (rfl | hxt)
  exacts[(ha hx).elim, hxt]
#align set.insert_subset_insert_iff Set.insert_subset_insert_iff
-/

/- warning: set.ssubset_iff_insert -> Set.ssubset_iff_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s t) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) (fun (H : Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s t) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) (fun (H : Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) => HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t)))
Case conversion may be inaccurate. Consider using '#align set.ssubset_iff_insert Set.ssubset_iff_insertₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a «expr ∉ » s) -/
theorem ssubset_iff_insert {s t : Set α} : s ⊂ t ↔ ∃ (a : _)(_ : a ∉ s), insert a s ⊆ t :=
  by
  simp only [insert_subset, exists_and_right, ssubset_def, not_subset]
  simp only [exists_prop, and_comm']
#align set.ssubset_iff_insert Set.ssubset_iff_insert

/- warning: set.ssubset_insert -> Set.ssubset_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {a : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.ssubset_insert Set.ssubset_insertₓ'. -/
theorem ssubset_insert {s : Set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff_insert.2 ⟨a, h, Subset.rfl⟩
#align set.ssubset_insert Set.ssubset_insert

#print Set.insert_comm /-
theorem insert_comm (a b : α) (s : Set α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => or_left_comm
#align set.insert_comm Set.insert_comm
-/

#print Set.insert_idem /-
@[simp]
theorem insert_idem (a : α) (s : Set α) : insert a (insert a s) = insert a s :=
  insert_eq_of_mem <| mem_insert _ _
#align set.insert_idem Set.insert_idem
-/

/- warning: set.insert_union -> Set.insert_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.insert_union Set.insert_unionₓ'. -/
theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
  ext fun x => or_assoc
#align set.insert_union Set.insert_union

/- warning: set.union_insert -> Set.union_insert is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a t)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a t)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.union_insert Set.union_insertₓ'. -/
@[simp]
theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
  ext fun x => or_left_comm
#align set.union_insert Set.union_insert

#print Set.insert_nonempty /-
@[simp]
theorem insert_nonempty (a : α) (s : Set α) : (insert a s).Nonempty :=
  ⟨a, mem_insert a s⟩
#align set.insert_nonempty Set.insert_nonempty
-/

instance (a : α) (s : Set α) : Nonempty (insert a s : Set α) :=
  (insert_nonempty a s).to_subtype

/- warning: set.insert_inter_distrib -> Set.insert_inter_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a t))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a t))
Case conversion may be inaccurate. Consider using '#align set.insert_inter_distrib Set.insert_inter_distribₓ'. -/
theorem insert_inter_distrib (a : α) (s t : Set α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
  ext fun y => or_and_left
#align set.insert_inter_distrib Set.insert_inter_distrib

/- warning: set.insert_union_distrib -> Set.insert_union_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a t))
but is expected to have type
  forall {α : Type.{u1}} (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a t))
Case conversion may be inaccurate. Consider using '#align set.insert_union_distrib Set.insert_union_distribₓ'. -/
theorem insert_union_distrib (a : α) (s t : Set α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
  ext fun _ => or_or_distrib_left _ _ _
#align set.insert_union_distrib Set.insert_union_distrib

#print Set.insert_inj /-
theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_not_mem_of_mem_insert (h.subst <| mem_insert a s) ha, congr_arg _⟩
#align set.insert_inj Set.insert_inj
-/

#print Set.forall_of_forall_insert /-
-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ insert a s → P x)
    (x) (h : x ∈ s) : P x :=
  H _ (Or.inr h)
#align set.forall_of_forall_insert Set.forall_of_forall_insert
-/

#print Set.forall_insert_of_forall /-
theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : Set α} (H : ∀ x, x ∈ s → P x) (ha : P a)
    (x) (h : x ∈ insert a s) : P x :=
  h.elim (fun e => e.symm ▸ ha) (H _)
#align set.forall_insert_of_forall Set.forall_insert_of_forall
-/

/- warning: set.bex_insert_iff -> Set.bex_insert_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop} {a : α} {s : Set.{u1} α}, Iff (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)) => P x))) (Or (P a) (Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => P x))))
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop} {a : α} {s : Set.{u1} α}, Iff (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)) (P x))) (Or (P a) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (P x))))
Case conversion may be inaccurate. Consider using '#align set.bex_insert_iff Set.bex_insert_iffₓ'. -/
theorem bex_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∃ x ∈ insert a s, P x) ↔ P a ∨ ∃ x ∈ s, P x :=
  bex_or_left.trans <| or_congr_left bex_eq_left
#align set.bex_insert_iff Set.bex_insert_iff

#print Set.ball_insert_iff /-
theorem ball_insert_iff {P : α → Prop} {a : α} {s : Set α} :
    (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
  ball_or_left.trans <| and_congr_left' forall_eq
#align set.ball_insert_iff Set.ball_insert_iff
-/

/-! ### Lemmas about singletons -/


#print Set.singleton_def /-
theorem singleton_def (a : α) : ({a} : Set α) = insert a ∅ :=
  (insert_emptyc_eq _).symm
#align set.singleton_def Set.singleton_def
-/

#print Set.mem_singleton_iff /-
@[simp]
theorem mem_singleton_iff {a b : α} : a ∈ ({b} : Set α) ↔ a = b :=
  Iff.rfl
#align set.mem_singleton_iff Set.mem_singleton_iff
-/

#print Set.setOf_eq_eq_singleton /-
@[simp]
theorem setOf_eq_eq_singleton {a : α} : { n | n = a } = {a} :=
  rfl
#align set.set_of_eq_eq_singleton Set.setOf_eq_eq_singleton
-/

#print Set.setOf_eq_eq_singleton' /-
@[simp]
theorem setOf_eq_eq_singleton' {a : α} : { x | a = x } = {a} :=
  ext fun x => eq_comm
#align set.set_of_eq_eq_singleton' Set.setOf_eq_eq_singleton'
-/

#print Set.mem_singleton /-
-- TODO: again, annotation needed
@[simp]
theorem mem_singleton (a : α) : a ∈ ({a} : Set α) :=
  @rfl _ _
#align set.mem_singleton Set.mem_singleton
-/

#print Set.eq_of_mem_singleton /-
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Set α)) : x = y :=
  h
#align set.eq_of_mem_singleton Set.eq_of_mem_singleton
-/

#print Set.singleton_eq_singleton_iff /-
@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : Set α) ↔ x = y :=
  ext_iff.trans eq_iff_eq_cancel_left
#align set.singleton_eq_singleton_iff Set.singleton_eq_singleton_iff
-/

#print Set.singleton_injective /-
theorem singleton_injective : Injective (singleton : α → Set α) := fun _ _ =>
  singleton_eq_singleton_iff.mp
#align set.singleton_injective Set.singleton_injective
-/

#print Set.mem_singleton_of_eq /-
theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : Set α) :=
  H
#align set.mem_singleton_of_eq Set.mem_singleton_of_eq
-/

/- warning: set.insert_eq -> Set.insert_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x) s)
but is expected to have type
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x s) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x) s)
Case conversion may be inaccurate. Consider using '#align set.insert_eq Set.insert_eqₓ'. -/
theorem insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α) ∪ s :=
  rfl
#align set.insert_eq Set.insert_eq

#print Set.singleton_nonempty /-
@[simp]
theorem singleton_nonempty (a : α) : ({a} : Set α).Nonempty :=
  ⟨a, rfl⟩
#align set.singleton_nonempty Set.singleton_nonempty
-/

#print Set.singleton_ne_empty /-
@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Set α) ≠ ∅ :=
  (singleton_nonempty _).ne_empty
#align set.singleton_ne_empty Set.singleton_ne_empty
-/

/- warning: set.empty_ssubset_singleton -> Set.empty_ssubset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α}, HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} {a : α}, HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align set.empty_ssubset_singleton Set.empty_ssubset_singletonₓ'. -/
@[simp]
theorem empty_ssubset_singleton : (∅ : Set α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset
#align set.empty_ssubset_singleton Set.empty_ssubset_singleton

#print Set.singleton_subset_iff /-
@[simp]
theorem singleton_subset_iff {a : α} {s : Set α} : {a} ⊆ s ↔ a ∈ s :=
  forall_eq
#align set.singleton_subset_iff Set.singleton_subset_iff
-/

#print Set.set_compr_eq_eq_singleton /-
theorem set_compr_eq_eq_singleton {a : α} : { b | b = a } = {a} :=
  rfl
#align set.set_compr_eq_eq_singleton Set.set_compr_eq_eq_singleton
-/

/- warning: set.singleton_union -> Set.singleton_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.singleton_union Set.singleton_unionₓ'. -/
@[simp]
theorem singleton_union : {a} ∪ s = insert a s :=
  rfl
#align set.singleton_union Set.singleton_union

/- warning: set.union_singleton -> Set.union_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.union_singleton Set.union_singletonₓ'. -/
@[simp]
theorem union_singleton : s ∪ {a} = insert a s :=
  union_comm _ _
#align set.union_singleton Set.union_singleton

/- warning: set.singleton_inter_nonempty -> Set.singleton_inter_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s)) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s)) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.singleton_inter_nonempty Set.singleton_inter_nonemptyₓ'. -/
@[simp]
theorem singleton_inter_nonempty : ({a} ∩ s).Nonempty ↔ a ∈ s := by
  simp only [Set.Nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]
#align set.singleton_inter_nonempty Set.singleton_inter_nonempty

/- warning: set.inter_singleton_nonempty -> Set.inter_singleton_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.inter_singleton_nonempty Set.inter_singleton_nonemptyₓ'. -/
@[simp]
theorem inter_singleton_nonempty : (s ∩ {a}).Nonempty ↔ a ∈ s := by
  rw [inter_comm, singleton_inter_nonempty]
#align set.inter_singleton_nonempty Set.inter_singleton_nonempty

/- warning: set.singleton_inter_eq_empty -> Set.singleton_inter_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.singleton_inter_eq_empty Set.singleton_inter_eq_emptyₓ'. -/
@[simp]
theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
  not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.Not
#align set.singleton_inter_eq_empty Set.singleton_inter_eq_empty

/- warning: set.inter_singleton_eq_empty -> Set.inter_singleton_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.inter_singleton_eq_empty Set.inter_singleton_eq_emptyₓ'. -/
@[simp]
theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s := by
  rw [inter_comm, singleton_inter_eq_empty]
#align set.inter_singleton_eq_empty Set.inter_singleton_eq_empty

#print Set.nmem_singleton_empty /-
theorem nmem_singleton_empty {s : Set α} : s ∉ ({∅} : Set (Set α)) ↔ s.Nonempty :=
  nonempty_iff_ne_empty.symm
#align set.nmem_singleton_empty Set.nmem_singleton_empty
-/

#print Set.uniqueSingleton /-
instance uniqueSingleton (a : α) : Unique ↥({a} : Set α) :=
  ⟨⟨⟨a, mem_singleton a⟩⟩, fun ⟨x, h⟩ => Subtype.eq h⟩
#align set.unique_singleton Set.uniqueSingleton
-/

#print Set.eq_singleton_iff_unique_mem /-
theorem eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
  Subset.antisymm_iff.trans <| and_comm.trans <| and_congr_left' singleton_subset_iff
#align set.eq_singleton_iff_unique_mem Set.eq_singleton_iff_unique_mem
-/

#print Set.eq_singleton_iff_nonempty_unique_mem /-
theorem eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a :=
  eq_singleton_iff_unique_mem.trans <|
    and_congr_left fun H => ⟨fun h' => ⟨_, h'⟩, fun ⟨x, h⟩ => H x h ▸ h⟩
#align set.eq_singleton_iff_nonempty_unique_mem Set.eq_singleton_iff_nonempty_unique_mem
-/

#print Set.default_coe_singleton /-
-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp]
theorem default_coe_singleton (x : α) : (default : ({x} : Set α)) = ⟨x, rfl⟩ :=
  rfl
#align set.default_coe_singleton Set.default_coe_singleton
-/

/-! ### Lemmas about pairs -/


#print Set.pair_eq_singleton /-
@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : Set α) = {a} :=
  union_self _
#align set.pair_eq_singleton Set.pair_eq_singleton
-/

#print Set.pair_comm /-
theorem pair_comm (a b : α) : ({a, b} : Set α) = {b, a} :=
  union_comm _ _
#align set.pair_comm Set.pair_comm
-/

#print Set.pair_eq_pair_iff /-
theorem pair_eq_pair_iff {x y z w : α} :
    ({x, y} : Set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
  by
  simp only [Set.Subset.antisymm_iff, Set.insert_subset, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.singleton_subset_iff]
  constructor
  · tauto
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp
#align set.pair_eq_pair_iff Set.pair_eq_pair_iff
-/

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/


section Sep

variable {p q : α → Prop} {x : α}

#print Set.mem_sep /-
theorem mem_sep (xs : x ∈ s) (px : p x) : x ∈ { x ∈ s | p x } :=
  ⟨xs, px⟩
#align set.mem_sep Set.mem_sep
-/

/- warning: set.sep_mem_eq -> Set.sep_mem_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.sep_mem_eq Set.sep_mem_eqₓ'. -/
@[simp]
theorem sep_mem_eq : { x ∈ s | x ∈ t } = s ∩ t :=
  rfl
#align set.sep_mem_eq Set.sep_mem_eq

#print Set.mem_sep_iff /-
@[simp]
theorem mem_sep_iff : x ∈ { x ∈ s | p x } ↔ x ∈ s ∧ p x :=
  Iff.rfl
#align set.mem_sep_iff Set.mem_sep_iff
-/

#print Set.sep_ext_iff /-
theorem sep_ext_iff : { x ∈ s | p x } = { x ∈ s | q x } ↔ ∀ x ∈ s, p x ↔ q x := by
  simp_rw [ext_iff, mem_sep_iff, and_congr_right_iff]
#align set.sep_ext_iff Set.sep_ext_iff
-/

#print Set.sep_eq_of_subset /-
theorem sep_eq_of_subset (h : s ⊆ t) : { x ∈ t | x ∈ s } = s :=
  inter_eq_self_of_subset_right h
#align set.sep_eq_of_subset Set.sep_eq_of_subset
-/

#print Set.sep_subset /-
@[simp]
theorem sep_subset (s : Set α) (p : α → Prop) : { x ∈ s | p x } ⊆ s := fun x => And.left
#align set.sep_subset Set.sep_subset
-/

#print Set.sep_eq_self_iff_mem_true /-
@[simp]
theorem sep_eq_self_iff_mem_true : { x ∈ s | p x } = s ↔ ∀ x ∈ s, p x := by
  simp_rw [ext_iff, mem_sep_iff, and_iff_left_iff_imp]
#align set.sep_eq_self_iff_mem_true Set.sep_eq_self_iff_mem_true
-/

#print Set.sep_eq_empty_iff_mem_false /-
@[simp]
theorem sep_eq_empty_iff_mem_false : { x ∈ s | p x } = ∅ ↔ ∀ x ∈ s, ¬p x := by
  simp_rw [ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false_iff, not_and]
#align set.sep_eq_empty_iff_mem_false Set.sep_eq_empty_iff_mem_false
-/

#print Set.sep_true /-
@[simp]
theorem sep_true : { x ∈ s | True } = s :=
  inter_univ s
#align set.sep_true Set.sep_true
-/

#print Set.sep_false /-
@[simp]
theorem sep_false : { x ∈ s | False } = ∅ :=
  inter_empty s
#align set.sep_false Set.sep_false
-/

#print Set.sep_empty /-
@[simp]
theorem sep_empty (p : α → Prop) : { x ∈ (∅ : Set α) | p x } = ∅ :=
  empty_inter p
#align set.sep_empty Set.sep_empty
-/

#print Set.sep_univ /-
@[simp]
theorem sep_univ : { x ∈ (univ : Set α) | p x } = { x | p x } :=
  univ_inter p
#align set.sep_univ Set.sep_univ
-/

/- warning: set.sep_union -> Set.sep_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) s) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (x : α) => And (Or (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)) (p x))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (p x))) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (p x))))
Case conversion may be inaccurate. Consider using '#align set.sep_union Set.sep_unionₓ'. -/
@[simp]
theorem sep_union : { x ∈ s ∪ t | p x } = { x ∈ s | p x } ∪ { x ∈ t | p x } :=
  union_inter_distrib_right
#align set.sep_union Set.sep_union

/- warning: set.sep_inter -> Set.sep_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) s) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {p : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (x : α) => And (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)) (p x))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (p x))) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) (p x))))
Case conversion may be inaccurate. Consider using '#align set.sep_inter Set.sep_interₓ'. -/
@[simp]
theorem sep_inter : { x ∈ s ∩ t | p x } = { x ∈ s | p x } ∩ { x ∈ t | p x } :=
  inter_inter_distrib_right s t p
#align set.sep_inter Set.sep_inter

/- warning: set.sep_and -> Set.sep_and is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => And (p x) (q x)) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) s) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => q x) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (And (p x) (q x)))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (p x))) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (q x))))
Case conversion may be inaccurate. Consider using '#align set.sep_and Set.sep_andₓ'. -/
@[simp]
theorem sep_and : { x ∈ s | p x ∧ q x } = { x ∈ s | p x } ∩ { x ∈ s | q x } :=
  inter_inter_distrib_left s p q
#align set.sep_and Set.sep_and

/- warning: set.sep_or -> Set.sep_or is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => Or (p x) (q x)) s) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => p x) s) (Sep.sep.{u1, u1} α (Set.{u1} α) (Set.hasSep.{u1} α) (fun (x : α) => q x) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {p : α -> Prop} {q : α -> Prop}, Eq.{succ u1} (Set.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Or (p x) (q x)))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (p x))) (setOf.{u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (q x))))
Case conversion may be inaccurate. Consider using '#align set.sep_or Set.sep_orₓ'. -/
@[simp]
theorem sep_or : { x ∈ s | p x ∨ q x } = { x ∈ s | p x } ∪ { x ∈ s | q x } :=
  inter_union_distrib_left
#align set.sep_or Set.sep_or

#print Set.sep_setOf /-
@[simp]
theorem sep_setOf : { x ∈ { y | p y } | q x } = { x | p x ∧ q x } :=
  rfl
#align set.sep_set_of Set.sep_setOf
-/

end Sep

#print Set.subset_singleton_iff /-
@[simp]
theorem subset_singleton_iff {α : Type _} {s : Set α} {x : α} : s ⊆ {x} ↔ ∀ y ∈ s, y = x :=
  Iff.rfl
#align set.subset_singleton_iff Set.subset_singleton_iff
-/

#print Set.subset_singleton_iff_eq /-
theorem subset_singleton_iff_eq {s : Set α} {x : α} : s ⊆ {x} ↔ s = ∅ ∨ s = {x} :=
  by
  obtain rfl | hs := s.eq_empty_or_nonempty
  use ⟨fun _ => Or.inl rfl, fun _ => empty_subset _⟩
  simp [eq_singleton_iff_nonempty_unique_mem, hs, hs.ne_empty]
#align set.subset_singleton_iff_eq Set.subset_singleton_iff_eq
-/

#print Set.Nonempty.subset_singleton_iff /-
theorem Nonempty.subset_singleton_iff (h : s.Nonempty) : s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff_eq.trans <| or_iff_right h.ne_empty
#align set.nonempty.subset_singleton_iff Set.Nonempty.subset_singleton_iff
-/

/- warning: set.ssubset_singleton_iff -> Set.ssubset_singleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, Iff (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.ssubset_singleton_iff Set.ssubset_singleton_iffₓ'. -/
theorem ssubset_singleton_iff {s : Set α} {x : α} : s ⊂ {x} ↔ s = ∅ :=
  by
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_right, and_not_self_iff, or_false_iff,
    and_iff_left_iff_imp]
  exact fun h => ne_of_eq_of_ne h (singleton_ne_empty _).symm
#align set.ssubset_singleton_iff Set.ssubset_singleton_iff

/- warning: set.eq_empty_of_ssubset_singleton -> Set.eq_empty_of_ssubset_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.hasSsubset.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) -> (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (HasSSubset.SSubset.{u1} (Set.{u1} α) (Set.instHasSSubsetSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) -> (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.eq_empty_of_ssubset_singleton Set.eq_empty_of_ssubset_singletonₓ'. -/
theorem eq_empty_of_ssubset_singleton {s : Set α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs
#align set.eq_empty_of_ssubset_singleton Set.eq_empty_of_ssubset_singleton

/-! ### Disjointness -/


/- warning: set.disjoint_iff -> Set.disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_iff Set.disjoint_iffₓ'. -/
protected theorem disjoint_iff : Disjoint s t ↔ s ∩ t ⊆ ∅ :=
  disjoint_iff_inf_le
#align set.disjoint_iff Set.disjoint_iff

/- warning: set.disjoint_iff_inter_eq_empty -> Set.disjoint_iff_inter_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_iff_inter_eq_empty Set.disjoint_iff_inter_eq_emptyₓ'. -/
theorem disjoint_iff_inter_eq_empty : Disjoint s t ↔ s ∩ t = ∅ :=
  disjoint_iff
#align set.disjoint_iff_inter_eq_empty Set.disjoint_iff_inter_eq_empty

/- warning: disjoint.inter_eq -> Disjoint.inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align disjoint.inter_eq Disjoint.inter_eqₓ'. -/
theorem Disjoint.inter_eq : Disjoint s t → s ∩ t = ∅ :=
  Disjoint.eq_bot
#align disjoint.inter_eq Disjoint.inter_eq

/- warning: set.disjoint_left -> Set.disjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_left Set.disjoint_leftₓ'. -/
theorem disjoint_left : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
  disjoint_iff_inf_le.trans <| forall_congr' fun _ => not_and
#align set.disjoint_left Set.disjoint_left

/- warning: set.disjoint_right -> Set.disjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (forall {{a : α}}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (forall {{a : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_right Set.disjoint_rightₓ'. -/
theorem disjoint_right : Disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint_comm, disjoint_left]
#align set.disjoint_right Set.disjoint_right

/- warning: set.not_disjoint_iff -> Set.not_disjoint_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t)) (Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))
Case conversion may be inaccurate. Consider using '#align set.not_disjoint_iff Set.not_disjoint_iffₓ'. -/
theorem not_disjoint_iff : ¬Disjoint s t ↔ ∃ x, x ∈ s ∧ x ∈ t :=
  Set.disjoint_iff.Not.trans <| not_forall.trans <| exists_congr fun x => not_not
#align set.not_disjoint_iff Set.not_disjoint_iff

/- warning: set.not_disjoint_iff_nonempty_inter -> Set.not_disjoint_iff_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t)) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.not_disjoint_iff_nonempty_inter Set.not_disjoint_iff_nonempty_interₓ'. -/
theorem not_disjoint_iff_nonempty_inter : ¬Disjoint s t ↔ (s ∩ t).Nonempty :=
  not_disjoint_iff
#align set.not_disjoint_iff_nonempty_inter Set.not_disjoint_iff_nonempty_inter

/- warning: set.nonempty.not_disjoint -> Set.Nonempty.not_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) -> (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) -> (Not (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.not_disjoint Set.Nonempty.not_disjointₓ'. -/
alias not_disjoint_iff_nonempty_inter ↔ _ nonempty.not_disjoint
#align set.nonempty.not_disjoint Set.Nonempty.not_disjoint

/- warning: set.disjoint_or_nonempty_inter -> Set.disjoint_or_nonempty_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Or (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Or (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.disjoint_or_nonempty_inter Set.disjoint_or_nonempty_interₓ'. -/
theorem disjoint_or_nonempty_inter (s t : Set α) : Disjoint s t ∨ (s ∩ t).Nonempty :=
  (em _).imp_right not_disjoint_iff_nonempty_inter.mp
#align set.disjoint_or_nonempty_inter Set.disjoint_or_nonempty_inter

/- warning: set.disjoint_iff_forall_ne -> Set.disjoint_iff_forall_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (forall (y : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (Ne.{succ u1} α x y)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{y : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y t) -> (Ne.{succ u1} α x y)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_iff_forall_ne Set.disjoint_iff_forall_neₓ'. -/
theorem disjoint_iff_forall_ne : Disjoint s t ↔ ∀ x ∈ s, ∀ y ∈ t, x ≠ y := by
  simp only [Ne.def, disjoint_left, @imp_not_comm _ (_ = _), forall_eq']
#align set.disjoint_iff_forall_ne Set.disjoint_iff_forall_ne

/- warning: disjoint.ne_of_mem -> Disjoint.ne_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (forall {x : α} {y : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y t) -> (Ne.{succ u1} α x y))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (forall {{x : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (forall {{hx : α}}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) hx t) -> (Ne.{succ u1} α x hx)))
Case conversion may be inaccurate. Consider using '#align disjoint.ne_of_mem Disjoint.ne_of_memₓ'. -/
theorem Disjoint.ne_of_mem (h : Disjoint s t) {x y} (hx : x ∈ s) (hy : y ∈ t) : x ≠ y :=
  disjoint_iff_forall_ne.mp h x hx y hy
#align disjoint.ne_of_mem Disjoint.ne_of_mem

/- warning: set.disjoint_of_subset_left -> Set.disjoint_of_subset_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₂ t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₁ t)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t s₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s₁ s₂)
Case conversion may be inaccurate. Consider using '#align set.disjoint_of_subset_left Set.disjoint_of_subset_leftₓ'. -/
theorem disjoint_of_subset_left (hs : s₁ ⊆ s₂) (h : Disjoint s₂ t) : Disjoint s₁ t :=
  h.mono_left hs
#align set.disjoint_of_subset_left Set.disjoint_of_subset_left

/- warning: set.disjoint_of_subset_right -> Set.disjoint_of_subset_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t₁)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t₁)
Case conversion may be inaccurate. Consider using '#align set.disjoint_of_subset_right Set.disjoint_of_subset_rightₓ'. -/
theorem disjoint_of_subset_right (ht : t₁ ⊆ t₂) (h : Disjoint s t₂) : Disjoint s t₁ :=
  h.mono_right ht
#align set.disjoint_of_subset_right Set.disjoint_of_subset_right

/- warning: set.disjoint_of_subset -> Set.disjoint_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₂ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s₁ t₁)
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t₁ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s₂ t₂) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s₁ t₁)
Case conversion may be inaccurate. Consider using '#align set.disjoint_of_subset Set.disjoint_of_subsetₓ'. -/
theorem disjoint_of_subset (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁ :=
  h.mono hs ht
#align set.disjoint_of_subset Set.disjoint_of_subset

/- warning: set.disjoint_union_left -> Set.disjoint_union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (And (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (And (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t u))
Case conversion may be inaccurate. Consider using '#align set.disjoint_union_left Set.disjoint_union_leftₓ'. -/
@[simp]
theorem disjoint_union_left : Disjoint (s ∪ t) u ↔ Disjoint s u ∧ Disjoint t u :=
  disjoint_sup_left
#align set.disjoint_union_left Set.disjoint_union_left

/- warning: set.disjoint_union_right -> Set.disjoint_union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) (And (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) (And (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u))
Case conversion may be inaccurate. Consider using '#align set.disjoint_union_right Set.disjoint_union_rightₓ'. -/
@[simp]
theorem disjoint_union_right : Disjoint s (t ∪ u) ↔ Disjoint s t ∧ Disjoint s u :=
  disjoint_sup_right
#align set.disjoint_union_right Set.disjoint_union_right

/- warning: set.disjoint_empty -> Set.disjoint_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.disjoint_empty Set.disjoint_emptyₓ'. -/
@[simp]
theorem disjoint_empty (s : Set α) : Disjoint s ∅ :=
  disjoint_bot_right
#align set.disjoint_empty Set.disjoint_empty

/- warning: set.empty_disjoint -> Set.empty_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s
Case conversion may be inaccurate. Consider using '#align set.empty_disjoint Set.empty_disjointₓ'. -/
@[simp]
theorem empty_disjoint (s : Set α) : Disjoint ∅ s :=
  disjoint_bot_left
#align set.empty_disjoint Set.empty_disjoint

/- warning: set.univ_disjoint -> Set.univ_disjoint is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Set.univ.{u1} α) s) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Set.univ.{u1} α) s) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.univ_disjoint Set.univ_disjointₓ'. -/
@[simp]
theorem univ_disjoint : Disjoint univ s ↔ s = ∅ :=
  top_disjoint
#align set.univ_disjoint Set.univ_disjoint

/- warning: set.disjoint_univ -> Set.disjoint_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Set.univ.{u1} α)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Set.univ.{u1} α)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.disjoint_univ Set.disjoint_univₓ'. -/
@[simp]
theorem disjoint_univ : Disjoint s univ ↔ s = ∅ :=
  disjoint_top
#align set.disjoint_univ Set.disjoint_univ

/- warning: set.disjoint_sdiff_left -> Set.disjoint_sdiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s) s
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s) s
Case conversion may be inaccurate. Consider using '#align set.disjoint_sdiff_left Set.disjoint_sdiff_leftₓ'. -/
theorem disjoint_sdiff_left : Disjoint (t \ s) s :=
  disjoint_sdiff_self_left
#align set.disjoint_sdiff_left Set.disjoint_sdiff_left

/- warning: set.disjoint_sdiff_right -> Set.disjoint_sdiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.disjoint_sdiff_right Set.disjoint_sdiff_rightₓ'. -/
theorem disjoint_sdiff_right : Disjoint s (t \ s) :=
  disjoint_sdiff_self_right
#align set.disjoint_sdiff_right Set.disjoint_sdiff_right

/- warning: set.disjoint_singleton_left -> Set.disjoint_singleton_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) s) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) s) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.disjoint_singleton_left Set.disjoint_singleton_leftₓ'. -/
@[simp]
theorem disjoint_singleton_left : Disjoint {a} s ↔ a ∉ s := by
  simp [Set.disjoint_iff, subset_def] <;> exact Iff.rfl
#align set.disjoint_singleton_left Set.disjoint_singleton_left

/- warning: set.disjoint_singleton_right -> Set.disjoint_singleton_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.disjoint_singleton_right Set.disjoint_singleton_rightₓ'. -/
@[simp]
theorem disjoint_singleton_right : Disjoint s {a} ↔ a ∉ s :=
  disjoint_comm.trans disjoint_singleton_left
#align set.disjoint_singleton_right Set.disjoint_singleton_right

/- warning: set.disjoint_singleton -> Set.disjoint_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) b)) (Ne.{succ u1} α a b)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {b : α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) b)) (Ne.{succ u1} α a b)
Case conversion may be inaccurate. Consider using '#align set.disjoint_singleton Set.disjoint_singletonₓ'. -/
@[simp]
theorem disjoint_singleton : Disjoint ({a} : Set α) {b} ↔ a ≠ b := by
  rw [disjoint_singleton_left, mem_singleton_iff]
#align set.disjoint_singleton Set.disjoint_singleton

/- warning: set.subset_diff -> Set.subset_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t u)) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u))
Case conversion may be inaccurate. Consider using '#align set.subset_diff Set.subset_diffₓ'. -/
theorem subset_diff : s ⊆ t \ u ↔ s ⊆ t ∧ Disjoint s u :=
  le_iff_subset.symm.trans le_sdiff
#align set.subset_diff Set.subset_diff

/-! ### Lemmas about complement -/


/- warning: set.compl_def -> Set.compl_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (setOf.{u1} α (fun (x : α) => Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (setOf.{u1} α (fun (x : α) => Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)))
Case conversion may be inaccurate. Consider using '#align set.compl_def Set.compl_defₓ'. -/
theorem compl_def (s : Set α) : sᶜ = { x | x ∉ s } :=
  rfl
#align set.compl_def Set.compl_def

/- warning: set.mem_compl -> Set.mem_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.mem_compl Set.mem_complₓ'. -/
theorem mem_compl {s : Set α} {x : α} (h : x ∉ s) : x ∈ sᶜ :=
  h
#align set.mem_compl Set.mem_compl

/- warning: set.compl_set_of -> Set.compl_setOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (p : α -> Prop), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (setOf.{u1} α (fun (a : α) => p a))) (setOf.{u1} α (fun (a : α) => Not (p a)))
but is expected to have type
  forall {α : Type.{u1}} (p : α -> Prop), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (setOf.{u1} α (fun (a : α) => p a))) (setOf.{u1} α (fun (a : α) => Not (p a)))
Case conversion may be inaccurate. Consider using '#align set.compl_set_of Set.compl_setOfₓ'. -/
theorem compl_setOf {α} (p : α → Prop) : { a | p a }ᶜ = { a | ¬p a } :=
  rfl
#align set.compl_set_of Set.compl_setOf

/- warning: set.not_mem_of_mem_compl -> Set.not_mem_of_mem_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align set.not_mem_of_mem_compl Set.not_mem_of_mem_complₓ'. -/
theorem not_mem_of_mem_compl {s : Set α} {x : α} (h : x ∈ sᶜ) : x ∉ s :=
  h
#align set.not_mem_of_mem_compl Set.not_mem_of_mem_compl

/- warning: set.mem_compl_iff -> Set.mem_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (x : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s))
Case conversion may be inaccurate. Consider using '#align set.mem_compl_iff Set.mem_compl_iffₓ'. -/
@[simp]
theorem mem_compl_iff (s : Set α) (x : α) : x ∈ sᶜ ↔ x ∉ s :=
  Iff.rfl
#align set.mem_compl_iff Set.mem_compl_iff

/- warning: set.not_mem_compl_iff -> Set.not_mem_compl_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, Iff (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, Iff (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)
Case conversion may be inaccurate. Consider using '#align set.not_mem_compl_iff Set.not_mem_compl_iffₓ'. -/
theorem not_mem_compl_iff {x : α} : x ∉ sᶜ ↔ x ∈ s :=
  not_not
#align set.not_mem_compl_iff Set.not_mem_compl_iff

/- warning: set.inter_compl_self -> Set.inter_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.inter_compl_self Set.inter_compl_selfₓ'. -/
@[simp]
theorem inter_compl_self (s : Set α) : s ∩ sᶜ = ∅ :=
  inf_compl_eq_bot
#align set.inter_compl_self Set.inter_compl_self

/- warning: set.compl_inter_self -> Set.compl_inter_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.compl_inter_self Set.compl_inter_selfₓ'. -/
@[simp]
theorem compl_inter_self (s : Set α) : sᶜ ∩ s = ∅ :=
  compl_inf_eq_bot
#align set.compl_inter_self Set.compl_inter_self

/- warning: set.compl_empty -> Set.compl_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.compl_empty Set.compl_emptyₓ'. -/
@[simp]
theorem compl_empty : (∅ : Set α)ᶜ = univ :=
  compl_bot
#align set.compl_empty Set.compl_empty

/- warning: set.compl_union -> Set.compl_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align set.compl_union Set.compl_unionₓ'. -/
@[simp]
theorem compl_union (s t : Set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  compl_sup
#align set.compl_union Set.compl_union

/- warning: set.compl_inter -> Set.compl_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align set.compl_inter Set.compl_interₓ'. -/
theorem compl_inter (s t : Set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ :=
  compl_inf
#align set.compl_inter Set.compl_inter

/- warning: set.compl_univ -> Set.compl_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.univ.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}}, Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Set.univ.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.compl_univ Set.compl_univₓ'. -/
@[simp]
theorem compl_univ : (univ : Set α)ᶜ = ∅ :=
  compl_top
#align set.compl_univ Set.compl_univ

/- warning: set.compl_empty_iff -> Set.compl_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.compl_empty_iff Set.compl_empty_iffₓ'. -/
@[simp]
theorem compl_empty_iff {s : Set α} : sᶜ = ∅ ↔ s = univ :=
  compl_eq_bot
#align set.compl_empty_iff Set.compl_empty_iff

/- warning: set.compl_univ_iff -> Set.compl_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Set.univ.{u1} α)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (Set.univ.{u1} α)) (Eq.{succ u1} (Set.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)))
Case conversion may be inaccurate. Consider using '#align set.compl_univ_iff Set.compl_univ_iffₓ'. -/
@[simp]
theorem compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅ :=
  compl_eq_top
#align set.compl_univ_iff Set.compl_univ_iff

/- warning: set.compl_ne_univ -> Set.compl_ne_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Ne.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (Set.univ.{u1} α)) (Set.Nonempty.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Ne.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (Set.univ.{u1} α)) (Set.Nonempty.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.compl_ne_univ Set.compl_ne_univₓ'. -/
theorem compl_ne_univ : sᶜ ≠ univ ↔ s.Nonempty :=
  compl_univ_iff.Not.trans nonempty_iff_ne_empty.symm
#align set.compl_ne_univ Set.compl_ne_univ

/- warning: set.nonempty_compl -> Set.nonempty_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Ne.{succ u1} (Set.{u1} α) s (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.nonempty_compl Set.nonempty_complₓ'. -/
theorem nonempty_compl : sᶜ.Nonempty ↔ s ≠ univ :=
  (ne_univ_iff_exists_not_mem s).symm
#align set.nonempty_compl Set.nonempty_compl

/- warning: set.mem_compl_singleton_iff -> Set.mem_compl_singleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {x : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Ne.{succ u1} α x a)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {x : α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Ne.{succ u1} α x a)
Case conversion may be inaccurate. Consider using '#align set.mem_compl_singleton_iff Set.mem_compl_singleton_iffₓ'. -/
theorem mem_compl_singleton_iff {a x : α} : x ∈ ({a} : Set α)ᶜ ↔ x ≠ a :=
  Iff.rfl
#align set.mem_compl_singleton_iff Set.mem_compl_singleton_iff

/- warning: set.compl_singleton_eq -> Set.compl_singleton_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))
but is expected to have type
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))
Case conversion may be inaccurate. Consider using '#align set.compl_singleton_eq Set.compl_singleton_eqₓ'. -/
theorem compl_singleton_eq (a : α) : ({a} : Set α)ᶜ = { x | x ≠ a } :=
  rfl
#align set.compl_singleton_eq Set.compl_singleton_eq

/- warning: set.compl_ne_eq_singleton -> Set.compl_ne_eq_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)
but is expected to have type
  forall {α : Type.{u1}} (a : α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (setOf.{u1} α (fun (x : α) => Ne.{succ u1} α x a))) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)
Case conversion may be inaccurate. Consider using '#align set.compl_ne_eq_singleton Set.compl_ne_eq_singletonₓ'. -/
@[simp]
theorem compl_ne_eq_singleton (a : α) : ({ x | x ≠ a } : Set α)ᶜ = {a} :=
  compl_compl _
#align set.compl_ne_eq_singleton Set.compl_ne_eq_singleton

/- warning: set.union_eq_compl_compl_inter_compl -> Set.union_eq_compl_compl_inter_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)))
Case conversion may be inaccurate. Consider using '#align set.union_eq_compl_compl_inter_compl Set.union_eq_compl_compl_inter_complₓ'. -/
theorem union_eq_compl_compl_inter_compl (s t : Set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
  ext fun x => or_iff_not_and_not
#align set.union_eq_compl_compl_inter_compl Set.union_eq_compl_compl_inter_compl

/- warning: set.inter_eq_compl_compl_union_compl -> Set.inter_eq_compl_compl_union_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)))
Case conversion may be inaccurate. Consider using '#align set.inter_eq_compl_compl_union_compl Set.inter_eq_compl_compl_union_complₓ'. -/
theorem inter_eq_compl_compl_union_compl (s t : Set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
  ext fun x => and_iff_not_or_not
#align set.inter_eq_compl_compl_union_compl Set.inter_eq_compl_compl_union_compl

/- warning: set.union_compl_self -> Set.union_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s)) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s)) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.union_compl_self Set.union_compl_selfₓ'. -/
@[simp]
theorem union_compl_self (s : Set α) : s ∪ sᶜ = univ :=
  eq_univ_iff_forall.2 fun x => em _
#align set.union_compl_self Set.union_compl_self

/- warning: set.compl_union_self -> Set.compl_union_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) s) (Set.univ.{u1} α)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) s) (Set.univ.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.compl_union_self Set.compl_union_selfₓ'. -/
@[simp]
theorem compl_union_self (s : Set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]
#align set.compl_union_self Set.compl_union_self

/- warning: set.compl_subset_comm -> Set.compl_subset_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) s)
Case conversion may be inaccurate. Consider using '#align set.compl_subset_comm Set.compl_subset_commₓ'. -/
theorem compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s :=
  @compl_le_iff_compl_le _ s _ _
#align set.compl_subset_comm Set.compl_subset_comm

/- warning: set.subset_compl_comm -> Set.subset_compl_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.subset_compl_comm Set.subset_compl_commₓ'. -/
theorem subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ :=
  @le_compl_iff_le_compl _ _ _ t
#align set.subset_compl_comm Set.subset_compl_comm

/- warning: set.compl_subset_compl -> Set.compl_subset_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.compl_subset_compl Set.compl_subset_complₓ'. -/
@[simp]
theorem compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s :=
  @compl_le_compl_iff_le (Set α) _ _ _
#align set.compl_subset_compl Set.compl_subset_compl

/- warning: set.subset_compl_iff_disjoint_left -> Set.subset_compl_iff_disjoint_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t s)
Case conversion may be inaccurate. Consider using '#align set.subset_compl_iff_disjoint_left Set.subset_compl_iff_disjoint_leftₓ'. -/
theorem subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ Disjoint t s :=
  @le_compl_iff_disjoint_left (Set α) _ _ _
#align set.subset_compl_iff_disjoint_left Set.subset_compl_iff_disjoint_left

/- warning: set.subset_compl_iff_disjoint_right -> Set.subset_compl_iff_disjoint_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t)
Case conversion may be inaccurate. Consider using '#align set.subset_compl_iff_disjoint_right Set.subset_compl_iff_disjoint_rightₓ'. -/
theorem subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ Disjoint s t :=
  @le_compl_iff_disjoint_right (Set α) _ _ _
#align set.subset_compl_iff_disjoint_right Set.subset_compl_iff_disjoint_right

/- warning: set.disjoint_compl_left_iff_subset -> Set.disjoint_compl_left_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.disjoint_compl_left_iff_subset Set.disjoint_compl_left_iff_subsetₓ'. -/
theorem disjoint_compl_left_iff_subset : Disjoint (sᶜ) t ↔ t ⊆ s :=
  disjoint_compl_left_iff
#align set.disjoint_compl_left_iff_subset Set.disjoint_compl_left_iff_subset

/- warning: set.disjoint_compl_right_iff_subset -> Set.disjoint_compl_right_iff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.disjoint_compl_right_iff_subset Set.disjoint_compl_right_iff_subsetₓ'. -/
theorem disjoint_compl_right_iff_subset : Disjoint s (tᶜ) ↔ s ⊆ t :=
  disjoint_compl_right_iff
#align set.disjoint_compl_right_iff_subset Set.disjoint_compl_right_iff_subset

/- warning: disjoint.subset_compl_right -> Disjoint.subset_compl_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align disjoint.subset_compl_right Disjoint.subset_compl_rightₓ'. -/
alias subset_compl_iff_disjoint_right ↔ _ _root_.disjoint.subset_compl_right
#align disjoint.subset_compl_right Disjoint.subset_compl_right

/- warning: disjoint.subset_compl_left -> Disjoint.subset_compl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align disjoint.subset_compl_left Disjoint.subset_compl_leftₓ'. -/
alias subset_compl_iff_disjoint_left ↔ _ _root_.disjoint.subset_compl_left
#align disjoint.subset_compl_left Disjoint.subset_compl_left

/- warning: has_subset.subset.disjoint_compl_left -> HasSubset.Subset.disjoint_compl_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) t)
Case conversion may be inaccurate. Consider using '#align has_subset.subset.disjoint_compl_left HasSubset.Subset.disjoint_compl_leftₓ'. -/
alias disjoint_compl_left_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_left
#align has_subset.subset.disjoint_compl_left HasSubset.Subset.disjoint_compl_left

/- warning: has_subset.subset.disjoint_compl_right -> HasSubset.Subset.disjoint_compl_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align has_subset.subset.disjoint_compl_right HasSubset.Subset.disjoint_compl_rightₓ'. -/
alias disjoint_compl_right_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_right
#align has_subset.subset.disjoint_compl_right HasSubset.Subset.disjoint_compl_right

/- warning: set.subset_union_compl_iff_inter_subset -> Set.subset_union_compl_iff_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) u))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) u))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t)
Case conversion may be inaccurate. Consider using '#align set.subset_union_compl_iff_inter_subset Set.subset_union_compl_iff_inter_subsetₓ'. -/
theorem subset_union_compl_iff_inter_subset {s t u : Set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
  (@isCompl_compl _ u _).le_sup_right_iff_inf_left_le
#align set.subset_union_compl_iff_inter_subset Set.subset_union_compl_iff_inter_subset

/- warning: set.compl_subset_iff_union -> Set.compl_subset_iff_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) t) (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Set.univ.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) t) (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Set.univ.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.compl_subset_iff_union Set.compl_subset_iff_unionₓ'. -/
theorem compl_subset_iff_union {s t : Set α} : sᶜ ⊆ t ↔ s ∪ t = univ :=
  Iff.symm <| eq_univ_iff_forall.trans <| forall_congr' fun a => or_iff_not_imp_left
#align set.compl_subset_iff_union Set.compl_subset_iff_union

/- warning: set.subset_compl_singleton_iff -> Set.subset_compl_singleton_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))
Case conversion may be inaccurate. Consider using '#align set.subset_compl_singleton_iff Set.subset_compl_singleton_iffₓ'. -/
@[simp]
theorem subset_compl_singleton_iff {a : α} {s : Set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
  subset_compl_comm.trans singleton_subset_iff
#align set.subset_compl_singleton_iff Set.subset_compl_singleton_iff

/- warning: set.inter_subset -> Set.inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b) c) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) b) c))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b) c) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) b) c))
Case conversion may be inaccurate. Consider using '#align set.inter_subset Set.inter_subsetₓ'. -/
theorem inter_subset (a b c : Set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
  forall_congr' fun x => and_imp.trans <| imp_congr_right fun _ => imp_iff_not_or
#align set.inter_subset Set.inter_subset

/- warning: set.inter_compl_nonempty_iff -> Set.inter_compl_nonempty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.inter_compl_nonempty_iff Set.inter_compl_nonempty_iffₓ'. -/
theorem inter_compl_nonempty_iff {s t : Set α} : (s ∩ tᶜ).Nonempty ↔ ¬s ⊆ t :=
  (not_subset.trans <| exists_congr fun x => by simp [mem_compl]).symm
#align set.inter_compl_nonempty_iff Set.inter_compl_nonempty_iff

/-! ### Lemmas about set difference -/


/- warning: set.diff_eq -> Set.diff_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align set.diff_eq Set.diff_eqₓ'. -/
theorem diff_eq (s t : Set α) : s \ t = s ∩ tᶜ :=
  rfl
#align set.diff_eq Set.diff_eq

/- warning: set.mem_diff -> Set.mem_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (x : α), Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (x : α), Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)))
Case conversion may be inaccurate. Consider using '#align set.mem_diff Set.mem_diffₓ'. -/
@[simp]
theorem mem_diff {s t : Set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t :=
  Iff.rfl
#align set.mem_diff Set.mem_diff

/- warning: set.mem_diff_of_mem -> Set.mem_diff_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.mem_diff_of_mem Set.mem_diff_of_memₓ'. -/
theorem mem_diff_of_mem {s t : Set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
  ⟨h1, h2⟩
#align set.mem_diff_of_mem Set.mem_diff_of_mem

/- warning: set.not_mem_diff_of_mem -> Set.not_mem_diff_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align set.not_mem_diff_of_mem Set.not_mem_diff_of_memₓ'. -/
theorem not_mem_diff_of_mem {s t : Set α} {x : α} (hx : x ∈ t) : x ∉ s \ t := fun h => h.2 hx
#align set.not_mem_diff_of_mem Set.not_mem_diff_of_mem

/- warning: set.mem_of_mem_diff -> Set.mem_of_mem_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) -> (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)
Case conversion may be inaccurate. Consider using '#align set.mem_of_mem_diff Set.mem_of_mem_diffₓ'. -/
theorem mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
  h.left
#align set.mem_of_mem_diff Set.mem_of_mem_diff

/- warning: set.not_mem_of_mem_diff -> Set.not_mem_of_mem_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x t))
Case conversion may be inaccurate. Consider using '#align set.not_mem_of_mem_diff Set.not_mem_of_mem_diffₓ'. -/
theorem not_mem_of_mem_diff {s t : Set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
  h.right
#align set.not_mem_of_mem_diff Set.not_mem_of_mem_diff

/- warning: set.diff_eq_compl_inter -> Set.diff_eq_compl_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) s)
Case conversion may be inaccurate. Consider using '#align set.diff_eq_compl_inter Set.diff_eq_compl_interₓ'. -/
theorem diff_eq_compl_inter {s t : Set α} : s \ t = tᶜ ∩ s := by rw [diff_eq, inter_comm]
#align set.diff_eq_compl_inter Set.diff_eq_compl_inter

/- warning: set.nonempty_diff -> Set.nonempty_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty_diff Set.nonempty_diffₓ'. -/
theorem nonempty_diff {s t : Set α} : (s \ t).Nonempty ↔ ¬s ⊆ t :=
  inter_compl_nonempty_iff
#align set.nonempty_diff Set.nonempty_diff

/- warning: set.diff_subset -> Set.diff_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) s
Case conversion may be inaccurate. Consider using '#align set.diff_subset Set.diff_subsetₓ'. -/
theorem diff_subset (s t : Set α) : s \ t ⊆ s :=
  show s \ t ≤ s from sdiff_le
#align set.diff_subset Set.diff_subset

/- warning: set.union_diff_cancel' -> Set.union_diff_cancel' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t u) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) u s)) u)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t u) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) u s)) u)
Case conversion may be inaccurate. Consider using '#align set.union_diff_cancel' Set.union_diff_cancel'ₓ'. -/
theorem union_diff_cancel' {s t u : Set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ u \ s = u :=
  sup_sdiff_cancel' h₁ h₂
#align set.union_diff_cancel' Set.union_diff_cancel'

/- warning: set.union_diff_cancel -> Set.union_diff_cancel is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) t)
Case conversion may be inaccurate. Consider using '#align set.union_diff_cancel Set.union_diff_cancelₓ'. -/
theorem union_diff_cancel {s t : Set α} (h : s ⊆ t) : s ∪ t \ s = t :=
  sup_sdiff_cancel_right h
#align set.union_diff_cancel Set.union_diff_cancel

/- warning: set.union_diff_cancel_left -> Set.union_diff_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s) t)
Case conversion may be inaccurate. Consider using '#align set.union_diff_cancel_left Set.union_diff_cancel_leftₓ'. -/
theorem union_diff_cancel_left {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
  Disjoint.sup_sdiff_cancel_left <| disjoint_iff_inf_le.2 h
#align set.union_diff_cancel_left Set.union_diff_cancel_left

/- warning: set.union_diff_cancel_right -> Set.union_diff_cancel_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t) s)
Case conversion may be inaccurate. Consider using '#align set.union_diff_cancel_right Set.union_diff_cancel_rightₓ'. -/
theorem union_diff_cancel_right {s t : Set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
  Disjoint.sup_sdiff_cancel_right <| disjoint_iff_inf_le.2 h
#align set.union_diff_cancel_right Set.union_diff_cancel_right

/- warning: set.union_diff_left -> Set.union_diff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) s) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) s) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.union_diff_left Set.union_diff_leftₓ'. -/
@[simp]
theorem union_diff_left {s t : Set α} : (s ∪ t) \ s = t \ s :=
  sup_sdiff_left_self
#align set.union_diff_left Set.union_diff_left

/- warning: set.union_diff_right -> Set.union_diff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.union_diff_right Set.union_diff_rightₓ'. -/
@[simp]
theorem union_diff_right {s t : Set α} : (s ∪ t) \ t = s \ t :=
  sup_sdiff_right_self
#align set.union_diff_right Set.union_diff_right

/- warning: set.union_diff_distrib -> Set.union_diff_distrib is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.union_diff_distrib Set.union_diff_distribₓ'. -/
theorem union_diff_distrib {s t u : Set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
  sup_sdiff
#align set.union_diff_distrib Set.union_diff_distrib

/- warning: set.inter_diff_assoc -> Set.inter_diff_assoc is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a b) c) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) b c))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α) (c : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a b) c) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) b c))
Case conversion may be inaccurate. Consider using '#align set.inter_diff_assoc Set.inter_diff_assocₓ'. -/
theorem inter_diff_assoc (a b c : Set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
  inf_sdiff_assoc
#align set.inter_diff_assoc Set.inter_diff_assoc

/- warning: set.inter_diff_self -> Set.inter_diff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) b a)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (a : Set.{u1} α) (b : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) b a)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.inter_diff_self Set.inter_diff_selfₓ'. -/
@[simp]
theorem inter_diff_self (a b : Set α) : a ∩ (b \ a) = ∅ :=
  inf_sdiff_self_right
#align set.inter_diff_self Set.inter_diff_self

/- warning: set.inter_union_diff -> Set.inter_union_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) s
Case conversion may be inaccurate. Consider using '#align set.inter_union_diff Set.inter_union_diffₓ'. -/
@[simp]
theorem inter_union_diff (s t : Set α) : s ∩ t ∪ s \ t = s :=
  sup_inf_sdiff s t
#align set.inter_union_diff Set.inter_union_diff

/- warning: set.diff_union_inter -> Set.diff_union_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) s
Case conversion may be inaccurate. Consider using '#align set.diff_union_inter Set.diff_union_interₓ'. -/
@[simp]
theorem diff_union_inter (s t : Set α) : s \ t ∪ s ∩ t = s :=
  by
  rw [union_comm]
  exact sup_inf_sdiff _ _
#align set.diff_union_inter Set.diff_union_inter

/- warning: set.inter_union_compl -> Set.inter_union_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))) s
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))) s
Case conversion may be inaccurate. Consider using '#align set.inter_union_compl Set.inter_union_complₓ'. -/
@[simp]
theorem inter_union_compl (s t : Set α) : s ∩ t ∪ s ∩ tᶜ = s :=
  inter_union_diff _ _
#align set.inter_union_compl Set.inter_union_compl

/- warning: set.diff_subset_diff -> Set.diff_subset_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t₂ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁ t₁) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₂ t₂))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u1} α} {t₂ : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t₂ t₁) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s₁ t₁) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.diff_subset_diff Set.diff_subset_diffₓ'. -/
theorem diff_subset_diff {s₁ s₂ t₁ t₂ : Set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
  show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂ from sdiff_le_sdiff
#align set.diff_subset_diff Set.diff_subset_diff

/- warning: set.diff_subset_diff_left -> Set.diff_subset_diff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₁ t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s₁ t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.diff_subset_diff_left Set.diff_subset_diff_leftₓ'. -/
theorem diff_subset_diff_left {s₁ s₂ t : Set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
  sdiff_le_sdiff_right ‹s₁ ≤ s₂›
#align set.diff_subset_diff_left Set.diff_subset_diff_left

/- warning: set.diff_subset_diff_right -> Set.diff_subset_diff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.diff_subset_diff_right Set.diff_subset_diff_rightₓ'. -/
theorem diff_subset_diff_right {s t u : Set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
  sdiff_le_sdiff_left ‹t ≤ u›
#align set.diff_subset_diff_right Set.diff_subset_diff_right

/- warning: set.compl_eq_univ_diff -> Set.compl_eq_univ_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.univ.{u1} α) s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.univ.{u1} α) s)
Case conversion may be inaccurate. Consider using '#align set.compl_eq_univ_diff Set.compl_eq_univ_diffₓ'. -/
theorem compl_eq_univ_diff (s : Set α) : sᶜ = univ \ s :=
  top_sdiff.symm
#align set.compl_eq_univ_diff Set.compl_eq_univ_diff

/- warning: set.empty_diff -> Set.empty_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.empty_diff Set.empty_diffₓ'. -/
@[simp]
theorem empty_diff (s : Set α) : (∅ \ s : Set α) = ∅ :=
  bot_sdiff
#align set.empty_diff Set.empty_diff

/- warning: set.diff_eq_empty -> Set.diff_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_eq_empty Set.diff_eq_emptyₓ'. -/
theorem diff_eq_empty {s t : Set α} : s \ t = ∅ ↔ s ⊆ t :=
  sdiff_eq_bot_iff
#align set.diff_eq_empty Set.diff_eq_empty

/- warning: set.diff_empty -> Set.diff_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) s
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) s
Case conversion may be inaccurate. Consider using '#align set.diff_empty Set.diff_emptyₓ'. -/
@[simp]
theorem diff_empty {s : Set α} : s \ ∅ = s :=
  sdiff_bot
#align set.diff_empty Set.diff_empty

/- warning: set.diff_univ -> Set.diff_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Set.univ.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Set.univ.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.diff_univ Set.diff_univₓ'. -/
@[simp]
theorem diff_univ (s : Set α) : s \ univ = ∅ :=
  diff_eq_empty.2 (subset_univ s)
#align set.diff_univ Set.diff_univ

/- warning: set.diff_diff -> Set.diff_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) u) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) u) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.diff_diff Set.diff_diffₓ'. -/
theorem diff_diff {u : Set α} : (s \ t) \ u = s \ (t ∪ u) :=
  sdiff_sdiff_left
#align set.diff_diff Set.diff_diff

/- warning: set.diff_diff_comm -> Set.diff_diff_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) u) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) u) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u) t)
Case conversion may be inaccurate. Consider using '#align set.diff_diff_comm Set.diff_diff_commₓ'. -/
-- the following statement contains parentheses to help the reader
theorem diff_diff_comm {s t u : Set α} : (s \ t) \ u = (s \ u) \ t :=
  sdiff_sdiff_comm
#align set.diff_diff_comm Set.diff_diff_comm

/- warning: set.diff_subset_iff -> Set.diff_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.diff_subset_iff Set.diff_subset_iffₓ'. -/
theorem diff_subset_iff {s t u : Set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
  show s \ t ≤ u ↔ s ≤ t ∪ u from sdiff_le_iff
#align set.diff_subset_iff Set.diff_subset_iff

/- warning: set.subset_diff_union -> Set.subset_diff_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) t)
Case conversion may be inaccurate. Consider using '#align set.subset_diff_union Set.subset_diff_unionₓ'. -/
theorem subset_diff_union (s t : Set α) : s ⊆ s \ t ∪ t :=
  show s ≤ s \ t ∪ t from le_sdiff_sup
#align set.subset_diff_union Set.subset_diff_union

/- warning: set.diff_union_of_subset -> Set.diff_union_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) t) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) t s) -> (Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) t) s)
Case conversion may be inaccurate. Consider using '#align set.diff_union_of_subset Set.diff_union_of_subsetₓ'. -/
theorem diff_union_of_subset {s t : Set α} (h : t ⊆ s) : s \ t ∪ t = s :=
  Subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)
#align set.diff_union_of_subset Set.diff_union_of_subset

/- warning: set.diff_singleton_subset_iff -> Set.diff_singleton_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x t))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)) t) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x t))
Case conversion may be inaccurate. Consider using '#align set.diff_singleton_subset_iff Set.diff_singleton_subset_iffₓ'. -/
@[simp]
theorem diff_singleton_subset_iff {x : α} {s t : Set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t :=
  by
  rw [← union_singleton, union_comm]
  apply diff_subset_iff
#align set.diff_singleton_subset_iff Set.diff_singleton_subset_iff

/- warning: set.subset_diff_singleton -> Set.subset_diff_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s)) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align set.subset_diff_singleton Set.subset_diff_singletonₓ'. -/
theorem subset_diff_singleton {x : α} {s t : Set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
  subset_inter h <| subset_compl_comm.1 <| singleton_subset_iff.2 hx
#align set.subset_diff_singleton Set.subset_diff_singleton

/- warning: set.subset_insert_diff_singleton -> Set.subset_insert_diff_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) x)))
but is expected to have type
  forall {α : Type.{u1}} (x : α) (s : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) x)))
Case conversion may be inaccurate. Consider using '#align set.subset_insert_diff_singleton Set.subset_insert_diff_singletonₓ'. -/
theorem subset_insert_diff_singleton (x : α) (s : Set α) : s ⊆ insert x (s \ {x}) := by
  rw [← diff_singleton_subset_iff]
#align set.subset_insert_diff_singleton Set.subset_insert_diff_singleton

/- warning: set.diff_subset_comm -> Set.diff_subset_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) u) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u) t)
Case conversion may be inaccurate. Consider using '#align set.diff_subset_comm Set.diff_subset_commₓ'. -/
theorem diff_subset_comm {s t u : Set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
  show s \ t ≤ u ↔ s \ u ≤ t from sdiff_le_comm
#align set.diff_subset_comm Set.diff_subset_comm

/- warning: set.diff_inter -> Set.diff_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.diff_inter Set.diff_interₓ'. -/
theorem diff_inter {s t u : Set α} : s \ (t ∩ u) = s \ t ∪ s \ u :=
  sdiff_inf
#align set.diff_inter Set.diff_inter

/- warning: set.diff_inter_diff -> Set.diff_inter_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s u)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.diff_inter_diff Set.diff_inter_diffₓ'. -/
theorem diff_inter_diff {s t u : Set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
  sdiff_sup.symm
#align set.diff_inter_diff Set.diff_inter_diff

/- warning: set.diff_compl -> Set.diff_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_compl Set.diff_complₓ'. -/
theorem diff_compl : s \ tᶜ = s ∩ t :=
  sdiff_compl
#align set.diff_compl Set.diff_compl

/- warning: set.diff_diff_right -> Set.diff_diff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t u)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t u)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.diff_diff_right Set.diff_diff_rightₓ'. -/
theorem diff_diff_right {s t u : Set α} : s \ (t \ u) = s \ t ∪ s ∩ u :=
  sdiff_sdiff_right'
#align set.diff_diff_right Set.diff_diff_right

/- warning: set.insert_diff_of_mem -> Set.insert_diff_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {t : Set.{u1} α} (s : Set.{u1} α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {t : Set.{u1} α} (s : Set.{u1} α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.insert_diff_of_mem Set.insert_diff_of_memₓ'. -/
@[simp]
theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
  by
  ext
  constructor <;> simp (config := { contextual := true }) [or_imp, h]
#align set.insert_diff_of_mem Set.insert_diff_of_mem

/- warning: set.insert_diff_of_not_mem -> Set.insert_diff_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {t : Set.{u1} α} (s : Set.{u1} α), (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {t : Set.{u1} α} (s : Set.{u1} α), (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align set.insert_diff_of_not_mem Set.insert_diff_of_not_memₓ'. -/
theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) := by
  classical
    ext x
    by_cases h' : x ∈ t
    · have : x ≠ a := by
        intro H
        rw [H] at h'
        exact h h'
      simp [h, h', this]
    · simp [h, h']
#align set.insert_diff_of_not_mem Set.insert_diff_of_not_mem

/- warning: set.insert_diff_self_of_not_mem -> Set.insert_diff_self_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) s)
Case conversion may be inaccurate. Consider using '#align set.insert_diff_self_of_not_mem Set.insert_diff_self_of_not_memₓ'. -/
theorem insert_diff_self_of_not_mem {a : α} {s : Set α} (h : a ∉ s) : insert a s \ {a} = s :=
  by
  ext
  simp [and_iff_left_of_imp fun hx : x ∈ s => show x ≠ a from fun hxa => h <| hxa ▸ hx]
#align set.insert_diff_self_of_not_mem Set.insert_diff_self_of_not_mem

/- warning: set.insert_diff_eq_singleton -> Set.insert_diff_eq_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) s) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))
Case conversion may be inaccurate. Consider using '#align set.insert_diff_eq_singleton Set.insert_diff_eq_singletonₓ'. -/
@[simp]
theorem insert_diff_eq_singleton {a : α} {s : Set α} (h : a ∉ s) : insert a s \ s = {a} :=
  by
  ext
  rw [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, or_and_right, and_not_self_iff,
    or_false_iff, and_iff_left_iff_imp]
  rintro rfl
  exact h
#align set.insert_diff_eq_singleton Set.insert_diff_eq_singleton

/- warning: set.inter_insert_of_mem -> Set.inter_insert_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a t)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a t)) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align set.inter_insert_of_mem Set.inter_insert_of_memₓ'. -/
theorem inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
#align set.inter_insert_of_mem Set.inter_insert_of_mem

/- warning: set.insert_inter_of_mem -> Set.insert_inter_of_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)))
Case conversion may be inaccurate. Consider using '#align set.insert_inter_of_mem Set.insert_inter_of_memₓ'. -/
theorem insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) := by
  rw [insert_inter_distrib, insert_eq_of_mem h]
#align set.insert_inter_of_mem Set.insert_inter_of_mem

/- warning: set.inter_insert_of_not_mem -> Set.inter_insert_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.inter_insert_of_not_mem Set.inter_insert_of_not_memₓ'. -/
theorem inter_insert_of_not_mem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
  ext fun x => and_congr_right fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h
#align set.inter_insert_of_not_mem Set.inter_insert_of_not_mem

/- warning: set.insert_inter_of_not_mem -> Set.insert_inter_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s) t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.insert_inter_of_not_mem Set.insert_inter_of_not_memₓ'. -/
theorem insert_inter_of_not_mem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
  ext fun x => and_congr_left fun hx => or_iff_right <| ne_of_mem_of_not_mem hx h
#align set.insert_inter_of_not_mem Set.insert_inter_of_not_mem

/- warning: set.union_diff_self -> Set.union_diff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.union_diff_self Set.union_diff_selfₓ'. -/
@[simp]
theorem union_diff_self {s t : Set α} : s ∪ t \ s = s ∪ t :=
  sup_sdiff_self _ _
#align set.union_diff_self Set.union_diff_self

/- warning: set.diff_union_self -> Set.diff_union_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_union_self Set.diff_union_selfₓ'. -/
@[simp]
theorem diff_union_self {s t : Set α} : s \ t ∪ t = s ∪ t :=
  sdiff_sup_self _ _
#align set.diff_union_self Set.diff_union_self

/- warning: set.diff_inter_self -> Set.diff_inter_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : Set.{u1} α} {b : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) b a) a) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {a : Set.{u1} α} {b : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) b a) a) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.diff_inter_self Set.diff_inter_selfₓ'. -/
@[simp]
theorem diff_inter_self {a b : Set α} : b \ a ∩ a = ∅ :=
  inf_sdiff_self_left
#align set.diff_inter_self Set.diff_inter_self

/- warning: set.diff_inter_self_eq_diff -> Set.diff_inter_self_eq_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_inter_self_eq_diff Set.diff_inter_self_eq_diffₓ'. -/
@[simp]
theorem diff_inter_self_eq_diff {s t : Set α} : s \ (t ∩ s) = s \ t :=
  sdiff_inf_self_right _ _
#align set.diff_inter_self_eq_diff Set.diff_inter_self_eq_diff

/- warning: set.diff_self_inter -> Set.diff_self_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_self_inter Set.diff_self_interₓ'. -/
@[simp]
theorem diff_self_inter {s t : Set α} : s \ (s ∩ t) = s \ t :=
  sdiff_inf_self_left _ _
#align set.diff_self_inter Set.diff_self_inter

/- warning: set.diff_singleton_eq_self -> Set.diff_singleton_eq_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a)) s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a)) s)
Case conversion may be inaccurate. Consider using '#align set.diff_singleton_eq_self Set.diff_singleton_eq_selfₓ'. -/
@[simp]
theorem diff_singleton_eq_self {a : α} {s : Set α} (h : a ∉ s) : s \ {a} = s :=
  sdiff_eq_self_iff_disjoint.2 <| by simp [h]
#align set.diff_singleton_eq_self Set.diff_singleton_eq_self

/- warning: set.insert_diff_singleton -> Set.insert_diff_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) a))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.hasInsert.{u1} α) a s)
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) a))) (Insert.insert.{u1, u1} α (Set.{u1} α) (Set.instInsertSet.{u1} α) a s)
Case conversion may be inaccurate. Consider using '#align set.insert_diff_singleton Set.insert_diff_singletonₓ'. -/
@[simp]
theorem insert_diff_singleton {a : α} {s : Set α} : insert a (s \ {a}) = insert a s := by
  simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]
#align set.insert_diff_singleton Set.insert_diff_singleton

/- warning: set.diff_self -> Set.diff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s s) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))
Case conversion may be inaccurate. Consider using '#align set.diff_self Set.diff_selfₓ'. -/
@[simp]
theorem diff_self {s : Set α} : s \ s = ∅ :=
  sdiff_self
#align set.diff_self Set.diff_self

/- warning: set.diff_diff_right_self -> Set.diff_diff_right_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.diff_diff_right_self Set.diff_diff_right_selfₓ'. -/
theorem diff_diff_right_self (s t : Set α) : s \ (s \ t) = s ∩ t :=
  sdiff_sdiff_right_self
#align set.diff_diff_right_self Set.diff_diff_right_self

/- warning: set.diff_diff_cancel_left -> Set.diff_diff_cancel_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t) -> (Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) s)
Case conversion may be inaccurate. Consider using '#align set.diff_diff_cancel_left Set.diff_diff_cancel_leftₓ'. -/
theorem diff_diff_cancel_left {s t : Set α} (h : s ⊆ t) : t \ (t \ s) = s :=
  sdiff_sdiff_eq_self h
#align set.diff_diff_cancel_left Set.diff_diff_cancel_left

/- warning: set.mem_diff_singleton -> Set.mem_diff_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {x : α} {y : α} {s : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) y))) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (Ne.{succ u1} α x y))
but is expected to have type
  forall {α : Type.{u1}} {x : α} {y : α} {s : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.instSingletonSet.{u1} α) y))) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Ne.{succ u1} α x y))
Case conversion may be inaccurate. Consider using '#align set.mem_diff_singleton Set.mem_diff_singletonₓ'. -/
theorem mem_diff_singleton {x y : α} {s : Set α} : x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y :=
  Iff.rfl
#align set.mem_diff_singleton Set.mem_diff_singleton

/- warning: set.mem_diff_singleton_empty -> Set.mem_diff_singleton_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} (Set.{u1} α)}, Iff (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.booleanAlgebra.{u1} (Set.{u1} α))) t (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasSingleton.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))))) (And (Membership.Mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.hasMem.{u1} (Set.{u1} α)) s t) (Set.Nonempty.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} (Set.{u1} α)}, Iff (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s (SDiff.sdiff.{u1} (Set.{u1} (Set.{u1} α)) (Set.instSDiffSet.{u1} (Set.{u1} α)) t (Singleton.singleton.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instSingletonSet.{u1} (Set.{u1} α)) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))))) (And (Membership.mem.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (Set.instMembershipSet.{u1} (Set.{u1} α)) s t) (Set.Nonempty.{u1} α s))
Case conversion may be inaccurate. Consider using '#align set.mem_diff_singleton_empty Set.mem_diff_singleton_emptyₓ'. -/
theorem mem_diff_singleton_empty {t : Set (Set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.Nonempty :=
  mem_diff_singleton.trans <| and_congr_right' nonempty_iff_ne_empty.symm
#align set.mem_diff_singleton_empty Set.mem_diff_singleton_empty

/- warning: set.union_eq_diff_union_diff_union_inter -> Set.union_eq_diff_union_diff_union_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.union_eq_diff_union_diff_union_inter Set.union_eq_diff_union_diff_union_interₓ'. -/
theorem union_eq_diff_union_diff_union_inter (s t : Set α) : s ∪ t = s \ t ∪ t \ s ∪ s ∩ t :=
  sup_eq_sdiff_sup_sdiff_sup_inf
#align set.union_eq_diff_union_diff_union_inter Set.union_eq_diff_union_diff_union_inter

/-! ### Symmetric difference -/


/- warning: set.mem_symm_diff -> Set.mem_symmDiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (Or (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t))) (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (Not (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s))))
but is expected to have type
  forall {α : Type.{u1}} {a : α} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t)) (Or (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t))) (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (Not (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s))))
Case conversion may be inaccurate. Consider using '#align set.mem_symm_diff Set.mem_symmDiffₓ'. -/
theorem mem_symmDiff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s :=
  Iff.rfl
#align set.mem_symm_diff Set.mem_symmDiff

/- warning: set.symm_diff_def -> Set.symmDiff_def is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) t s))
Case conversion may be inaccurate. Consider using '#align set.symm_diff_def Set.symmDiff_defₓ'. -/
protected theorem symmDiff_def (s t : Set α) : s ∆ t = s \ t ∪ t \ s :=
  rfl
#align set.symm_diff_def Set.symmDiff_def

/- warning: set.symm_diff_subset_union -> Set.symmDiff_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.symm_diff_subset_union Set.symmDiff_subset_unionₓ'. -/
theorem symmDiff_subset_union : s ∆ t ⊆ s ∪ t :=
  @symmDiff_le_sup (Set α) _ _ _
#align set.symm_diff_subset_union Set.symmDiff_subset_union

/- warning: set.symm_diff_eq_empty -> Set.symmDiff_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Eq.{succ u1} (Set.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Eq.{succ u1} (Set.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.symm_diff_eq_empty Set.symmDiff_eq_emptyₓ'. -/
@[simp]
theorem symmDiff_eq_empty : s ∆ t = ∅ ↔ s = t :=
  symmDiff_eq_bot
#align set.symm_diff_eq_empty Set.symmDiff_eq_empty

/- warning: set.symm_diff_nonempty -> Set.symmDiff_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)) (Ne.{succ u1} (Set.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.Nonempty.{u1} α (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t)) (Ne.{succ u1} (Set.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.symm_diff_nonempty Set.symmDiff_nonemptyₓ'. -/
@[simp]
theorem symmDiff_nonempty : (s ∆ t).Nonempty ↔ s ≠ t :=
  nonempty_iff_ne_empty.trans symmDiff_eq_empty.Not
#align set.symm_diff_nonempty Set.symmDiff_nonempty

/- warning: set.inter_symm_diff_distrib_left -> Set.inter_symmDiff_distrib_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t u)) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) t u)) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u))
Case conversion may be inaccurate. Consider using '#align set.inter_symm_diff_distrib_left Set.inter_symmDiff_distrib_leftₓ'. -/
theorem inter_symmDiff_distrib_left (s t u : Set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
  inf_symmDiff_distrib_left _ _ _
#align set.inter_symm_diff_distrib_left Set.inter_symmDiff_distrib_left

/- warning: set.inter_symm_diff_distrib_right -> Set.inter_symmDiff_distrib_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) u) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (u : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) u) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align set.inter_symm_diff_distrib_right Set.inter_symmDiff_distrib_rightₓ'. -/
theorem inter_symmDiff_distrib_right (s t u : Set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
  inf_symmDiff_distrib_right _ _ _
#align set.inter_symm_diff_distrib_right Set.inter_symmDiff_distrib_right

/- warning: set.subset_symm_diff_union_symm_diff_left -> Set.subset_symmDiff_union_symmDiff_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t u)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) u (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s u) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) t u)))
Case conversion may be inaccurate. Consider using '#align set.subset_symm_diff_union_symm_diff_left Set.subset_symmDiff_union_symmDiff_leftₓ'. -/
theorem subset_symmDiff_union_symmDiff_left (h : Disjoint s t) : u ⊆ s ∆ u ∪ t ∆ u :=
  h.le_symm_diff_sup_symm_diff_left
#align set.subset_symm_diff_union_symm_diff_left Set.subset_symmDiff_union_symmDiff_left

/- warning: set.subset_symm_diff_union_symm_diff_right -> Set.subset_symmDiff_union_symmDiff_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s u)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s t) (symmDiff.{u1} (Set.{u1} α) (SemilatticeSup.toHasSup.{u1} (Set.{u1} α) (Lattice.toSemilatticeSup.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (Set.instSDiffSet.{u1} α) s u)))
Case conversion may be inaccurate. Consider using '#align set.subset_symm_diff_union_symm_diff_right Set.subset_symmDiff_union_symmDiff_rightₓ'. -/
theorem subset_symmDiff_union_symmDiff_right (h : Disjoint t u) : s ⊆ s ∆ t ∪ s ∆ u :=
  h.le_symm_diff_sup_symm_diff_right
#align set.subset_symm_diff_union_symm_diff_right Set.subset_symmDiff_union_symmDiff_right

/-! ### Powerset -/


#print Set.powerset /-
/-- `𝒫 s = set.powerset s` is the set of all subsets of `s`. -/
def powerset (s : Set α) : Set (Set α) :=
  { t | t ⊆ s }
#align set.powerset Set.powerset
-/

#print Set.mem_powerset /-
theorem mem_powerset {x s : Set α} (h : x ⊆ s) : x ∈ 𝒫 s :=
  h
#align set.mem_powerset Set.mem_powerset
-/

#print Set.subset_of_mem_powerset /-
theorem subset_of_mem_powerset {x s : Set α} (h : x ∈ 𝒫 s) : x ⊆ s :=
  h
#align set.subset_of_mem_powerset Set.subset_of_mem_powerset
-/

#print Set.mem_powerset_iff /-
@[simp]
theorem mem_powerset_iff (x s : Set α) : x ∈ 𝒫 s ↔ x ⊆ s :=
  Iff.rfl
#align set.mem_powerset_iff Set.mem_powerset_iff
-/

/- warning: set.powerset_inter -> Set.powerset_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Set.powerset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.hasInter.{u1} (Set.{u1} α)) (Set.powerset.{u1} α s) (Set.powerset.{u1} α t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} (Set.{u1} α)) (Set.powerset.{u1} α (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)) (Inter.inter.{u1} (Set.{u1} (Set.{u1} α)) (Set.instInterSet.{u1} (Set.{u1} α)) (Set.powerset.{u1} α s) (Set.powerset.{u1} α t))
Case conversion may be inaccurate. Consider using '#align set.powerset_inter Set.powerset_interₓ'. -/
theorem powerset_inter (s t : Set α) : 𝒫(s ∩ t) = 𝒫 s ∩ 𝒫 t :=
  ext fun u => subset_inter_iff
#align set.powerset_inter Set.powerset_inter

#print Set.powerset_mono /-
@[simp]
theorem powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
  ⟨fun h => h (Subset.refl s), fun h u hu => Subset.trans hu h⟩
#align set.powerset_mono Set.powerset_mono
-/

/- warning: set.monotone_powerset -> Set.monotone_powerset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Set.{u1} α)) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} (Set.{u1} α)) (Set.booleanAlgebra.{u1} (Set.{u1} α)))))))) (Set.powerset.{u1} α)
but is expected to have type
  forall {α : Type.{u1}}, Monotone.{u1, u1} (Set.{u1} α) (Set.{u1} (Set.{u1} α)) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (PartialOrder.toPreorder.{u1} (Set.{u1} (Set.{u1} α)) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Set.{u1} α)) (Lattice.toSemilatticeInf.{u1} (Set.{u1} (Set.{u1} α)) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} (Set.{u1} α)) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} (Set.{u1} α)) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} (Set.{u1} α)) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} (Set.{u1} α)) (Set.instBooleanAlgebraSet.{u1} (Set.{u1} α))))))))) (Set.powerset.{u1} α)
Case conversion may be inaccurate. Consider using '#align set.monotone_powerset Set.monotone_powersetₓ'. -/
theorem monotone_powerset : Monotone (powerset : Set α → Set (Set α)) := fun s t => powerset_mono.2
#align set.monotone_powerset Set.monotone_powerset

#print Set.powerset_nonempty /-
@[simp]
theorem powerset_nonempty : (𝒫 s).Nonempty :=
  ⟨∅, empty_subset s⟩
#align set.powerset_nonempty Set.powerset_nonempty
-/

#print Set.powerset_empty /-
@[simp]
theorem powerset_empty : 𝒫(∅ : Set α) = {∅} :=
  ext fun s => subset_empty_iff
#align set.powerset_empty Set.powerset_empty
-/

#print Set.powerset_univ /-
@[simp]
theorem powerset_univ : 𝒫(univ : Set α) = univ :=
  eq_univ_of_forall subset_univ
#align set.powerset_univ Set.powerset_univ
-/

/-! ### Sets defined as an if-then-else -/


#print Set.mem_dite_univ_right /-
theorem mem_dite_univ_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else univ) ↔ ∀ h : p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_univ_right Set.mem_dite_univ_right
-/

#print Set.mem_ite_univ_right /-
@[simp]
theorem mem_ite_univ_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t Set.univ ↔ p → x ∈ t :=
  mem_dite_univ_right p (fun _ => t) x
#align set.mem_ite_univ_right Set.mem_ite_univ_right
-/

#print Set.mem_dite_univ_left /-
theorem mem_dite_univ_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then univ else t h) ↔ ∀ h : ¬p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_univ_left Set.mem_dite_univ_left
-/

#print Set.mem_ite_univ_left /-
@[simp]
theorem mem_ite_univ_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p Set.univ t ↔ ¬p → x ∈ t :=
  mem_dite_univ_left p (fun _ => t) x
#align set.mem_ite_univ_left Set.mem_ite_univ_left
-/

#print Set.mem_dite_empty_right /-
theorem mem_dite_empty_right (p : Prop) [Decidable p] (t : p → Set α) (x : α) :
    (x ∈ if h : p then t h else ∅) ↔ ∃ h : p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_empty_right Set.mem_dite_empty_right
-/

#print Set.mem_ite_empty_right /-
@[simp]
theorem mem_ite_empty_right (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p t ∅ ↔ p ∧ x ∈ t := by split_ifs <;> simp [h]
#align set.mem_ite_empty_right Set.mem_ite_empty_right
-/

#print Set.mem_dite_empty_left /-
theorem mem_dite_empty_left (p : Prop) [Decidable p] (t : ¬p → Set α) (x : α) :
    (x ∈ if h : p then ∅ else t h) ↔ ∃ h : ¬p, x ∈ t h := by split_ifs <;> simp [h]
#align set.mem_dite_empty_left Set.mem_dite_empty_left
-/

#print Set.mem_ite_empty_left /-
@[simp]
theorem mem_ite_empty_left (p : Prop) [Decidable p] (t : Set α) (x : α) :
    x ∈ ite p ∅ t ↔ ¬p ∧ x ∈ t := by split_ifs <;> simp [h]
#align set.mem_ite_empty_left Set.mem_ite_empty_left
-/

/-! ### If-then-else for sets -/


#print Set.ite /-
/-- `ite` for sets: `set.ite t s s' ∩ t = s ∩ t`, `set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : Set α) : Set α :=
  s ∩ t ∪ s' \ t
#align set.ite Set.ite
-/

/- warning: set.ite_inter_self -> Set.ite_inter_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s s') t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s s') t) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.ite_inter_self Set.ite_inter_selfₓ'. -/
@[simp]
theorem ite_inter_self (t s s' : Set α) : t.ite s s' ∩ t = s ∩ t := by
  rw [Set.ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]
#align set.ite_inter_self Set.ite_inter_self

/- warning: set.ite_compl -> Set.ite_compl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t) s s') (Set.ite.{u1} α t s' s)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t) s s') (Set.ite.{u1} α t s' s)
Case conversion may be inaccurate. Consider using '#align set.ite_compl Set.ite_complₓ'. -/
@[simp]
theorem ite_compl (t s s' : Set α) : tᶜ.ite s s' = t.ite s' s := by
  rw [Set.ite, Set.ite, diff_compl, union_comm, diff_eq]
#align set.ite_compl Set.ite_compl

/- warning: set.ite_inter_compl_self -> Set.ite_inter_compl_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s s') (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s' (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) t))
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s s') (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s' (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) t))
Case conversion may be inaccurate. Consider using '#align set.ite_inter_compl_self Set.ite_inter_compl_selfₓ'. -/
@[simp]
theorem ite_inter_compl_self (t s s' : Set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ := by
  rw [← ite_compl, ite_inter_self]
#align set.ite_inter_compl_self Set.ite_inter_compl_self

/- warning: set.ite_diff_self -> Set.ite_diff_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) (Set.ite.{u1} α t s s') t) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s' t)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) (Set.ite.{u1} α t s s') t) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s' t)
Case conversion may be inaccurate. Consider using '#align set.ite_diff_self Set.ite_diff_selfₓ'. -/
@[simp]
theorem ite_diff_self (t s s' : Set α) : t.ite s s' \ t = s' \ t :=
  ite_inter_compl_self t s s'
#align set.ite_diff_self Set.ite_diff_self

#print Set.ite_same /-
@[simp]
theorem ite_same (t s : Set α) : t.ite s s = s :=
  inter_union_diff _ _
#align set.ite_same Set.ite_same
-/

/- warning: set.ite_left -> Set.ite_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α s s t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α s s t) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.ite_left Set.ite_leftₓ'. -/
@[simp]
theorem ite_left (s t : Set α) : s.ite s t = s ∪ t := by simp [Set.ite]
#align set.ite_left Set.ite_left

/- warning: set.ite_right -> Set.ite_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α s t s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t s)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α s t s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t s)
Case conversion may be inaccurate. Consider using '#align set.ite_right Set.ite_rightₓ'. -/
@[simp]
theorem ite_right (s t : Set α) : s.ite t s = t ∩ s := by simp [Set.ite]
#align set.ite_right Set.ite_right

#print Set.ite_empty /-
@[simp]
theorem ite_empty (s s' : Set α) : Set.ite ∅ s s' = s' := by simp [Set.ite]
#align set.ite_empty Set.ite_empty
-/

#print Set.ite_univ /-
@[simp]
theorem ite_univ (s s' : Set α) : Set.ite univ s s' = s := by simp [Set.ite]
#align set.ite_univ Set.ite_univ
-/

/- warning: set.ite_empty_left -> Set.ite_empty_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α)) s) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α)) s) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.ite_empty_left Set.ite_empty_leftₓ'. -/
@[simp]
theorem ite_empty_left (t s : Set α) : t.ite ∅ s = s \ t := by simp [Set.ite]
#align set.ite_empty_left Set.ite_empty_left

/- warning: set.ite_empty_right -> Set.ite_empty_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t s (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align set.ite_empty_right Set.ite_empty_rightₓ'. -/
@[simp]
theorem ite_empty_right (t s : Set α) : t.ite s ∅ = s ∩ t := by simp [Set.ite]
#align set.ite_empty_right Set.ite_empty_right

#print Set.ite_mono /-
theorem ite_mono (t : Set α) {s₁ s₁' s₂ s₂' : Set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
    t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
  union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')
#align set.ite_mono Set.ite_mono
-/

/- warning: set.ite_subset_union -> Set.ite_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Set.ite.{u1} α t s s') (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s s')
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Set.ite.{u1} α t s s') (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s s')
Case conversion may be inaccurate. Consider using '#align set.ite_subset_union Set.ite_subset_unionₓ'. -/
theorem ite_subset_union (t s s' : Set α) : t.ite s s' ⊆ s ∪ s' :=
  union_subset_union (inter_subset_left _ _) (diff_subset _ _)
#align set.ite_subset_union Set.ite_subset_union

/- warning: set.inter_subset_ite -> Set.inter_subset_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s s') (Set.ite.{u1} α t s s')
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s : Set.{u1} α) (s' : Set.{u1} α), HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s s') (Set.ite.{u1} α t s s')
Case conversion may be inaccurate. Consider using '#align set.inter_subset_ite Set.inter_subset_iteₓ'. -/
theorem inter_subset_ite (t s s' : Set α) : s ∩ s' ⊆ t.ite s s' :=
  ite_same t (s ∩ s') ▸ ite_mono _ (inter_subset_left _ _) (inter_subset_right _ _)
#align set.inter_subset_ite Set.inter_subset_ite

/- warning: set.ite_inter_inter -> Set.ite_inter_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₁' : Set.{u1} α) (s₂' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁' s₂')) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s₁ s₁') (Set.ite.{u1} α t s₂ s₂'))
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s₁' : Set.{u1} α) (s₂' : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁' s₂')) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s₁ s₁') (Set.ite.{u1} α t s₂ s₂'))
Case conversion may be inaccurate. Consider using '#align set.ite_inter_inter Set.ite_inter_interₓ'. -/
theorem ite_inter_inter (t s₁ s₂ s₁' s₂' : Set α) :
    t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' :=
  by
  ext x
  simp only [Set.ite, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
  itauto
#align set.ite_inter_inter Set.ite_inter_inter

/- warning: set.ite_inter -> Set.ite_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ s)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s₁ s₂) s)
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) (s₁ : Set.{u1} α) (s₂ : Set.{u1} α) (s : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (Set.ite.{u1} α t (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₂ s)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s₁ s₂) s)
Case conversion may be inaccurate. Consider using '#align set.ite_inter Set.ite_interₓ'. -/
theorem ite_inter (t s₁ s₂ s : Set α) : t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s := by
  rw [ite_inter_inter, ite_same]
#align set.ite_inter Set.ite_inter

/- warning: set.ite_inter_of_inter_eq -> Set.ite_inter_of_inter_eq is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (t : Set.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₂ s)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.ite.{u1} α t s₁ s₂) s) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s))
but is expected to have type
  forall {α : Type.{u1}} (t : Set.{u1} α) {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {s : Set.{u1} α}, (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₂ s)) -> (Eq.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.ite.{u1} α t s₁ s₂) s) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s))
Case conversion may be inaccurate. Consider using '#align set.ite_inter_of_inter_eq Set.ite_inter_of_inter_eqₓ'. -/
theorem ite_inter_of_inter_eq (t : Set α) {s₁ s₂ s : Set α} (h : s₁ ∩ s = s₂ ∩ s) :
    t.ite s₁ s₂ ∩ s = s₁ ∩ s := by rw [← ite_inter, ← h, ite_same]
#align set.ite_inter_of_inter_eq Set.ite_inter_of_inter_eq

/- warning: set.subset_ite -> Set.subset_ite is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {t : Set.{u1} α} {s : Set.{u1} α} {s' : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) u (Set.ite.{u1} α t s s')) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) u t) s'))
but is expected to have type
  forall {α : Type.{u1}} {t : Set.{u1} α} {s : Set.{u1} α} {s' : Set.{u1} α} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) u (Set.ite.{u1} α t s s')) (And (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u t) s) (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) u t) s'))
Case conversion may be inaccurate. Consider using '#align set.subset_ite Set.subset_iteₓ'. -/
theorem subset_ite {t s s' u : Set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' :=
  by
  simp only [subset_def, ← forall_and]
  refine' forall_congr' fun x => _
  by_cases hx : x ∈ t <;> simp [*, Set.ite]
#align set.subset_ite Set.subset_ite

/-! ### Subsingleton -/


#print Set.Subsingleton /-
/-- A set `s` is a `subsingleton` if it has at most one element. -/
protected def Subsingleton (s : Set α) : Prop :=
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y
#align set.subsingleton Set.Subsingleton
-/

#print Set.Subsingleton.anti /-
theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s ⊆ t) : s.Subsingleton := fun x hx y hy =>
  ht (hst hx) (hst hy)
#align set.subsingleton.anti Set.Subsingleton.anti
-/

#print Set.Subsingleton.eq_singleton_of_mem /-
theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x ∈ s) : s = {x} :=
  ext fun y => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩
#align set.subsingleton.eq_singleton_of_mem Set.Subsingleton.eq_singleton_of_mem
-/

#print Set.subsingleton_empty /-
@[simp]
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun x => False.elim
#align set.subsingleton_empty Set.subsingleton_empty
-/

#print Set.subsingleton_singleton /-
@[simp]
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun x hx y hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
#align set.subsingleton_singleton Set.subsingleton_singleton
-/

#print Set.subsingleton_of_subset_singleton /-
theorem subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h
#align set.subsingleton_of_subset_singleton Set.subsingleton_of_subset_singleton
-/

#print Set.subsingleton_of_forall_eq /-
theorem subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.Subsingleton := fun b hb c hc =>
  (h _ hb).trans (h _ hc).symm
#align set.subsingleton_of_forall_eq Set.subsingleton_of_forall_eq
-/

#print Set.subsingleton_iff_singleton /-
theorem subsingleton_iff_singleton {x} (hx : x ∈ s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩
#align set.subsingleton_iff_singleton Set.subsingleton_iff_singleton
-/

#print Set.Subsingleton.eq_empty_or_singleton /-
theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ ∃ x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩
#align set.subsingleton.eq_empty_or_singleton Set.Subsingleton.eq_empty_or_singleton
-/

#print Set.Subsingleton.induction_on /-
theorem Subsingleton.induction_on {p : Set α → Prop} (hs : s.Subsingleton) (he : p ∅)
    (h₁ : ∀ x, p {x}) : p s :=
  by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts[he, h₁ _]
#align set.subsingleton.induction_on Set.Subsingleton.induction_on
-/

#print Set.subsingleton_univ /-
theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x hx y hy =>
  Subsingleton.elim x y
#align set.subsingleton_univ Set.subsingleton_univ
-/

#print Set.subsingleton_of_univ_subsingleton /-
theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩
#align set.subsingleton_of_univ_subsingleton Set.subsingleton_of_univ_subsingleton
-/

#print Set.subsingleton_univ_iff /-
@[simp]
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩
#align set.subsingleton_univ_iff Set.subsingleton_univ_iff
-/

#print Set.subsingleton_of_subsingleton /-
theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : Set.Subsingleton s :=
  subsingleton_univ.anti (subset_univ s)
#align set.subsingleton_of_subsingleton Set.subsingleton_of_subsingleton
-/

#print Set.subsingleton_isTop /-
theorem subsingleton_isTop (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsTop x } :=
  fun x hx y hy => hx.IsMax.eq_of_le (hy x)
#align set.subsingleton_is_top Set.subsingleton_isTop
-/

#print Set.subsingleton_isBot /-
theorem subsingleton_isBot (α : Type _) [PartialOrder α] : Set.Subsingleton { x : α | IsBot x } :=
  fun x hx y hy => hx.IsMin.eq_of_ge (hy x)
#align set.subsingleton_is_bot Set.subsingleton_isBot
-/

#print Set.exists_eq_singleton_iff_nonempty_subsingleton /-
theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (∃ a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton :=
  by
  refine' ⟨_, fun h => _⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty
#align
  set.exists_eq_singleton_iff_nonempty_subsingleton Set.exists_eq_singleton_iff_nonempty_subsingleton
-/

#print Set.subsingleton_coe /-
/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton :=
  by
  constructor
  · refine' fun h => fun a ha b hb => _
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)
#align set.subsingleton_coe Set.subsingleton_coe
-/

#print Set.Subsingleton.coe_sort /-
theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton → Subsingleton s :=
  s.subsingleton_coe.2
#align set.subsingleton.coe_sort Set.Subsingleton.coe_sort
-/

#print Set.subsingleton_coe_of_subsingleton /-
/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s :=
  by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton
#align set.subsingleton_coe_of_subsingleton Set.subsingleton_coe_of_subsingleton
-/

/-! ### Nontrivial -/


/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Nontrivial /-
/-- A set `s` is `nontrivial` if it has at least two distinct elements. -/
protected def Nontrivial (s : Set α) : Prop :=
  ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), x ≠ y
#align set.nontrivial Set.Nontrivial
-/

#print Set.nontrivial_of_mem_mem_ne /-
theorem nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩
#align set.nontrivial_of_mem_mem_ne Set.nontrivial_of_mem_mem_ne
-/

#print Set.Nontrivial.choose /-
/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
protected noncomputable def Nontrivial.choose (hs : s.Nontrivial) : α × α :=
  (hs.some, hs.some_spec.some_spec.some)
#align set.nontrivial.some Set.Nontrivial.choose
-/

#print Set.Nontrivial.choose_fst_mem /-
protected theorem Nontrivial.choose_fst_mem (hs : s.Nontrivial) : hs.some.fst ∈ s :=
  hs.some_spec.some
#align set.nontrivial.some_fst_mem Set.Nontrivial.choose_fst_mem
-/

#print Set.Nontrivial.choose_snd_mem /-
protected theorem Nontrivial.choose_snd_mem (hs : s.Nontrivial) : hs.some.snd ∈ s :=
  hs.some_spec.some_spec.some_spec.some
#align set.nontrivial.some_snd_mem Set.Nontrivial.choose_snd_mem
-/

#print Set.Nontrivial.choose_fst_ne_choose_snd /-
protected theorem Nontrivial.choose_fst_ne_choose_snd (hs : s.Nontrivial) :
    hs.some.fst ≠ hs.some.snd :=
  hs.some_spec.some_spec.some_spec.some_spec
#align set.nontrivial.some_fst_ne_some_snd Set.Nontrivial.choose_fst_ne_choose_snd
-/

#print Set.Nontrivial.mono /-
theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s ⊆ t) : t.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩
#align set.nontrivial.mono Set.Nontrivial.mono
-/

#print Set.nontrivial_pair /-
theorem nontrivial_pair {x y} (hxy : x ≠ y) : ({x, y} : Set α).Nontrivial :=
  ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩
#align set.nontrivial_pair Set.nontrivial_pair
-/

#print Set.nontrivial_of_pair_subset /-
theorem nontrivial_of_pair_subset {x y} (hxy : x ≠ y) (h : {x, y} ⊆ s) : s.Nontrivial :=
  (nontrivial_pair hxy).mono h
#align set.nontrivial_of_pair_subset Set.nontrivial_of_pair_subset
-/

#print Set.Nontrivial.pair_subset /-
theorem Nontrivial.pair_subset (hs : s.Nontrivial) : ∃ (x y : _)(hab : x ≠ y), {x, y} ⊆ s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, y, hxy, insert_subset.2 ⟨hx, singleton_subset_iff.2 hy⟩⟩
#align set.nontrivial.pair_subset Set.Nontrivial.pair_subset
-/

#print Set.nontrivial_iff_pair_subset /-
theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ ∃ (x y : _)(hxy : x ≠ y), {x, y} ⊆ s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨x, y, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩
#align set.nontrivial_iff_pair_subset Set.nontrivial_iff_pair_subset
-/

/- warning: set.nontrivial_of_exists_ne -> Set.nontrivial_of_exists_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Ne.{succ u1} α y x))) -> (Set.Nontrivial.{u1} α s)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (Ne.{succ u1} α y x))) -> (Set.Nontrivial.{u1} α s)
Case conversion may be inaccurate. Consider using '#align set.nontrivial_of_exists_ne Set.nontrivial_of_exists_neₓ'. -/
theorem nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩
#align set.nontrivial_of_exists_ne Set.nontrivial_of_exists_ne

/- warning: set.nontrivial.exists_ne -> Set.Nontrivial.exists_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (forall (z : α), Exists.{succ u1} α (fun (x : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) => Ne.{succ u1} α x z)))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (forall (z : α), Exists.{succ u1} α (fun (x : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) (Ne.{succ u1} α x z)))
Case conversion may be inaccurate. Consider using '#align set.nontrivial.exists_ne Set.Nontrivial.exists_neₓ'. -/
theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : ∃ x ∈ s, x ≠ z :=
  by
  by_contra H; push_neg  at H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx, H y hy] at hxy
  exact hxy rfl
#align set.nontrivial.exists_ne Set.Nontrivial.exists_ne

/- warning: set.nontrivial_iff_exists_ne -> Set.nontrivial_iff_exists_ne is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Iff (Set.Nontrivial.{u1} α s) (Exists.{succ u1} α (fun (y : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) y s) => Ne.{succ u1} α y x))))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {x : α}, (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Iff (Set.Nontrivial.{u1} α s) (Exists.{succ u1} α (fun (y : α) => And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) y s) (Ne.{succ u1} α y x))))
Case conversion may be inaccurate. Consider using '#align set.nontrivial_iff_exists_ne Set.nontrivial_iff_exists_neₓ'. -/
theorem nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.Nontrivial ↔ ∃ y ∈ s, y ≠ x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩
#align set.nontrivial_iff_exists_ne Set.nontrivial_iff_exists_ne

#print Set.nontrivial_of_lt /-
theorem nontrivial_of_lt [Preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) :
    s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩
#align set.nontrivial_of_lt Set.nontrivial_of_lt
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.nontrivial_of_exists_lt /-
theorem nontrivial_of_exists_lt [Preorder α] (H : ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), x < y) :
    s.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy
#align set.nontrivial_of_exists_lt Set.nontrivial_of_exists_lt
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.Nontrivial.exists_lt /-
theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) :
    ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩
#align set.nontrivial.exists_lt Set.Nontrivial.exists_lt
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
#print Set.nontrivial_iff_exists_lt /-
theorem nontrivial_iff_exists_lt [LinearOrder α] :
    s.Nontrivial ↔ ∃ (x : _)(_ : x ∈ s)(y : _)(_ : y ∈ s), x < y :=
  ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩
#align set.nontrivial_iff_exists_lt Set.nontrivial_iff_exists_lt
-/

#print Set.Nontrivial.nonempty /-
protected theorem Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty :=
  let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩
#align set.nontrivial.nonempty Set.Nontrivial.nonempty
-/

#print Set.Nontrivial.ne_empty /-
protected theorem Nontrivial.ne_empty (hs : s.Nontrivial) : s ≠ ∅ :=
  hs.Nonempty.ne_empty
#align set.nontrivial.ne_empty Set.Nontrivial.ne_empty
-/

#print Set.Nontrivial.not_subset_empty /-
theorem Nontrivial.not_subset_empty (hs : s.Nontrivial) : ¬s ⊆ ∅ :=
  hs.Nonempty.not_subset_empty
#align set.nontrivial.not_subset_empty Set.Nontrivial.not_subset_empty
-/

#print Set.not_nontrivial_empty /-
@[simp]
theorem not_nontrivial_empty : ¬(∅ : Set α).Nontrivial := fun h => h.ne_empty rfl
#align set.not_nontrivial_empty Set.not_nontrivial_empty
-/

#print Set.not_nontrivial_singleton /-
@[simp]
theorem not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial := fun H =>
  by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  exact
    let ⟨y, hy, hya⟩ := H
    hya (mem_singleton_iff.1 hy)
#align set.not_nontrivial_singleton Set.not_nontrivial_singleton
-/

#print Set.Nontrivial.ne_singleton /-
theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s ≠ {x} := fun H =>
  by
  rw [H] at hs
  exact not_nontrivial_singleton hs
#align set.nontrivial.ne_singleton Set.Nontrivial.ne_singleton
-/

#print Set.Nontrivial.not_subset_singleton /-
theorem Nontrivial.not_subset_singleton {x} (hs : s.Nontrivial) : ¬s ⊆ {x} :=
  (not_congr subset_singleton_iff_eq).2 (not_or_of_not hs.ne_empty hs.ne_singleton)
#align set.nontrivial.not_subset_singleton Set.Nontrivial.not_subset_singleton
-/

#print Set.nontrivial_univ /-
theorem nontrivial_univ [Nontrivial α] : (univ : Set α).Nontrivial :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩
#align set.nontrivial_univ Set.nontrivial_univ
-/

#print Set.nontrivial_of_univ_nontrivial /-
theorem nontrivial_of_univ_nontrivial (h : (univ : Set α).Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩
#align set.nontrivial_of_univ_nontrivial Set.nontrivial_of_univ_nontrivial
-/

#print Set.nontrivial_univ_iff /-
@[simp]
theorem nontrivial_univ_iff : (univ : Set α).Nontrivial ↔ Nontrivial α :=
  ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩
#align set.nontrivial_univ_iff Set.nontrivial_univ_iff
-/

#print Set.nontrivial_of_nontrivial /-
theorem nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩
#align set.nontrivial_of_nontrivial Set.nontrivial_of_nontrivial
-/

#print Set.nontrivial_coe_sort /-
/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  simp_rw [← nontrivial_univ_iff, Set.Nontrivial, mem_univ, exists_true_left, SetCoe.exists,
    Subtype.mk_eq_mk]
#align set.nontrivial_coe_sort Set.nontrivial_coe_sort
-/

alias nontrivial_coe_sort ↔ _ nontrivial.coe_sort
#align set.nontrivial.coe_sort Set.Nontrivial.coe_sort

#print Set.nontrivial_of_nontrivial_coe /-
/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `subtype`, see `subtype.nontrivial_iff_exists_ne`. -/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
  nontrivial_of_nontrivial <| nontrivial_coe_sort.1 hs
#align set.nontrivial_of_nontrivial_coe Set.nontrivial_of_nontrivial_coe
-/

#print Set.nontrivial_mono /-
theorem nontrivial_mono {α : Type _} {s t : Set α} (hst : s ⊆ t) (hs : Nontrivial s) :
    Nontrivial t :=
  nontrivial.coe_sort <| (nontrivial_coe_sort.1 hs).mono hst
#align set.nontrivial_mono Set.nontrivial_mono
-/

#print Set.not_subsingleton_iff /-
@[simp]
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall]
#align set.not_subsingleton_iff Set.not_subsingleton_iff
-/

#print Set.not_nontrivial_iff /-
@[simp]
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm
#align set.not_nontrivial_iff Set.not_nontrivial_iff
-/

alias not_nontrivial_iff ↔ _ subsingleton.not_nontrivial
#align set.subsingleton.not_nontrivial Set.Subsingleton.not_nontrivial

alias not_subsingleton_iff ↔ _ nontrivial.not_subsingleton
#align set.nontrivial.not_subsingleton Set.Nontrivial.not_subsingleton

#print Set.subsingleton_or_nontrivial /-
protected theorem subsingleton_or_nontrivial (s : Set α) : s.Subsingleton ∨ s.Nontrivial := by
  simp [or_iff_not_imp_right]
#align set.subsingleton_or_nontrivial Set.subsingleton_or_nontrivial
-/

#print Set.eq_singleton_or_nontrivial /-
theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial :=
  by
  rw [← subsingleton_iff_singleton ha]
  exact s.subsingleton_or_nontrivial
#align set.eq_singleton_or_nontrivial Set.eq_singleton_or_nontrivial
-/

#print Set.nontrivial_iff_ne_singleton /-
theorem nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩
#align set.nontrivial_iff_ne_singleton Set.nontrivial_iff_ne_singleton
-/

#print Set.Nonempty.exists_eq_singleton_or_nontrivial /-
theorem Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a
#align set.nonempty.exists_eq_singleton_or_nontrivial Set.Nonempty.exists_eq_singleton_or_nontrivial
-/

#print Set.univ_eq_true_false /-
theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
  Eq.symm <| eq_univ_of_forall <| Classical.cases (by simp) (by simp)
#align set.univ_eq_true_false Set.univ_eq_true_false
-/

section Preorder

variable [Preorder α] [Preorder β] {f : α → β}

#print Set.monotoneOn_iff_monotone /-
theorem monotoneOn_iff_monotone : MonotoneOn f s ↔ Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]
#align set.monotone_on_iff_monotone Set.monotoneOn_iff_monotone
-/

#print Set.antitoneOn_iff_antitone /-
theorem antitoneOn_iff_antitone : AntitoneOn f s ↔ Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]
#align set.antitone_on_iff_antitone Set.antitoneOn_iff_antitone
-/

#print Set.strictMonoOn_iff_strictMono /-
theorem strictMonoOn_iff_strictMono : StrictMonoOn f s ↔ StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]
#align set.strict_mono_on_iff_strict_mono Set.strictMonoOn_iff_strictMono
-/

#print Set.strictAntiOn_iff_strictAnti /-
theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔ StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]
#align set.strict_anti_on_iff_strict_anti Set.strictAntiOn_iff_strictAnti
-/

variable (f)

/-! ### Monotonicity on singletons -/


#print Set.Subsingleton.monotoneOn /-
protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun a ha b hb _ => (congr_arg _ (h ha hb)).le
#align set.subsingleton.monotone_on Set.Subsingleton.monotoneOn
-/

#print Set.Subsingleton.antitoneOn /-
protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun a ha b hb _ => (congr_arg _ (h hb ha)).le
#align set.subsingleton.antitone_on Set.Subsingleton.antitoneOn
-/

#print Set.Subsingleton.strictMonoOn /-
protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun a ha b hb hlt => (hlt.Ne (h ha hb)).elim
#align set.subsingleton.strict_mono_on Set.Subsingleton.strictMonoOn
-/

#print Set.Subsingleton.strictAntiOn /-
protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun a ha b hb hlt => (hlt.Ne (h ha hb)).elim
#align set.subsingleton.strict_anti_on Set.Subsingleton.strictAntiOn
-/

#print Set.monotoneOn_singleton /-
@[simp]
theorem monotoneOn_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.MonotoneOn f
#align set.monotone_on_singleton Set.monotoneOn_singleton
-/

#print Set.antitoneOn_singleton /-
@[simp]
theorem antitoneOn_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.AntitoneOn f
#align set.antitone_on_singleton Set.antitoneOn_singleton
-/

#print Set.strictMonoOn_singleton /-
@[simp]
theorem strictMonoOn_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.StrictMonoOn f
#align set.strict_mono_on_singleton Set.strictMonoOn_singleton
-/

#print Set.strictAntiOn_singleton /-
@[simp]
theorem strictAntiOn_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.StrictAntiOn f
#align set.strict_anti_on_singleton Set.strictAntiOn_singleton
-/

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β}

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b c «expr ∈ » s) -/
#print Set.not_monotoneOn_not_antitoneOn_iff_exists_le_le /-
/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a : _)(_ : a ∈ s)(b : _)(_ : b ∈ s)(c : _)(_ : c ∈ s),
        a ≤ b ∧ b ≤ c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
  by
  simp [monotone_on_iff_monotone, antitone_on_iff_antitone, and_assoc', exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ ∈ s)]
#align
  set.not_monotone_on_not_antitone_on_iff_exists_le_le Set.not_monotoneOn_not_antitoneOn_iff_exists_le_le
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (a b c «expr ∈ » s) -/
#print Set.not_monotoneOn_not_antitoneOn_iff_exists_lt_lt /-
/-- A function between linear orders which is neither monotone nor antitone makes a dent upright or
downright. -/
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      ∃ (a : _)(_ : a ∈ s)(b : _)(_ : b ∈ s)(c : _)(_ : c ∈ s),
        a < b ∧ b < c ∧ (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) :=
  by
  simp [monotone_on_iff_monotone, antitone_on_iff_antitone, and_assoc', exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ ∈ s)]
#align
  set.not_monotone_on_not_antitone_on_iff_exists_lt_lt Set.not_monotoneOn_not_antitoneOn_iff_exists_lt_lt
-/

end LinearOrder

end Set

open Set

namespace Function

variable {ι : Sort _} {α : Type _} {β : Type _} {f : α → β}

/- warning: function.injective.nonempty_apply_iff -> Function.Injective.nonempty_apply_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {f : (Set.{u1} α) -> (Set.{u2} β)}, (Function.Injective.{succ u1, succ u2} (Set.{u1} α) (Set.{u2} β) f) -> (Eq.{succ u2} (Set.{u2} β) (f (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) -> (forall {s : Set.{u1} α}, Iff (Set.Nonempty.{u2} β (f s)) (Set.Nonempty.{u1} α s))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {f : (Set.{u2} α) -> (Set.{u1} β)}, (Function.Injective.{succ u2, succ u1} (Set.{u2} α) (Set.{u1} β) f) -> (Eq.{succ u1} (Set.{u1} β) (f (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) -> (forall {s : Set.{u2} α}, Iff (Set.Nonempty.{u1} β (f s)) (Set.Nonempty.{u2} α s))
Case conversion may be inaccurate. Consider using '#align function.injective.nonempty_apply_iff Function.Injective.nonempty_apply_iffₓ'. -/
theorem Injective.nonempty_apply_iff {f : Set α → Set β} (hf : Injective f) (h2 : f ∅ = ∅)
    {s : Set α} : (f s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]
#align function.injective.nonempty_apply_iff Function.Injective.nonempty_apply_iff

end Function

open Function

namespace Set

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/


section Inclusion

variable {α : Type _} {s t u : Set α}

#print Set.inclusion /-
/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion (h : s ⊆ t) : s → t := fun x : s => (⟨x, h x.2⟩ : t)
#align set.inclusion Set.inclusion
-/

#print Set.inclusion_self /-
@[simp]
theorem inclusion_self (x : s) : inclusion Subset.rfl x = x :=
  by
  cases x
  rfl
#align set.inclusion_self Set.inclusion_self
-/

#print Set.inclusion_eq_id /-
theorem inclusion_eq_id (h : s ⊆ s) : inclusion h = id :=
  funext inclusion_self
#align set.inclusion_eq_id Set.inclusion_eq_id
-/

#print Set.inclusion_mk /-
@[simp]
theorem inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ :=
  rfl
#align set.inclusion_mk Set.inclusion_mk
-/

#print Set.inclusion_right /-
theorem inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x :=
  by
  cases x
  rfl
#align set.inclusion_right Set.inclusion_right
-/

#print Set.inclusion_inclusion /-
@[simp]
theorem inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
    inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x :=
  by
  cases x
  rfl
#align set.inclusion_inclusion Set.inclusion_inclusion
-/

#print Set.inclusion_comp_inclusion /-
@[simp]
theorem inclusion_comp_inclusion {α} {s t u : Set α} (hst : s ⊆ t) (htu : t ⊆ u) :
    inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
  funext (inclusion_inclusion hst htu)
#align set.inclusion_comp_inclusion Set.inclusion_comp_inclusion
-/

#print Set.coe_inclusion /-
@[simp]
theorem coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) :=
  rfl
#align set.coe_inclusion Set.coe_inclusion
-/

#print Set.inclusion_injective /-
theorem inclusion_injective (h : s ⊆ t) : Injective (inclusion h)
  | ⟨_, _⟩, ⟨_, _⟩ => Subtype.ext_iff_val.2 ∘ Subtype.ext_iff_val.1
#align set.inclusion_injective Set.inclusion_injective
-/

#print Set.eq_of_inclusion_surjective /-
theorem eq_of_inclusion_surjective {s t : Set α} {h : s ⊆ t}
    (h_surj : Function.Surjective (inclusion h)) : s = t :=
  by
  refine' Set.Subset.antisymm h fun x hx => _
  obtain ⟨y, hy⟩ := h_surj ⟨x, hx⟩
  exact mem_of_eq_of_mem (congr_arg coe hy).symm y.prop
#align set.eq_of_inclusion_surjective Set.eq_of_inclusion_surjective
-/

end Inclusion

end Set

namespace Subsingleton

variable {α : Type _} [Subsingleton α]

#print Subsingleton.eq_univ_of_nonempty /-
theorem eq_univ_of_nonempty {s : Set α} : s.Nonempty → s = univ := fun ⟨x, hx⟩ =>
  eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
#align subsingleton.eq_univ_of_nonempty Subsingleton.eq_univ_of_nonempty
-/

#print Subsingleton.set_cases /-
@[elab_as_elim]
theorem set_cases {p : Set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
  s.eq_empty_or_nonempty.elim (fun h => h.symm ▸ h0) fun h => (eq_univ_of_nonempty h).symm ▸ h1
#align subsingleton.set_cases Subsingleton.set_cases
-/

#print Subsingleton.mem_iff_nonempty /-
theorem mem_iff_nonempty {α : Type _} [Subsingleton α] {s : Set α} {x : α} : x ∈ s ↔ s.Nonempty :=
  ⟨fun hx => ⟨x, hx⟩, fun ⟨y, hy⟩ => Subsingleton.elim y x ▸ hy⟩
#align subsingleton.mem_iff_nonempty Subsingleton.mem_iff_nonempty
-/

end Subsingleton

/-! ### Decidability instances for sets -/


namespace Set

variable {α : Type u} (s t : Set α) (a : α)

/- warning: set.decidable_sdiff -> Set.decidableSdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)] [_inst_2 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)], Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)] [_inst_2 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)], Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (SDiff.sdiff.{u1} (Set.{u1} α) (Set.instSDiffSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.decidable_sdiff Set.decidableSdiffₓ'. -/
instance decidableSdiff [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s \ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∉ t))
#align set.decidable_sdiff Set.decidableSdiff

/- warning: set.decidable_inter -> Set.decidableInter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)] [_inst_2 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)], Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)] [_inst_2 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)], Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.decidable_inter Set.decidableInterₓ'. -/
instance decidableInter [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∩ t) :=
  (by infer_instance : Decidable (a ∈ s ∧ a ∈ t))
#align set.decidable_inter Set.decidableInter

/- warning: set.decidable_union -> Set.decidableUnion is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)] [_inst_2 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t)], Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (t : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)] [_inst_2 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t)], Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t))
Case conversion may be inaccurate. Consider using '#align set.decidable_union Set.decidableUnionₓ'. -/
instance decidableUnion [Decidable (a ∈ s)] [Decidable (a ∈ t)] : Decidable (a ∈ s ∪ t) :=
  (by infer_instance : Decidable (a ∈ s ∨ a ∈ t))
#align set.decidable_union Set.decidableUnion

/- warning: set.decidable_compl -> Set.decidableCompl is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s)], Decidable (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)) s))
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (a : α) [_inst_1 : Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s)], Decidable (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a (HasCompl.compl.{u1} (Set.{u1} α) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)) s))
Case conversion may be inaccurate. Consider using '#align set.decidable_compl Set.decidableComplₓ'. -/
instance decidableCompl [Decidable (a ∈ s)] : Decidable (a ∈ sᶜ) :=
  (by infer_instance : Decidable (a ∉ s))
#align set.decidable_compl Set.decidableCompl

#print Set.decidableEmptyset /-
instance decidableEmptyset : DecidablePred (· ∈ (∅ : Set α)) := fun _ => Decidable.isFalse (by simp)
#align set.decidable_emptyset Set.decidableEmptyset
-/

#print Set.decidableUniv /-
instance decidableUniv : DecidablePred (· ∈ (Set.univ : Set α)) := fun _ =>
  Decidable.isTrue (by simp)
#align set.decidable_univ Set.decidableUniv
-/

#print Set.decidableSetOf /-
instance decidableSetOf (p : α → Prop) [Decidable (p a)] : Decidable (a ∈ { a | p a }) := by
  assumption
#align set.decidable_set_of Set.decidableSetOf
-/

end Set

/-! ### Monotone lemmas for sets -/


section Monotone

variable {α β : Type _}

/- warning: monotone.inter -> Monotone.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.inter Monotone.interₓ'. -/
theorem Monotone.inter [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∩ g x :=
  hf.inf hg
#align monotone.inter Monotone.inter

/- warning: monotone_on.inter -> MonotoneOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.inter MonotoneOn.interₓ'. -/
theorem MonotoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
#align monotone_on.inter MonotoneOn.inter

/- warning: antitone.inter -> Antitone.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.inter Antitone.interₓ'. -/
theorem Antitone.inter [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∩ g x :=
  hf.inf hg
#align antitone.inter Antitone.inter

/- warning: antitone_on.inter -> AntitoneOn.inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.inter AntitoneOn.interₓ'. -/
theorem AntitoneOn.inter [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∩ g x) s :=
  hf.inf hg
#align antitone_on.inter AntitoneOn.inter

/- warning: monotone.union -> Monotone.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g) -> (Monotone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align monotone.union Monotone.unionₓ'. -/
theorem Monotone.union [Preorder β] {f g : β → Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ∪ g x :=
  hf.sup hg
#align monotone.union Monotone.union

/- warning: monotone_on.union -> MonotoneOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g s) -> (MonotoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align monotone_on.union MonotoneOn.unionₓ'. -/
theorem MonotoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg
#align monotone_on.union MonotoneOn.union

/- warning: antitone.union -> Antitone.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (f x) (g x)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)}, (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g) -> (Antitone.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align antitone.union Antitone.unionₓ'. -/
theorem Antitone.union [Preorder β] {f g : β → Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ∪ g x :=
  hf.sup hg
#align antitone.union Antitone.union

/- warning: antitone_on.union -> AntitoneOn.union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) f s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) g s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (f x) (g x)) s)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u2} β] {f : β -> (Set.{u1} α)} {g : β -> (Set.{u1} α)} {s : Set.{u2} β}, (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) f s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) g s) -> (AntitoneOn.{u2, u1} β (Set.{u1} α) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (fun (x : β) => Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (f x) (g x)) s)
Case conversion may be inaccurate. Consider using '#align antitone_on.union AntitoneOn.unionₓ'. -/
theorem AntitoneOn.union [Preorder β] {f g : β → Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x ∪ g x) s :=
  hf.sup hg
#align antitone_on.union AntitoneOn.union

namespace Set

/- warning: set.monotone_set_of -> Set.monotone_setOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {p : α -> β -> Prop}, (forall (b : β), Monotone.{u1, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (a : α) => p a b)) -> (Monotone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (fun (a : α) => setOf.{u2} β (fun (b : β) => p a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] {p : α -> β -> Prop}, (forall (b : β), Monotone.{u2, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (a : α) => p a b)) -> (Monotone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)))))))) (fun (a : α) => setOf.{u1} β (fun (b : β) => p a b)))
Case conversion may be inaccurate. Consider using '#align set.monotone_set_of Set.monotone_setOfₓ'. -/
theorem monotone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun a a' h b => hp b h
#align set.monotone_set_of Set.monotone_setOf

/- warning: set.antitone_set_of -> Set.antitone_setOf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Preorder.{u1} α] {p : α -> β -> Prop}, (forall (b : β), Antitone.{u1, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (a : α) => p a b)) -> (Antitone.{u1, u2} α (Set.{u2} β) _inst_1 (PartialOrder.toPreorder.{u2} (Set.{u2} β) (SemilatticeInf.toPartialOrder.{u2} (Set.{u2} β) (Lattice.toSemilatticeInf.{u2} (Set.{u2} β) (GeneralizedCoheytingAlgebra.toLattice.{u2} (Set.{u2} β) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u2} (Set.{u2} β) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β))))))) (fun (a : α) => setOf.{u2} β (fun (b : β) => p a b)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Preorder.{u2} α] {p : α -> β -> Prop}, (forall (b : β), Antitone.{u2, 0} α Prop _inst_1 (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (a : α) => p a b)) -> (Antitone.{u2, u1} α (Set.{u1} β) _inst_1 (PartialOrder.toPreorder.{u1} (Set.{u1} β) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} β) (Lattice.toSemilatticeInf.{u1} (Set.{u1} β) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} β) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} β) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} β) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} β) (Set.instBooleanAlgebraSet.{u1} β)))))))) (fun (a : α) => setOf.{u1} β (fun (b : β) => p a b)))
Case conversion may be inaccurate. Consider using '#align set.antitone_set_of Set.antitone_setOfₓ'. -/
theorem antitone_setOf [Preorder α] {p : α → β → Prop} (hp : ∀ b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun a a' h b => hp b h
#align set.antitone_set_of Set.antitone_setOf

/- warning: set.antitone_bforall -> Set.antitone_bforall is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {P : α -> Prop}, Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Set.{u1} α) => forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (P x))
but is expected to have type
  forall {α : Type.{u1}} {P : α -> Prop}, Antitone.{u1, 0} (Set.{u1} α) Prop (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α)))))))) (PartialOrder.toPreorder.{0} Prop Prop.partialOrder) (fun (s : Set.{u1} α) => forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (P x))
Case conversion may be inaccurate. Consider using '#align set.antitone_bforall Set.antitone_bforallₓ'. -/
/-- Quantifying over a set is antitone in the set -/
theorem antitone_bforall {P : α → Prop} : Antitone fun s : Set α => ∀ x ∈ s, P x :=
  fun s t hst h x hx => h x <| hst hx
#align set.antitone_bforall Set.antitone_bforall

end Set

end Monotone

/-! ### Disjoint sets -/


variable {α β : Type _} {s t u : Set α} {f : α → β}

namespace Disjoint

/- warning: disjoint.union_left -> Disjoint.union_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) t u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s t) u)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) t u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s t) u)
Case conversion may be inaccurate. Consider using '#align disjoint.union_left Disjoint.union_leftₓ'. -/
theorem union_left (hs : Disjoint s u) (ht : Disjoint t u) : Disjoint (s ∪ t) u :=
  hs.sup_left ht
#align disjoint.union_left Disjoint.union_left

/- warning: disjoint.union_right -> Disjoint.union_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align disjoint.union_right Disjoint.union_rightₓ'. -/
theorem union_right (ht : Disjoint s t) (hu : Disjoint s u) : Disjoint s (t ∪ u) :=
  ht.sup_right hu
#align disjoint.union_right Disjoint.union_right

/- warning: disjoint.inter_left -> Disjoint.inter_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s u) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s u) t)
Case conversion may be inaccurate. Consider using '#align disjoint.inter_left Disjoint.inter_leftₓ'. -/
theorem inter_left (u : Set α) (h : Disjoint s t) : Disjoint (s ∩ u) t :=
  h.inf_left u
#align disjoint.inter_left Disjoint.inter_left

/- warning: disjoint.inter_left' -> Disjoint.inter_left' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u s) t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u s) t)
Case conversion may be inaccurate. Consider using '#align disjoint.inter_left' Disjoint.inter_left'ₓ'. -/
theorem inter_left' (u : Set α) (h : Disjoint s t) : Disjoint (u ∩ s) t :=
  h.inf_left' _
#align disjoint.inter_left' Disjoint.inter_left'

/- warning: disjoint.inter_right -> Disjoint.inter_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) t u))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) t u))
Case conversion may be inaccurate. Consider using '#align disjoint.inter_right Disjoint.inter_rightₓ'. -/
theorem inter_right (u : Set α) (h : Disjoint s t) : Disjoint s (t ∩ u) :=
  h.inf_right _
#align disjoint.inter_right Disjoint.inter_right

/- warning: disjoint.inter_right' -> Disjoint.inter_right' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) u t))
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} (u : Set.{u1} α), (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) u t))
Case conversion may be inaccurate. Consider using '#align disjoint.inter_right' Disjoint.inter_right'ₓ'. -/
theorem inter_right' (u : Set α) (h : Disjoint s t) : Disjoint s (u ∩ t) :=
  h.inf_right' _
#align disjoint.inter_right' Disjoint.inter_right'

/- warning: disjoint.subset_left_of_subset_union -> Disjoint.subset_left_of_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s u) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s t)
Case conversion may be inaccurate. Consider using '#align disjoint.subset_left_of_subset_union Disjoint.subset_left_of_subset_unionₓ'. -/
theorem subset_left_of_subset_union (h : s ⊆ t ∪ u) (hac : Disjoint s u) : s ⊆ t :=
  hac.left_le_of_le_sup_right h
#align disjoint.subset_left_of_subset_union Disjoint.subset_left_of_subset_union

/- warning: disjoint.subset_right_of_subset_union -> Disjoint.subset_right_of_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) t u)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (GeneralizedBooleanAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s u)
but is expected to have type
  forall {α : Type.{u1}} {s : Set.{u1} α} {t : Set.{u1} α} {u : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) t u)) -> (Disjoint.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (SemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (Lattice.toSemilatticeInf.{u1} (Set.{u1} α) (GeneralizedCoheytingAlgebra.toLattice.{u1} (Set.{u1} α) (CoheytingAlgebra.toGeneralizedCoheytingAlgebra.{u1} (Set.{u1} α) (BiheytingAlgebra.toCoheytingAlgebra.{u1} (Set.{u1} α) (BooleanAlgebra.toBiheytingAlgebra.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))))))))) (BooleanAlgebra.toBoundedOrder.{u1} (Set.{u1} α) (Set.instBooleanAlgebraSet.{u1} α))) s t) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.instHasSubsetSet.{u1} α) s u)
Case conversion may be inaccurate. Consider using '#align disjoint.subset_right_of_subset_union Disjoint.subset_right_of_subset_unionₓ'. -/
theorem subset_right_of_subset_union (h : s ⊆ t ∪ u) (hab : Disjoint s t) : s ⊆ u :=
  hab.left_le_of_le_sup_left h
#align disjoint.subset_right_of_subset_union Disjoint.subset_right_of_subset_union

end Disjoint

