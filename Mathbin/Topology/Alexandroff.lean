/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov

! This file was ported from Lean 3 source module topology.alexandroff
! leanprover-community/mathlib commit bd9851ca476957ea4549eb19b40e7b5ade9428cc
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Option
import Mathbin.Topology.Separation
import Mathbin.Topology.Sets.Opens

/-!
# The Alexandroff Compactification

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We construct the Alexandroff compactification (the one-point compactification) of an arbitrary
topological space `X` and prove some properties inherited from `X`.

## Main definitions

* `alexandroff`: the Alexandroff compactification, we use coercion for the canonical embedding
  `X → alexandroff X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `alexandroff.infty`: the extra point

## Main results

* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for a noncompact, preconnected `X`
* `alexandroff X` is `T₀` for a T₀ space `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is normal if `X` is a locally compact Hausdorff space

## Tags

one-point compactification, compactness
-/


open Set Filter

open Classical Topology Filter

/-!
### Definition and basic properties

In this section we define `alexandroff X` to be the disjoint union of `X` and `∞`, implemented as
`option X`. Then we restate some lemmas about `option X` for `alexandroff X`.
-/


variable {X : Type _}

#print Alexandroff /-
/-- The Alexandroff extension of an arbitrary topological space `X` -/
def Alexandroff (X : Type _) :=
  Option X
#align alexandroff Alexandroff
-/

/-- The repr uses the notation from the `alexandroff` locale. -/
instance [Repr X] : Repr (Alexandroff X) :=
  ⟨fun o =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace Alexandroff

#print Alexandroff.infty /-
/-- The point at infinity -/
def infty : Alexandroff X :=
  none
#align alexandroff.infty Alexandroff.infty
-/

-- mathport name: alexandroff.infty
scoped notation "∞" => Alexandroff.infty

instance : CoeTC X (Alexandroff X) :=
  ⟨Option.some⟩

instance : Inhabited (Alexandroff X) :=
  ⟨∞⟩

instance [Fintype X] : Fintype (Alexandroff X) :=
  Option.fintype

#print Alexandroff.infinite /-
instance infinite [Infinite X] : Infinite (Alexandroff X) :=
  Option.infinite
#align alexandroff.infinite Alexandroff.infinite
-/

#print Alexandroff.coe_injective /-
theorem coe_injective : Function.Injective (coe : X → Alexandroff X) :=
  Option.some_injective X
#align alexandroff.coe_injective Alexandroff.coe_injective
-/

#print Alexandroff.coe_eq_coe /-
@[norm_cast]
theorem coe_eq_coe {x y : X} : (x : Alexandroff X) = y ↔ x = y :=
  coe_injective.eq_iff
#align alexandroff.coe_eq_coe Alexandroff.coe_eq_coe
-/

#print Alexandroff.coe_ne_infty /-
@[simp]
theorem coe_ne_infty (x : X) : (x : Alexandroff X) ≠ ∞ :=
  fun.
#align alexandroff.coe_ne_infty Alexandroff.coe_ne_infty
-/

#print Alexandroff.infty_ne_coe /-
@[simp]
theorem infty_ne_coe (x : X) : ∞ ≠ (x : Alexandroff X) :=
  fun.
#align alexandroff.infty_ne_coe Alexandroff.infty_ne_coe
-/

#print Alexandroff.rec /-
/-- Recursor for `alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim]
protected def rec (C : Alexandroff X → Sort _) (h₁ : C ∞) (h₂ : ∀ x : X, C x) :
    ∀ z : Alexandroff X, C z :=
  Option.rec h₁ h₂
#align alexandroff.rec Alexandroff.rec
-/

/- warning: alexandroff.is_compl_range_coe_infty -> Alexandroff.isCompl_range_coe_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}}, IsCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.completeBooleanAlgebra.{u1} (Alexandroff.{u1} X))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.completeBooleanAlgebra.{u1} (Alexandroff.{u1} X)))))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
but is expected to have type
  forall {X : Type.{u1}}, IsCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instCompleteBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} (Alexandroff.{u1} X)) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instCompleteBooleanAlgebraSet.{u1} (Alexandroff.{u1} X)))))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_compl_range_coe_infty Alexandroff.isCompl_range_coe_inftyₓ'. -/
theorem isCompl_range_coe_infty : IsCompl (range (coe : X → Alexandroff X)) {∞} :=
  isCompl_range_some_none X
#align alexandroff.is_compl_range_coe_infty Alexandroff.isCompl_range_coe_infty

/- warning: alexandroff.range_coe_union_infty -> Alexandroff.range_coe_union_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasUnion.{u1} (Alexandroff.{u1} X)) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (Set.univ.{u1} (Alexandroff.{u1} X))
but is expected to have type
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instUnionSet.{u1} (Alexandroff.{u1} X)) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (Set.univ.{u1} (Alexandroff.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.range_coe_union_infty Alexandroff.range_coe_union_inftyₓ'. -/
@[simp]
theorem range_coe_union_infty : range (coe : X → Alexandroff X) ∪ {∞} = univ :=
  range_some_union_none X
#align alexandroff.range_coe_union_infty Alexandroff.range_coe_union_infty

/- warning: alexandroff.range_coe_inter_infty -> Alexandroff.range_coe_inter_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (Inter.inter.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasInter.{u1} (Alexandroff.{u1} X)) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasEmptyc.{u1} (Alexandroff.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (Inter.inter.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instInterSet.{u1} (Alexandroff.{u1} X)) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (EmptyCollection.emptyCollection.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instEmptyCollectionSet.{u1} (Alexandroff.{u1} X)))
Case conversion may be inaccurate. Consider using '#align alexandroff.range_coe_inter_infty Alexandroff.range_coe_inter_inftyₓ'. -/
@[simp]
theorem range_coe_inter_infty : range (coe : X → Alexandroff X) ∩ {∞} = ∅ :=
  range_some_inter_none X
#align alexandroff.range_coe_inter_infty Alexandroff.range_coe_inter_infty

/- warning: alexandroff.compl_range_coe -> Alexandroff.compl_range_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
but is expected to have type
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.compl_range_coe Alexandroff.compl_range_coeₓ'. -/
@[simp]
theorem compl_range_coe : range (coe : X → Alexandroff X)ᶜ = {∞} :=
  compl_range_some X
#align alexandroff.compl_range_coe Alexandroff.compl_range_coe

/- warning: alexandroff.compl_infty -> Alexandroff.compl_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))))
but is expected to have type
  forall {X : Type.{u1}}, Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.compl_infty Alexandroff.compl_inftyₓ'. -/
theorem compl_infty : ({∞}ᶜ : Set (Alexandroff X)) = range (coe : X → Alexandroff X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq
#align alexandroff.compl_infty Alexandroff.compl_infty

/- warning: alexandroff.compl_image_coe -> Alexandroff.compl_image_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} (s : Set.{u1} X), Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasUnion.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}} (s : Set.{u1} X), Eq.{succ u1} (Set.{u1} (Alexandroff.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instUnionSet.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))
Case conversion may be inaccurate. Consider using '#align alexandroff.compl_image_coe Alexandroff.compl_image_coeₓ'. -/
theorem compl_image_coe (s : Set X) : (coe '' s : Set (Alexandroff X))ᶜ = coe '' sᶜ ∪ {∞} := by
  rw [coe_injective.compl_image_eq, compl_range_coe]
#align alexandroff.compl_image_coe Alexandroff.compl_image_coe

#print Alexandroff.ne_infty_iff_exists /-
theorem ne_infty_iff_exists {x : Alexandroff X} : x ≠ ∞ ↔ ∃ y : X, (y : Alexandroff X) = x := by
  induction x using Alexandroff.rec <;> simp
#align alexandroff.ne_infty_iff_exists Alexandroff.ne_infty_iff_exists
-/

#print Alexandroff.canLift /-
instance canLift : CanLift (Alexandroff X) X coe fun x => x ≠ ∞ :=
  WithTop.canLift
#align alexandroff.can_lift Alexandroff.canLift
-/

#print Alexandroff.not_mem_range_coe_iff /-
theorem not_mem_range_coe_iff {x : Alexandroff X} : x ∉ range (coe : X → Alexandroff X) ↔ x = ∞ :=
  by rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]
#align alexandroff.not_mem_range_coe_iff Alexandroff.not_mem_range_coe_iff
-/

#print Alexandroff.infty_not_mem_range_coe /-
theorem infty_not_mem_range_coe : ∞ ∉ range (coe : X → Alexandroff X) :=
  not_mem_range_coe_iff.2 rfl
#align alexandroff.infty_not_mem_range_coe Alexandroff.infty_not_mem_range_coe
-/

#print Alexandroff.infty_not_mem_image_coe /-
theorem infty_not_mem_image_coe {s : Set X} : ∞ ∉ (coe : X → Alexandroff X) '' s :=
  not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe
#align alexandroff.infty_not_mem_image_coe Alexandroff.infty_not_mem_image_coe
-/

#print Alexandroff.coe_preimage_infty /-
@[simp]
theorem coe_preimage_infty : (coe : X → Alexandroff X) ⁻¹' {∞} = ∅ :=
  by
  ext
  simp
#align alexandroff.coe_preimage_infty Alexandroff.coe_preimage_infty
-/

/-!
### Topological space structure on `alexandroff X`

We define a topological space structure on `alexandroff X` so that `s` is open if and only if

* `coe ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `(coe ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`coe : X → alexandroff X` is an open embedding. If `X` is not a compact space, then we also prove
that `coe` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

instance : TopologicalSpace (Alexandroff X)
    where
  IsOpen s :=
    (∞ ∈ s → IsCompact (((coe : X → Alexandroff X) ⁻¹' s)ᶜ)) ∧
      IsOpen ((coe : X → Alexandroff X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine' ⟨_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_unionₛ S ho :=
    by
    suffices IsOpen (coe ⁻¹' ⋃₀ S : Set X) by
      refine' ⟨_, this⟩
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
      refine' isCompact_of_isClosed_subset ((ho s hsS).1 hs) this.is_closed_compl _
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_bunionᵢ fun s hs => (ho s hs).2

variable {s : Set (Alexandroff X)} {t : Set X}

/- warning: alexandroff.is_open_def -> Alexandroff.isOpen_def is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (And ((Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (And ((Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_def Alexandroff.isOpen_defₓ'. -/
theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact ((coe ⁻¹' s : Set X)ᶜ)) ∧ IsOpen (coe ⁻¹' s : Set X) :=
  Iff.rfl
#align alexandroff.is_open_def Alexandroff.isOpen_def

/- warning: alexandroff.is_open_iff_of_mem' -> Alexandroff.isOpen_iff_of_mem' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (And (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s))) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (And (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s))) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s))))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_iff_of_mem' Alexandroff.isOpen_iff_of_mem'ₓ'. -/
theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact ((coe ⁻¹' s : Set X)ᶜ) ∧ IsOpen (coe ⁻¹' s : Set X) := by
  simp [is_open_def, h]
#align alexandroff.is_open_iff_of_mem' Alexandroff.isOpen_iff_of_mem'

/- warning: alexandroff.is_open_iff_of_mem -> Alexandroff.isOpen_iff_of_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (And (IsClosed.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s))) (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (And (IsClosed.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s))) (IsCompact.{u1} X _inst_1 (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_iff_of_mem Alexandroff.isOpen_iff_of_memₓ'. -/
theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed ((coe ⁻¹' s : Set X)ᶜ) ∧ IsCompact ((coe ⁻¹' s : Set X)ᶜ) := by
  simp only [is_open_iff_of_mem' h, isClosed_compl_iff, and_comm]
#align alexandroff.is_open_iff_of_mem Alexandroff.isOpen_iff_of_mem

/- warning: alexandroff.is_open_iff_of_not_mem -> Alexandroff.isOpen_iff_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Not (Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s)) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Not (Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s)) -> (Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (IsOpen.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_iff_of_not_mem Alexandroff.isOpen_iff_of_not_memₓ'. -/
theorem isOpen_iff_of_not_mem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen (coe ⁻¹' s : Set X) := by
  simp [is_open_def, h]
#align alexandroff.is_open_iff_of_not_mem Alexandroff.isOpen_iff_of_not_mem

/- warning: alexandroff.is_closed_iff_of_mem -> Alexandroff.isClosed_iff_of_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (IsClosed.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s) -> (Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (IsClosed.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_closed_iff_of_mem Alexandroff.isClosed_iff_of_memₓ'. -/
theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed (coe ⁻¹' s : Set X) :=
  by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, is_open_iff_of_not_mem this, ← isOpen_compl_iff, preimage_compl]
#align alexandroff.is_closed_iff_of_mem Alexandroff.isClosed_iff_of_mem

/- warning: alexandroff.is_closed_iff_of_not_mem -> Alexandroff.isClosed_iff_of_not_mem is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Not (Membership.Mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasMem.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s)) -> (Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) s) (And (IsClosed.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)) (IsCompact.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} (Alexandroff.{u1} X)}, (Not (Membership.mem.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instMembershipSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X) s)) -> (Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) s) (And (IsClosed.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)) (IsCompact.{u1} X _inst_1 (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s))))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_closed_iff_of_not_mem Alexandroff.isClosed_iff_of_not_memₓ'. -/
theorem isClosed_iff_of_not_mem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed (coe ⁻¹' s : Set X) ∧ IsCompact (coe ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, is_open_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]
#align alexandroff.is_closed_iff_of_not_mem Alexandroff.isClosed_iff_of_not_mem

/- warning: alexandroff.is_open_image_coe -> Alexandroff.isOpen_image_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)) (IsOpen.{u1} X _inst_1 s)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)) (IsOpen.{u1} X _inst_1 s)
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_image_coe Alexandroff.isOpen_image_coeₓ'. -/
@[simp]
theorem isOpen_image_coe {s : Set X} : IsOpen (coe '' s : Set (Alexandroff X)) ↔ IsOpen s := by
  rw [is_open_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]
#align alexandroff.is_open_image_coe Alexandroff.isOpen_image_coe

/- warning: alexandroff.is_open_compl_image_coe -> Alexandroff.isOpen_compl_image_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s))) (And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s))) (And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_compl_image_coe Alexandroff.isOpen_compl_image_coeₓ'. -/
theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((coe '' s : Set (Alexandroff X))ᶜ) ↔ IsClosed s ∧ IsCompact s :=
  by
  rw [is_open_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_not_mem_image_coe
#align alexandroff.is_open_compl_image_coe Alexandroff.isOpen_compl_image_coe

/- warning: alexandroff.is_closed_image_coe -> Alexandroff.isClosed_image_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)) (And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {s : Set.{u1} X}, Iff (IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)) (And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_closed_image_coe Alexandroff.isClosed_image_coeₓ'. -/
@[simp]
theorem isClosed_image_coe {s : Set X} :
    IsClosed (coe '' s : Set (Alexandroff X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff, is_open_compl_image_coe]
#align alexandroff.is_closed_image_coe Alexandroff.isClosed_image_coe

/- warning: alexandroff.opens_of_compl -> Alexandroff.opensOfCompl is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (TopologicalSpace.Opens.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (TopologicalSpace.Opens.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align alexandroff.opens_of_compl Alexandroff.opensOfComplₓ'. -/
/-- An open set in `alexandroff X` constructed from a closed compact set in `X` -/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (Alexandroff X) :=
  ⟨(coe '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩
#align alexandroff.opens_of_compl Alexandroff.opensOfCompl

#print Alexandroff.infty_mem_opensOfCompl /-
theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ ∈ opensOfCompl s h₁ h₂ :=
  mem_compl infty_not_mem_image_coe
#align alexandroff.infty_mem_opens_of_compl Alexandroff.infty_mem_opensOfCompl
-/

/- warning: alexandroff.continuous_coe -> Alexandroff.continuous_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Continuous.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Continuous.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X)
Case conversion may be inaccurate. Consider using '#align alexandroff.continuous_coe Alexandroff.continuous_coeₓ'. -/
@[continuity]
theorem continuous_coe : Continuous (coe : X → Alexandroff X) :=
  continuous_def.mpr fun s hs => hs.right
#align alexandroff.continuous_coe Alexandroff.continuous_coe

/- warning: alexandroff.is_open_map_coe -> Alexandroff.isOpenMap_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsOpenMap.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsOpenMap.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X)
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_map_coe Alexandroff.isOpenMap_coeₓ'. -/
theorem isOpenMap_coe : IsOpenMap (coe : X → Alexandroff X) := fun s => isOpen_image_coe.2
#align alexandroff.is_open_map_coe Alexandroff.isOpenMap_coe

/- warning: alexandroff.open_embedding_coe -> Alexandroff.openEmbedding_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], OpenEmbedding.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], OpenEmbedding.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X)
Case conversion may be inaccurate. Consider using '#align alexandroff.open_embedding_coe Alexandroff.openEmbedding_coeₓ'. -/
theorem openEmbedding_coe : OpenEmbedding (coe : X → Alexandroff X) :=
  openEmbedding_of_continuous_injective_open continuous_coe coe_injective isOpenMap_coe
#align alexandroff.open_embedding_coe Alexandroff.openEmbedding_coe

/- warning: alexandroff.is_open_range_coe -> Alexandroff.isOpen_range_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsOpen.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Set.range.{u1, succ u1} (Alexandroff.{u1} X) X (Alexandroff.some.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_open_range_coe Alexandroff.isOpen_range_coeₓ'. -/
theorem isOpen_range_coe : IsOpen (range (coe : X → Alexandroff X)) :=
  openEmbedding_coe.open_range
#align alexandroff.is_open_range_coe Alexandroff.isOpen_range_coe

/- warning: alexandroff.is_closed_infty -> Alexandroff.isClosed_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], IsClosed.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.is_closed_infty Alexandroff.isClosed_inftyₓ'. -/
theorem isClosed_infty : IsClosed ({∞} : Set (Alexandroff X)) :=
  by
  rw [← compl_range_coe, isClosed_compl_iff]
  exact is_open_range_coe
#align alexandroff.is_closed_infty Alexandroff.isClosed_infty

/- warning: alexandroff.nhds_coe_eq -> Alexandroff.nhds_coe_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x)) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (nhds.{u1} X _inst_1 x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x)) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (nhds.{u1} X _inst_1 x))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_coe_eq Alexandroff.nhds_coe_eqₓ'. -/
theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map (coe : X → Alexandroff X) (𝓝 x) :=
  (openEmbedding_coe.map_nhds_eq x).symm
#align alexandroff.nhds_coe_eq Alexandroff.nhds_coe_eq

/- warning: alexandroff.nhds_within_coe_image -> Alexandroff.nhdsWithin_coe_image is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} X) (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (nhdsWithin.{u1} X _inst_1 x s))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} X) (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (nhdsWithin.{u1} X _inst_1 x s))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_coe_image Alexandroff.nhdsWithin_coe_imageₓ'. -/
theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[coe '' s] (x : Alexandroff X) = map coe (𝓝[s] x) :=
  (openEmbedding_coe.toEmbedding.map_nhdsWithin_eq _ _).symm
#align alexandroff.nhds_within_coe_image Alexandroff.nhdsWithin_coe_image

/- warning: alexandroff.nhds_within_coe -> Alexandroff.nhdsWithin_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} (Alexandroff.{u1} X)) (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) s) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (nhdsWithin.{u1} X _inst_1 x (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (s : Set.{u1} (Alexandroff.{u1} X)) (x : X), Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) s) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (nhdsWithin.{u1} X _inst_1 x (Set.preimage.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s)))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_coe Alexandroff.nhdsWithin_coeₓ'. -/
theorem nhdsWithin_coe (s : Set (Alexandroff X)) (x : X) : 𝓝[s] ↑x = map coe (𝓝[coe ⁻¹' s] x) :=
  (openEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm
#align alexandroff.nhds_within_coe Alexandroff.nhdsWithin_coe

/- warning: alexandroff.comap_coe_nhds -> Alexandroff.comap_coe_nhds is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X), Eq.{succ u1} (Filter.{u1} X) (Filter.comap.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x))) (nhds.{u1} X _inst_1 x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X), Eq.{succ u1} (Filter.{u1} X) (Filter.comap.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x))) (nhds.{u1} X _inst_1 x)
Case conversion may be inaccurate. Consider using '#align alexandroff.comap_coe_nhds Alexandroff.comap_coe_nhdsₓ'. -/
theorem comap_coe_nhds (x : X) : comap (coe : X → Alexandroff X) (𝓝 x) = 𝓝 x :=
  (openEmbedding_coe.to_inducing.nhds_eq_comap x).symm
#align alexandroff.comap_coe_nhds Alexandroff.comap_coe_nhds

/- warning: alexandroff.nhds_within_compl_coe_ne_bot -> Alexandroff.nhdsWithin_compl_coe_neBot is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X) [h : Filter.NeBot.{u1} X (nhdsWithin.{u1} X _inst_1 x (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) x)))], Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] (x : X) [h : Filter.NeBot.{u1} X (nhdsWithin.{u1} X _inst_1 x (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x)))], Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.some.{u1} X x))))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_compl_coe_ne_bot Alexandroff.nhdsWithin_compl_coe_neBotₓ'. -/
/-- If `x` is not an isolated point of `X`, then `x : alexandroff X` is not an isolated point
of `alexandroff X`. -/
instance nhdsWithin_compl_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] :
    NeBot (𝓝[≠] (x : Alexandroff X)) := by
  simpa [nhds_within_coe, preimage, coe_eq_coe] using h.map coe
#align alexandroff.nhds_within_compl_coe_ne_bot Alexandroff.nhdsWithin_compl_coe_neBot

/- warning: alexandroff.nhds_within_compl_infty_eq -> Alexandroff.nhdsWithin_compl_infty_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (Filter.coclosedCompact.{u1} X _inst_1))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (Filter.coclosedCompact.{u1} X _inst_1))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_compl_infty_eq Alexandroff.nhdsWithin_compl_infty_eqₓ'. -/
theorem nhdsWithin_compl_infty_eq : 𝓝[≠] (∞ : Alexandroff X) = map coe (coclosedCompact X) :=
  by
  refine' (nhdsWithin_basis_open ∞ _).ext (has_basis_coclosed_compact.map _) _ _
  · rintro s ⟨hs, hso⟩
    refine' ⟨_, (is_open_iff_of_mem hs).mp hso, _⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine' ⟨_, ⟨mem_compl infty_not_mem_image_coe, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩
    simp [compl_image_coe, ← diff_eq, subset_preimage_image]
#align alexandroff.nhds_within_compl_infty_eq Alexandroff.nhdsWithin_compl_infty_eq

/- warning: alexandroff.nhds_within_compl_infty_ne_bot -> Alexandroff.nhdsWithin_compl_infty_neBot is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_compl_infty_ne_bot Alexandroff.nhdsWithin_compl_infty_neBotₓ'. -/
/-- If `X` is a non-compact space, then `∞` is not an isolated point of `alexandroff X`. -/
instance nhdsWithin_compl_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : Alexandroff X)) :=
  by
  rw [nhds_within_compl_infty_eq]
  infer_instance
#align alexandroff.nhds_within_compl_infty_ne_bot Alexandroff.nhdsWithin_compl_infty_neBot

/- warning: alexandroff.nhds_within_compl_ne_bot -> Alexandroff.nhdsWithin_compl_neBot is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : forall (x : X), Filter.NeBot.{u1} X (nhdsWithin.{u1} X _inst_1 x (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.hasSingleton.{u1} X) x)))] [_inst_3 : NoncompactSpace.{u1} X _inst_1] (x : Alexandroff.{u1} X), Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.booleanAlgebra.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) x)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : forall (x : X), Filter.NeBot.{u1} X (nhdsWithin.{u1} X _inst_1 x (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) (Singleton.singleton.{u1, u1} X (Set.{u1} X) (Set.instSingletonSet.{u1} X) x)))] [_inst_3 : NoncompactSpace.{u1} X _inst_1] (x : Alexandroff.{u1} X), Filter.NeBot.{u1} (Alexandroff.{u1} X) (nhdsWithin.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) x (HasCompl.compl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instBooleanAlgebraSet.{u1} (Alexandroff.{u1} X))) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) x)))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_within_compl_ne_bot Alexandroff.nhdsWithin_compl_neBotₓ'. -/
instance (priority := 900) nhdsWithin_compl_neBot [∀ x : X, NeBot (𝓝[≠] x)] [NoncompactSpace X]
    (x : Alexandroff X) : NeBot (𝓝[≠] x) :=
  Alexandroff.rec _ Alexandroff.nhdsWithin_compl_infty_neBot
    (fun y => Alexandroff.nhdsWithin_compl_coe_neBot y) x
#align alexandroff.nhds_within_compl_ne_bot Alexandroff.nhdsWithin_compl_neBot

/- warning: alexandroff.nhds_infty_eq -> Alexandroff.nhds_infty_eq is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) (HasSup.sup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.completeLattice.{u1} (Alexandroff.{u1} X)))))) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (Filter.coclosedCompact.{u1} X _inst_1)) (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} (Alexandroff.{u1} X) (Alexandroff.infty.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} (Alexandroff.{u1} X)) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) (HasSup.sup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (SemilatticeSup.toHasSup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Lattice.toSemilatticeSup.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (ConditionallyCompleteLattice.toLattice.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (CompleteLattice.toConditionallyCompleteLattice.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.instCompleteLatticeFilter.{u1} (Alexandroff.{u1} X)))))) (Filter.map.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (Filter.coclosedCompact.{u1} X _inst_1)) (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} (Alexandroff.{u1} X) (Alexandroff.infty.{u1} X)))
Case conversion may be inaccurate. Consider using '#align alexandroff.nhds_infty_eq Alexandroff.nhds_infty_eqₓ'. -/
theorem nhds_infty_eq : 𝓝 (∞ : Alexandroff X) = map coe (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhds_within_compl_infty_eq, nhdsWithin_compl_singleton_sup_pure]
#align alexandroff.nhds_infty_eq Alexandroff.nhds_infty_eq

/- warning: alexandroff.has_basis_nhds_infty -> Alexandroff.hasBasis_nhds_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Filter.HasBasis.{u1, succ u1} (Alexandroff.{u1} X) (Set.{u1} X) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) (fun (s : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s)) (fun (s : Set.{u1} X) => Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasUnion.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Filter.HasBasis.{u1, succ u1} (Alexandroff.{u1} X) (Set.{u1} X) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) (fun (s : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 s) (IsCompact.{u1} X _inst_1 s)) (fun (s : Set.{u1} X) => Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instUnionSet.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X)))
Case conversion may be inaccurate. Consider using '#align alexandroff.has_basis_nhds_infty Alexandroff.hasBasis_nhds_inftyₓ'. -/
theorem hasBasis_nhds_infty :
    (𝓝 (∞ : Alexandroff X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      coe '' sᶜ ∪ {∞} :=
  by
  rw [nhds_infty_eq]
  exact (has_basis_coclosed_compact.map _).sup_pure _
#align alexandroff.has_basis_nhds_infty Alexandroff.hasBasis_nhds_infty

/- warning: alexandroff.comap_coe_nhds_infty -> Alexandroff.comap_coe_nhds_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} X) (Filter.comap.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (Filter.coclosedCompact.{u1} X _inst_1)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X], Eq.{succ u1} (Filter.{u1} X) (Filter.comap.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (Filter.coclosedCompact.{u1} X _inst_1)
Case conversion may be inaccurate. Consider using '#align alexandroff.comap_coe_nhds_infty Alexandroff.comap_coe_nhds_inftyₓ'. -/
@[simp]
theorem comap_coe_nhds_infty : comap (coe : X → Alexandroff X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]
#align alexandroff.comap_coe_nhds_infty Alexandroff.comap_coe_nhds_infty

/- warning: alexandroff.le_nhds_infty -> Alexandroff.le_nhds_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : Filter.{u1} (Alexandroff.{u1} X)}, Iff (LE.le.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Preorder.toLE.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.partialOrder.{u1} (Alexandroff.{u1} X)))) f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (Membership.Mem.{u1, u1} (Set.{u1} (Alexandroff.{u1} X)) (Filter.{u1} (Alexandroff.{u1} X)) (Filter.hasMem.{u1} (Alexandroff.{u1} X)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.hasUnion.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.hasSingleton.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) f))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : Filter.{u1} (Alexandroff.{u1} X)}, Iff (LE.le.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Preorder.toLE.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.instPartialOrderFilter.{u1} (Alexandroff.{u1} X)))) f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (Membership.mem.{u1, u1} (Set.{u1} (Alexandroff.{u1} X)) (Filter.{u1} (Alexandroff.{u1} X)) (instMembershipSetFilter.{u1} (Alexandroff.{u1} X)) (Union.union.{u1} (Set.{u1} (Alexandroff.{u1} X)) (Set.instUnionSet.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) s)) (Singleton.singleton.{u1, u1} (Alexandroff.{u1} X) (Set.{u1} (Alexandroff.{u1} X)) (Set.instSingletonSet.{u1} (Alexandroff.{u1} X)) (Alexandroff.infty.{u1} X))) f))
Case conversion may be inaccurate. Consider using '#align alexandroff.le_nhds_infty Alexandroff.le_nhds_inftyₓ'. -/
theorem le_nhds_infty {f : Filter (Alexandroff X)} :
    f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coe '' sᶜ ∪ {∞} ∈ f := by
  simp only [has_basis_nhds_infty.ge_iff, and_imp]
#align alexandroff.le_nhds_infty Alexandroff.le_nhds_infty

/- warning: alexandroff.ultrafilter_le_nhds_infty -> Alexandroff.ultrafilter_le_nhds_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : Ultrafilter.{u1} (Alexandroff.{u1} X)}, Iff (LE.le.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Preorder.toLE.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.partialOrder.{u1} (Alexandroff.{u1} X)))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Ultrafilter.{u1} (Alexandroff.{u1} X)) (Filter.{u1} (Alexandroff.{u1} X)) (HasLiftT.mk.{succ u1, succ u1} (Ultrafilter.{u1} (Alexandroff.{u1} X)) (Filter.{u1} (Alexandroff.{u1} X)) (CoeTCₓ.coe.{succ u1, succ u1} (Ultrafilter.{u1} (Alexandroff.{u1} X)) (Filter.{u1} (Alexandroff.{u1} X)) (Ultrafilter.Filter.hasCoeT.{u1} (Alexandroff.{u1} X)))) f) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (Not (Membership.Mem.{u1, u1} (Set.{u1} (Alexandroff.{u1} X)) (Ultrafilter.{u1} (Alexandroff.{u1} X)) (Ultrafilter.hasMem.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X)))) s) f)))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {f : Ultrafilter.{u1} (Alexandroff.{u1} X)}, Iff (LE.le.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Preorder.toLE.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (PartialOrder.toPreorder.{u1} (Filter.{u1} (Alexandroff.{u1} X)) (Filter.instPartialOrderFilter.{u1} (Alexandroff.{u1} X)))) (Ultrafilter.toFilter.{u1} (Alexandroff.{u1} X) f) (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X))) (forall (s : Set.{u1} X), (IsClosed.{u1} X _inst_1 s) -> (IsCompact.{u1} X _inst_1 s) -> (Not (Membership.mem.{u1, u1} (Set.{u1} (Alexandroff.{u1} X)) (Ultrafilter.{u1} (Alexandroff.{u1} X)) (Ultrafilter.instMembershipSetUltrafilter.{u1} (Alexandroff.{u1} X)) (Set.image.{u1, u1} X (Alexandroff.{u1} X) (Alexandroff.some.{u1} X) s) f)))
Case conversion may be inaccurate. Consider using '#align alexandroff.ultrafilter_le_nhds_infty Alexandroff.ultrafilter_le_nhds_inftyₓ'. -/
theorem ultrafilter_le_nhds_infty {f : Ultrafilter (Alexandroff X)} :
    (f : Filter (Alexandroff X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → coe '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_not_mem]
#align alexandroff.ultrafilter_le_nhds_infty Alexandroff.ultrafilter_le_nhds_infty

/- warning: alexandroff.tendsto_nhds_infty' -> Alexandroff.tendsto_nhds_infty' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u2}} {f : (Alexandroff.{u1} X) -> α} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) l) (And (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (Pure.pure.{u1, u1} Filter.{u1} Filter.hasPure.{u1} (Alexandroff.{u1} X) (Alexandroff.infty.{u1} X)) l) (Filter.Tendsto.{u1, u2} X α (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) α f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (Filter.coclosedCompact.{u1} X _inst_1) l))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u2}} {f : (Alexandroff.{u1} X) -> α} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) l) (And (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (Pure.pure.{u1, u1} Filter.{u1} Filter.instPureFilter.{u1} (Alexandroff.{u1} X) (Alexandroff.infty.{u1} X)) l) (Filter.Tendsto.{u1, u2} X α (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) α f (Alexandroff.some.{u1} X)) (Filter.coclosedCompact.{u1} X _inst_1) l))
Case conversion may be inaccurate. Consider using '#align alexandroff.tendsto_nhds_infty' Alexandroff.tendsto_nhds_infty'ₓ'. -/
theorem tendsto_nhds_infty' {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ coe) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm']
#align alexandroff.tendsto_nhds_infty' Alexandroff.tendsto_nhds_infty'

/- warning: alexandroff.tendsto_nhds_infty -> Alexandroff.tendsto_nhds_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u2}} {f : (Alexandroff.{u1} X) -> α} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) l) (forall (s : Set.{u2} α), (Membership.Mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (Filter.hasMem.{u2} α) s l) -> (And (Membership.Mem.{u2, u2} α (Set.{u2} α) (Set.hasMem.{u2} α) (f (Alexandroff.infty.{u1} X)) s) (Exists.{succ u1} (Set.{u1} X) (fun (t : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 t) (And (IsCompact.{u1} X _inst_1 t) (Set.MapsTo.{u1, u2} X α (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) α f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) t) s))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {α : Type.{u2}} {f : (Alexandroff.{u1} X) -> α} {l : Filter.{u2} α}, Iff (Filter.Tendsto.{u1, u2} (Alexandroff.{u1} X) α f (nhds.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X)) l) (forall (s : Set.{u2} α), (Membership.mem.{u2, u2} (Set.{u2} α) (Filter.{u2} α) (instMembershipSetFilter.{u2} α) s l) -> (And (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (f (Alexandroff.infty.{u1} X)) s) (Exists.{succ u1} (Set.{u1} X) (fun (t : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 t) (And (IsCompact.{u1} X _inst_1 t) (Set.MapsTo.{u1, u2} X α (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) α f (Alexandroff.some.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) t) s))))))
Case conversion may be inaccurate. Consider using '#align alexandroff.tendsto_nhds_infty Alexandroff.tendsto_nhds_inftyₓ'. -/
theorem tendsto_nhds_infty {α : Type _} {f : Alexandroff X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ coe) (tᶜ) s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, has_basis_coclosed_compact.tendsto_left_iff, forall_and,
      and_assoc', exists_prop]
#align alexandroff.tendsto_nhds_infty Alexandroff.tendsto_nhds_infty

/- warning: alexandroff.continuous_at_infty' -> Alexandroff.continuousAt_infty' is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.topologicalSpace.{u1} X _inst_1) _inst_2 f (Alexandroff.infty.{u1} X)) (Filter.Tendsto.{u1, u2} X Y (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (Filter.coclosedCompact.{u1} X _inst_1) (nhds.{u2} Y _inst_2 (f (Alexandroff.infty.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) _inst_2 f (Alexandroff.infty.{u1} X)) (Filter.Tendsto.{u1, u2} X Y (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f (Alexandroff.some.{u1} X)) (Filter.coclosedCompact.{u1} X _inst_1) (nhds.{u2} Y _inst_2 (f (Alexandroff.infty.{u1} X))))
Case conversion may be inaccurate. Consider using '#align alexandroff.continuous_at_infty' Alexandroff.continuousAt_infty'ₓ'. -/
theorem continuousAt_infty' {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ coe) (coclosedCompact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans <| and_iff_right (tendsto_pure_nhds _ _)
#align alexandroff.continuous_at_infty' Alexandroff.continuousAt_infty'

/- warning: alexandroff.continuous_at_infty -> Alexandroff.continuousAt_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.topologicalSpace.{u1} X _inst_1) _inst_2 f (Alexandroff.infty.{u1} X)) (forall (s : Set.{u2} Y), (Membership.Mem.{u2, u2} (Set.{u2} Y) (Filter.{u2} Y) (Filter.hasMem.{u2} Y) s (nhds.{u2} Y _inst_2 (f (Alexandroff.infty.{u1} X)))) -> (Exists.{succ u1} (Set.{u1} X) (fun (t : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 t) (And (IsCompact.{u1} X _inst_1 t) (Set.MapsTo.{u1, u2} X Y (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.booleanAlgebra.{u1} X)) t) s)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) _inst_2 f (Alexandroff.infty.{u1} X)) (forall (s : Set.{u2} Y), (Membership.mem.{u2, u2} (Set.{u2} Y) (Filter.{u2} Y) (instMembershipSetFilter.{u2} Y) s (nhds.{u2} Y _inst_2 (f (Alexandroff.infty.{u1} X)))) -> (Exists.{succ u1} (Set.{u1} X) (fun (t : Set.{u1} X) => And (IsClosed.{u1} X _inst_1 t) (And (IsCompact.{u1} X _inst_1 t) (Set.MapsTo.{u1, u2} X Y (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f (Alexandroff.some.{u1} X)) (HasCompl.compl.{u1} (Set.{u1} X) (BooleanAlgebra.toHasCompl.{u1} (Set.{u1} X) (Set.instBooleanAlgebraSet.{u1} X)) t) s)))))
Case conversion may be inaccurate. Consider using '#align alexandroff.continuous_at_infty Alexandroff.continuousAt_inftyₓ'. -/
theorem continuousAt_infty {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} :
    ContinuousAt f ∞ ↔
      ∀ s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ coe) (tᶜ) s :=
  continuousAt_infty'.trans <| by
    simp only [has_basis_coclosed_compact.tendsto_left_iff, exists_prop, and_assoc']
#align alexandroff.continuous_at_infty Alexandroff.continuousAt_infty

/- warning: alexandroff.continuous_at_coe -> Alexandroff.continuousAt_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y} {x : X}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.topologicalSpace.{u1} X _inst_1) _inst_2 f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x)) (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))) x)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {Y : Type.{u2}} [_inst_2 : TopologicalSpace.{u2} Y] {f : (Alexandroff.{u1} X) -> Y} {x : X}, Iff (ContinuousAt.{u1, u2} (Alexandroff.{u1} X) Y (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) _inst_2 f (Alexandroff.some.{u1} X x)) (ContinuousAt.{u1, u2} X Y _inst_1 _inst_2 (Function.comp.{succ u1, succ u1, succ u2} X (Alexandroff.{u1} X) Y f (Alexandroff.some.{u1} X)) x)
Case conversion may be inaccurate. Consider using '#align alexandroff.continuous_at_coe Alexandroff.continuousAt_coeₓ'. -/
theorem continuousAt_coe {Y : Type _} [TopologicalSpace Y] {f : Alexandroff X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ coe) x := by
  rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]
#align alexandroff.continuous_at_coe Alexandroff.continuousAt_coe

/- warning: alexandroff.dense_range_coe -> Alexandroff.denseRange_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], DenseRange.{u1, u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) X ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], DenseRange.{u1, u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) X (Alexandroff.some.{u1} X)
Case conversion may be inaccurate. Consider using '#align alexandroff.dense_range_coe Alexandroff.denseRange_coeₓ'. -/
/-- If `X` is not a compact space, then the natural embedding `X → alexandroff X` has dense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange (coe : X → Alexandroff X) :=
  by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _
#align alexandroff.dense_range_coe Alexandroff.denseRange_coe

/- warning: alexandroff.dense_embedding_coe -> Alexandroff.denseEmbedding_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], DenseEmbedding.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : NoncompactSpace.{u1} X _inst_1], DenseEmbedding.{u1, u1} X (Alexandroff.{u1} X) _inst_1 (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X)
Case conversion may be inaccurate. Consider using '#align alexandroff.dense_embedding_coe Alexandroff.denseEmbedding_coeₓ'. -/
theorem denseEmbedding_coe [NoncompactSpace X] : DenseEmbedding (coe : X → Alexandroff X) :=
  { openEmbedding_coe with dense := denseRange_coe }
#align alexandroff.dense_embedding_coe Alexandroff.denseEmbedding_coe

/- warning: alexandroff.specializes_coe -> Alexandroff.specializes_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) y)) (Specializes.{u1} X _inst_1 x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Specializes.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) (Alexandroff.some.{u1} X y)) (Specializes.{u1} X _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align alexandroff.specializes_coe Alexandroff.specializes_coeₓ'. -/
@[simp]
theorem specializes_coe {x y : X} : (x : Alexandroff X) ⤳ y ↔ x ⤳ y :=
  openEmbedding_coe.to_inducing.specializes_iff
#align alexandroff.specializes_coe Alexandroff.specializes_coe

/- warning: alexandroff.inseparable_coe -> Alexandroff.inseparable_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) y)) (Inseparable.{u1} X _inst_1 x y)
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X} {y : X}, Iff (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) (Alexandroff.some.{u1} X y)) (Inseparable.{u1} X _inst_1 x y)
Case conversion may be inaccurate. Consider using '#align alexandroff.inseparable_coe Alexandroff.inseparable_coeₓ'. -/
@[simp]
theorem inseparable_coe {x y : X} : Inseparable (x : Alexandroff X) y ↔ Inseparable x y :=
  openEmbedding_coe.to_inducing.inseparable_iff
#align alexandroff.inseparable_coe Alexandroff.inseparable_coe

/- warning: alexandroff.not_specializes_infty_coe -> Alexandroff.not_specializes_infty_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Specializes.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Specializes.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (Alexandroff.some.{u1} X x))
Case conversion may be inaccurate. Consider using '#align alexandroff.not_specializes_infty_coe Alexandroff.not_specializes_infty_coeₓ'. -/
theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : Alexandroff X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)
#align alexandroff.not_specializes_infty_coe Alexandroff.not_specializes_infty_coe

/- warning: alexandroff.not_inseparable_infty_coe -> Alexandroff.not_inseparable_infty_coe is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) (Alexandroff.infty.{u1} X) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.infty.{u1} X) (Alexandroff.some.{u1} X x))
Case conversion may be inaccurate. Consider using '#align alexandroff.not_inseparable_infty_coe Alexandroff.not_inseparable_infty_coeₓ'. -/
theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : Alexandroff X) := fun h =>
  not_specializes_infty_coe h.Specializes
#align alexandroff.not_inseparable_infty_coe Alexandroff.not_inseparable_infty_coe

/- warning: alexandroff.not_inseparable_coe_infty -> Alexandroff.not_inseparable_coe_infty is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x) (Alexandroff.infty.{u1} X))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : X}, Not (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (Alexandroff.some.{u1} X x) (Alexandroff.infty.{u1} X))
Case conversion may be inaccurate. Consider using '#align alexandroff.not_inseparable_coe_infty Alexandroff.not_inseparable_coe_inftyₓ'. -/
theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : Alexandroff X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'
#align alexandroff.not_inseparable_coe_infty Alexandroff.not_inseparable_coe_infty

/- warning: alexandroff.inseparable_iff -> Alexandroff.inseparable_iff is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : Alexandroff.{u1} X} {y : Alexandroff.{u1} X}, Iff (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.topologicalSpace.{u1} X _inst_1) x y) (Or (And (Eq.{succ u1} (Alexandroff.{u1} X) x (Alexandroff.infty.{u1} X)) (Eq.{succ u1} (Alexandroff.{u1} X) y (Alexandroff.infty.{u1} X))) (Exists.{succ u1} X (fun (x' : X) => And (Eq.{succ u1} (Alexandroff.{u1} X) x ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) x')) (Exists.{succ u1} X (fun (y' : X) => And (Eq.{succ u1} (Alexandroff.{u1} X) y ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) X (Alexandroff.{u1} X) (HasLiftT.mk.{succ u1, succ u1} X (Alexandroff.{u1} X) (CoeTCₓ.coe.{succ u1, succ u1} X (Alexandroff.{u1} X) (Alexandroff.hasCoeT.{u1} X))) y')) (Inseparable.{u1} X _inst_1 x' y'))))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] {x : Alexandroff.{u1} X} {y : Alexandroff.{u1} X}, Iff (Inseparable.{u1} (Alexandroff.{u1} X) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) x y) (Or (And (Eq.{succ u1} (Alexandroff.{u1} X) x (Alexandroff.infty.{u1} X)) (Eq.{succ u1} (Alexandroff.{u1} X) y (Alexandroff.infty.{u1} X))) (Exists.{succ u1} X (fun (x' : X) => And (Eq.{succ u1} (Alexandroff.{u1} X) x (Alexandroff.some.{u1} X x')) (Exists.{succ u1} X (fun (y' : X) => And (Eq.{succ u1} (Alexandroff.{u1} X) y (Alexandroff.some.{u1} X y')) (Inseparable.{u1} X _inst_1 x' y'))))))
Case conversion may be inaccurate. Consider using '#align alexandroff.inseparable_iff Alexandroff.inseparable_iffₓ'. -/
theorem inseparable_iff {x y : Alexandroff X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ ∃ x' : X, x = x' ∧ ∃ y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using Alexandroff.rec <;> induction y using Alexandroff.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe]
#align alexandroff.inseparable_iff Alexandroff.inseparable_iff

/-!
### Compactness and separation properties

In this section we prove that `alexandroff X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `alexandroff X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`alexandroff X` is a connected space.
-/


/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : CompactSpace (Alexandroff X)
    where isCompact_univ :=
    by
    have : tendsto (coe : X → Alexandroff X) (cocompact X) (𝓝 ∞) :=
      by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosed_compact).mono_right le_sup_left
    convert ← this.is_compact_insert_range_of_cocompact continuous_coe
    exact insert_none_range_some X

/-- The one point compactification of a `t0_space` space is a `t0_space`. -/
instance [T0Space X] : T0Space (Alexandroff X) :=
  by
  refine' ⟨fun x y hxy => _⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts[rfl, congr_arg coe h.eq]

/-- The one point compactification of a `t1_space` space is a `t1_space`. -/
instance [T1Space X] : T1Space (Alexandroff X)
    where t1 z := by
    induction z using Alexandroff.rec
    · exact is_closed_infty
    · rw [← image_singleton, is_closed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a locally compact Hausdorff space is a normal (hence,
Hausdorff and regular) topological space. -/
instance [LocallyCompactSpace X] [T2Space X] : NormalSpace (Alexandroff X) :=
  by
  have key :
    ∀ z : X, ∃ u v : Set (Alexandroff X), IsOpen u ∧ IsOpen v ∧ ↑z ∈ u ∧ ∞ ∈ v ∧ Disjoint u v :=
    by
    intro z
    rcases exists_open_with_compact_closure z with ⟨u, hu, huy', Hu⟩
    exact
      ⟨coe '' u, (coe '' closure u)ᶜ, is_open_image_coe.2 hu,
        is_open_compl_image_coe.2 ⟨isClosed_closure, Hu⟩, mem_image_of_mem _ huy',
        mem_compl infty_not_mem_image_coe, (image_subset _ subset_closure).disjoint_compl_right⟩
  refine' @normalOfCompactT2 _ _ _ ⟨fun x y hxy => _⟩
  induction x using Alexandroff.rec <;> induction y using Alexandroff.rec
  · exact (hxy rfl).elim
  · rcases key y with ⟨u, v, hu, hv, hxu, hyv, huv⟩
    exact ⟨v, u, hv, hu, hyv, hxu, huv.symm⟩
  · exact key x
  · exact separated_by_openEmbedding open_embedding_coe (mt coe_eq_coe.mpr hxy)

/-- If `X` is not a compact space, then `alexandroff X` is a connected space. -/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (Alexandroff X)
    where
  to_preconnectedSpace := denseEmbedding_coe.to_denseInducing.PreconnectedSpace
  to_nonempty := inferInstance

/- warning: alexandroff.not_continuous_cofinite_topology_of_symm -> Alexandroff.not_continuous_cofiniteTopology_of_symm is a dubious translation:
lean 3 declaration is
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : Infinite.{succ u1} X] [_inst_3 : DiscreteTopology.{u1} X _inst_1], Not (Continuous.{u1, u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X) (CofiniteTopology.topologicalSpace.{u1} (Alexandroff.{u1} X)) (Alexandroff.topologicalSpace.{u1} X _inst_1) (coeFn.{succ u1, succ u1} (Equiv.{succ u1, succ u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X)) (fun (_x : Equiv.{succ u1, succ u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X)) => (CofiniteTopology.{u1} (Alexandroff.{u1} X)) -> (Alexandroff.{u1} X)) (Equiv.hasCoeToFun.{succ u1, succ u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X)) (Equiv.symm.{succ u1, succ u1} (Alexandroff.{u1} X) (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (CofiniteTopology.of.{u1} (Alexandroff.{u1} X)))))
but is expected to have type
  forall {X : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} X] [_inst_2 : Infinite.{succ u1} X] [_inst_3 : DiscreteTopology.{u1} X _inst_1], Not (Continuous.{u1, u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X) (CofiniteTopology.instTopologicalSpaceCofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.instTopologicalSpaceAlexandroff.{u1} X _inst_1) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.{succ u1, succ u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X)) (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (fun (_x : CofiniteTopology.{u1} (Alexandroff.{u1} X)) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : CofiniteTopology.{u1} (Alexandroff.{u1} X)) => Alexandroff.{u1} X) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (Alexandroff.{u1} X)) (Equiv.symm.{succ u1, succ u1} (Alexandroff.{u1} X) (CofiniteTopology.{u1} (Alexandroff.{u1} X)) (CofiniteTopology.of.{u1} (Alexandroff.{u1} X)))))
Case conversion may be inaccurate. Consider using '#align alexandroff.not_continuous_cofinite_topology_of_symm Alexandroff.not_continuous_cofiniteTopology_of_symmₓ'. -/
/-- If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity map from
`cofinite_topology (alexandroff X)` to `alexandroff X` is not continuous. -/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (Alexandroff X)).symm :=
  by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq] using
    (finite_singleton ((default : X) : Alexandroff X)).infinite_compl
#align alexandroff.not_continuous_cofinite_topology_of_symm Alexandroff.not_continuous_cofiniteTopology_of_symm

end Alexandroff

#print Continuous.homeoOfEquivCompactToT2.t1_counterexample /-
/-- A concrete counterexample shows that  `continuous.homeo_of_equiv_compact_to_t2`
cannot be generalized from `t2_space` to `t1_space`.

Let `α = alexandroff ℕ` be the one-point compactification of `ℕ`, and let `β` be the same space
`alexandroff ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and the identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    ∃ (α β : Type)(Iα : TopologicalSpace α)(Iβ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ ∃ f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨Alexandroff ℕ, CofiniteTopology (Alexandroff ℕ), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    Alexandroff.not_continuous_cofiniteTopology_of_symm⟩
#align continuous.homeo_of_equiv_compact_to_t2.t1_counterexample Continuous.homeoOfEquivCompactToT2.t1_counterexample
-/

