/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta

! This file was ported from Lean 3 source module analysis.convex.independent
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.Combination
import Mathbin.Analysis.Convex.Extreme

/-!
# Convex independence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines convex independent families of points.

Convex independence is closely related to affine independence. In both cases, no point can be
written as a combination of others. When the combination is affine (that is, any coefficients), this
yields affine independence. When the combination is convex (that is, all coefficients are
nonnegative), then this yields convex independence. In particular, affine independence implies
convex independence.

## Main declarations

* `convex_independent p`: Convex independence of the indexed family `p : ι → E`. Every point of the
  family only belongs to convex hulls of sets of the family containing it.
* `convex_independent_iff_finset`: Carathéodory's theorem allows us to only check finsets to
  conclude convex independence.
* `convex.extreme_points_convex_independent`: Extreme points of a convex set are convex independent.

## References

* https://en.wikipedia.org/wiki/Convex_position

## TODO

Prove `affine_independent.convex_independent`. This requires some glue between `affine_combination`
and `finset.center_mass`.

## Tags

independence, convex position
-/


open Affine BigOperators Classical

open Finset Function

variable {𝕜 E ι : Type _}

section OrderedSemiring

variable (𝕜) [OrderedSemiring 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

#print ConvexIndependent /-
/-- An indexed family is said to be convex independent if every point only belongs to convex hulls
of sets containing it. -/
def ConvexIndependent (p : ι → E) : Prop :=
  ∀ (s : Set ι) (x : ι), p x ∈ convexHull 𝕜 (p '' s) → x ∈ s
#align convex_independent ConvexIndependent
-/

variable {𝕜}

/- warning: subsingleton.convex_independent -> Subsingleton.convexIndependent is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] [_inst_4 : Subsingleton.{succ u3} ι] (p : ι -> E), ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u1} E _inst_2)] [_inst_4 : Subsingleton.{succ u3} ι] (p : ι -> E), ConvexIndependent.{u2, u1, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p
Case conversion may be inaccurate. Consider using '#align subsingleton.convex_independent Subsingleton.convexIndependentₓ'. -/
/-- A family with at most one point is convex independent. -/
theorem Subsingleton.convexIndependent [Subsingleton ι] (p : ι → E) : ConvexIndependent 𝕜 p :=
  fun s x hx => by
  have : (convexHull 𝕜 (p '' s)).Nonempty := ⟨p x, hx⟩
  rw [convexHull_nonempty_iff, Set.nonempty_image_iff] at this
  rwa [Subsingleton.mem_iff_nonempty]
#align subsingleton.convex_independent Subsingleton.convexIndependent

/- warning: convex_independent.injective -> ConvexIndependent.injective is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (Function.Injective.{succ u3, succ u2} ι E p)
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : OrderedSemiring.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (OrderedSemiring.toSemiring.{u3} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u3, u2, u1} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (Function.Injective.{succ u1, succ u2} ι E p)
Case conversion may be inaccurate. Consider using '#align convex_independent.injective ConvexIndependent.injectiveₓ'. -/
/-- A convex independent family is injective. -/
protected theorem ConvexIndependent.injective {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    Function.Injective p := by
  refine' fun i j hij => hc {j} i _
  rw [hij, Set.image_singleton, convexHull_singleton]
  exact Set.mem_singleton _
#align convex_independent.injective ConvexIndependent.injective

/- warning: convex_independent.comp_embedding -> ConvexIndependent.comp_embedding is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {ι' : Type.{u4}} (f : Function.Embedding.{succ u4, succ u3} ι' ι) {p : ι -> E}, (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (ConvexIndependent.{u1, u2, u4} 𝕜 E ι' _inst_1 _inst_2 _inst_3 (Function.comp.{succ u4, succ u3, succ u2} ι' ι E p (coeFn.{max 1 (succ u4) (succ u3), max (succ u4) (succ u3)} (Function.Embedding.{succ u4, succ u3} ι' ι) (fun (_x : Function.Embedding.{succ u4, succ u3} ι' ι) => ι' -> ι) (Function.Embedding.hasCoeToFun.{succ u4, succ u3} ι' ι) f)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} E] [_inst_3 : Module.{u2, u1} 𝕜 E (OrderedSemiring.toSemiring.{u2} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u1} E _inst_2)] {ι' : Type.{u4}} (f : Function.Embedding.{succ u4, succ u3} ι' ι) {p : ι -> E}, (ConvexIndependent.{u2, u1, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (ConvexIndependent.{u2, u1, u4} 𝕜 E ι' _inst_1 _inst_2 _inst_3 (Function.comp.{succ u4, succ u3, succ u1} ι' ι E p (FunLike.coe.{max (succ u3) (succ u4), succ u4, succ u3} (Function.Embedding.{succ u4, succ u3} ι' ι) ι' (fun (_x : ι') => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : ι') => ι) _x) (EmbeddingLike.toFunLike.{max (succ u3) (succ u4), succ u4, succ u3} (Function.Embedding.{succ u4, succ u3} ι' ι) ι' ι (Function.instEmbeddingLikeEmbedding.{succ u4, succ u3} ι' ι)) f)))
Case conversion may be inaccurate. Consider using '#align convex_independent.comp_embedding ConvexIndependent.comp_embeddingₓ'. -/
/-- If a family is convex independent, so is any subfamily given by composition of an embedding into
index type with the original family. -/
theorem ConvexIndependent.comp_embedding {ι' : Type _} (f : ι' ↪ ι) {p : ι → E}
    (hc : ConvexIndependent 𝕜 p) : ConvexIndependent 𝕜 (p ∘ f) :=
  by
  intro s x hx
  rw [← f.injective.mem_set_image]
  exact hc _ _ (by rwa [Set.image_image])
#align convex_independent.comp_embedding ConvexIndependent.comp_embedding

/- warning: convex_independent.subtype -> ConvexIndependent.subtype is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (forall (s : Set.{u3} ι), ConvexIndependent.{u1, u2, u3} 𝕜 E (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) _inst_1 _inst_2 _inst_3 (fun (i : coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) => p ((fun (a : Type.{u3}) (b : Type.{u3}) [self : HasLiftT.{succ u3, succ u3} a b] => self.0) (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) ι (HasLiftT.mk.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) ι (CoeTCₓ.coe.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) ι (coeBase.{succ u3, succ u3} (coeSort.{succ u3, succ (succ u3)} (Set.{u3} ι) Type.{u3} (Set.hasCoeToSort.{u3} ι) s) ι (coeSubtype.{succ u3} ι (fun (x : ι) => Membership.Mem.{u3, u3} ι (Set.{u3} ι) (Set.hasMem.{u3} ι) x s))))) i)))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : OrderedSemiring.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (OrderedSemiring.toSemiring.{u3} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u3, u2, u1} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (forall (s : Set.{u1} ι), ConvexIndependent.{u3, u2, u1} 𝕜 E (Set.Elem.{u1} ι s) _inst_1 _inst_2 _inst_3 (fun (i : Set.Elem.{u1} ι s) => p (Subtype.val.{succ u1} ι (fun (x : ι) => Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) x s) i)))
Case conversion may be inaccurate. Consider using '#align convex_independent.subtype ConvexIndependent.subtypeₓ'. -/
/-- If a family is convex independent, so is any subfamily indexed by a subtype of the index type.
-/
protected theorem ConvexIndependent.subtype {p : ι → E} (hc : ConvexIndependent 𝕜 p) (s : Set ι) :
    ConvexIndependent 𝕜 fun i : s => p i :=
  hc.comp_embedding (Embedding.subtype _)
#align convex_independent.subtype ConvexIndependent.subtype

/- warning: convex_independent.range -> ConvexIndependent.range is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (ConvexIndependent.{u1, u2, u2} 𝕜 E (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) _inst_1 _inst_2 _inst_3 (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι p)) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (Set.range.{u2, succ u3} E ι p)))))) x))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : OrderedSemiring.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (OrderedSemiring.toSemiring.{u3} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u3, u2, u1} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (ConvexIndependent.{u3, u2, u2} 𝕜 E (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u1} E ι p))) _inst_1 _inst_2 _inst_3 (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u1} E ι p))))
Case conversion may be inaccurate. Consider using '#align convex_independent.range ConvexIndependent.rangeₓ'. -/
/-- If an indexed family of points is convex independent, so is the corresponding set of points. -/
protected theorem ConvexIndependent.range {p : ι → E} (hc : ConvexIndependent 𝕜 p) :
    ConvexIndependent 𝕜 (fun x => x : Set.range p → E) :=
  by
  let f : Set.range p → ι := fun x => x.property.some
  have hf : ∀ x, p (f x) = x := fun x => x.property.some_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert hc.comp_embedding fe
  ext
  rw [embedding.coe_fn_mk, comp_app, hf]
#align convex_independent.range ConvexIndependent.range

#print ConvexIndependent.mono /-
/-- A subset of a convex independent set of points is convex independent as well. -/
protected theorem ConvexIndependent.mono {s t : Set E}
    (hc : ConvexIndependent 𝕜 (fun x => x : t → E)) (hs : s ⊆ t) :
    ConvexIndependent 𝕜 (fun x => x : s → E) :=
  hc.comp_embedding (s.embeddingOfSubset t hs)
#align convex_independent.mono ConvexIndependent.mono
-/

#print Function.Injective.convexIndependent_iff_set /-
/-- The range of an injective indexed family of points is convex independent iff that family is. -/
theorem Function.Injective.convexIndependent_iff_set {p : ι → E} (hi : Function.Injective p) :
    ConvexIndependent 𝕜 (fun x => x : Set.range p → E) ↔ ConvexIndependent 𝕜 p :=
  ⟨fun hc =>
    hc.comp_embedding
      (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ :
        ι ↪ Set.range p),
    ConvexIndependent.range⟩
#align function.injective.convex_independent_iff_set Function.Injective.convexIndependent_iff_set
-/

/- warning: convex_independent.mem_convex_hull_iff -> ConvexIndependent.mem_convexHull_iff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (forall (s : Set.{u3} ι) (i : ι), Iff (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (p i) (coeFn.{succ u2, succ u2} (ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (fun (_x : ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) => (Set.{u2} E) -> (Set.{u2} E)) (ClosureOperator.hasCoeToFun.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (Set.image.{u3, u2} ι E p s))) (Membership.Mem.{u3, u3} ι (Set.{u3} ι) (Set.hasMem.{u3} ι) i s))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : OrderedSemiring.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (OrderedSemiring.toSemiring.{u3} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, (ConvexIndependent.{u3, u2, u1} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) -> (forall (s : Set.{u1} ι) (i : ι), Iff (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (p i) (OrderHom.toFun.{u2, u2} (Set.{u2} E) (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (ClosureOperator.toOrderHom.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (convexHull.{u3, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)) (Set.image.{u1, u2} ι E p s))) (Membership.mem.{u1, u1} ι (Set.{u1} ι) (Set.instMembershipSet.{u1} ι) i s))
Case conversion may be inaccurate. Consider using '#align convex_independent.mem_convex_hull_iff ConvexIndependent.mem_convexHull_iffₓ'. -/
/-- If a family is convex independent, a point in the family is in the convex hull of some of the
points given by a subset of the index type if and only if the point's index is in this subset. -/
@[simp]
protected theorem ConvexIndependent.mem_convexHull_iff {p : ι → E} (hc : ConvexIndependent 𝕜 p)
    (s : Set ι) (i : ι) : p i ∈ convexHull 𝕜 (p '' s) ↔ i ∈ s :=
  ⟨hc _ _, fun hi => subset_convexHull 𝕜 _ (Set.mem_image_of_mem p hi)⟩
#align convex_independent.mem_convex_hull_iff ConvexIndependent.mem_convexHull_iff

/- warning: convex_independent_iff_not_mem_convex_hull_diff -> convexIndependent_iff_not_mem_convexHull_diff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, Iff (ConvexIndependent.{u1, u2, u3} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) (forall (i : ι) (s : Set.{u3} ι), Not (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (p i) (coeFn.{succ u2, succ u2} (ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (fun (_x : ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) => (Set.{u2} E) -> (Set.{u2} E)) (ClosureOperator.hasCoeToFun.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (Set.image.{u3, u2} ι E p (SDiff.sdiff.{u3} (Set.{u3} ι) (BooleanAlgebra.toHasSdiff.{u3} (Set.{u3} ι) (Set.booleanAlgebra.{u3} ι)) s (Singleton.singleton.{u3, u3} ι (Set.{u3} ι) (Set.hasSingleton.{u3} ι) i))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : OrderedSemiring.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (OrderedSemiring.toSemiring.{u3} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, Iff (ConvexIndependent.{u3, u2, u1} 𝕜 E ι _inst_1 _inst_2 _inst_3 p) (forall (i : ι) (s : Set.{u1} ι), Not (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (p i) (OrderHom.toFun.{u2, u2} (Set.{u2} E) (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (ClosureOperator.toOrderHom.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (convexHull.{u3, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)) (Set.image.{u1, u2} ι E p (SDiff.sdiff.{u1} (Set.{u1} ι) (Set.instSDiffSet.{u1} ι) s (Singleton.singleton.{u1, u1} ι (Set.{u1} ι) (Set.instSingletonSet.{u1} ι) i))))))
Case conversion may be inaccurate. Consider using '#align convex_independent_iff_not_mem_convex_hull_diff convexIndependent_iff_not_mem_convexHull_diffₓ'. -/
/-- If a family is convex independent, a point in the family is not in the convex hull of the other
points. See `convex_independent_set_iff_not_mem_convex_hull_diff` for the `set` version.  -/
theorem convexIndependent_iff_not_mem_convexHull_diff {p : ι → E} :
    ConvexIndependent 𝕜 p ↔ ∀ i s, p i ∉ convexHull 𝕜 (p '' (s \ {i})) :=
  by
  refine' ⟨fun hc i s h => _, fun h s i hi => _⟩
  · rw [hc.mem_convex_hull_iff] at h
    exact h.2 (Set.mem_singleton _)
  · by_contra H
    refine' h i s _
    rw [Set.diff_singleton_eq_self H]
    exact hi
#align convex_independent_iff_not_mem_convex_hull_diff convexIndependent_iff_not_mem_convexHull_diff

/- warning: convex_independent_set_iff_inter_convex_hull_subset -> convexIndependent_set_iff_inter_convexHull_subset is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {s : Set.{u2} E}, Iff (ConvexIndependent.{u1, u2, u2} 𝕜 E (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) _inst_1 _inst_2 _inst_3 (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s))))) x)) (forall (t : Set.{u2} E), (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) t s) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) (Inter.inter.{u2} (Set.{u2} E) (Set.hasInter.{u2} E) s (coeFn.{succ u2, succ u2} (ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (fun (_x : ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) => (Set.{u2} E) -> (Set.{u2} E)) (ClosureOperator.hasCoeToFun.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) t)) t))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {s : Set.{u2} E}, Iff (ConvexIndependent.{u1, u2, u2} 𝕜 E (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s)) _inst_1 _inst_2 _inst_3 (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s))) (forall (t : Set.{u2} E), (HasSubset.Subset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) t s) -> (HasSubset.Subset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) (Inter.inter.{u2} (Set.{u2} E) (Set.instInterSet.{u2} E) s (OrderHom.toFun.{u2, u2} (Set.{u2} E) (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (ClosureOperator.toOrderHom.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)) t)) t))
Case conversion may be inaccurate. Consider using '#align convex_independent_set_iff_inter_convex_hull_subset convexIndependent_set_iff_inter_convexHull_subsetₓ'. -/
theorem convexIndependent_set_iff_inter_convexHull_subset {s : Set E} :
    ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀ t, t ⊆ s → s ∩ convexHull 𝕜 t ⊆ t :=
  by
  constructor
  · rintro hc t h x ⟨hxs, hxt⟩
    refine' hc { x | ↑x ∈ t } ⟨x, hxs⟩ _
    rw [Subtype.coe_image_of_subset h]
    exact hxt
  · intro hc t x h
    rw [← subtype.coe_injective.mem_set_image]
    exact hc (t.image coe) (Subtype.coe_image_subset s t) ⟨x.prop, h⟩
#align convex_independent_set_iff_inter_convex_hull_subset convexIndependent_set_iff_inter_convexHull_subset

/- warning: convex_independent_set_iff_not_mem_convex_hull_diff -> convexIndependent_set_iff_not_mem_convexHull_diff is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {s : Set.{u2} E}, Iff (ConvexIndependent.{u1, u2, u2} 𝕜 E (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) _inst_1 _inst_2 _inst_3 (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s))))) x)) (forall (x : E), (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s) -> (Not (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (coeFn.{succ u2, succ u2} (ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (fun (_x : ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) => (Set.{u2} E) -> (Set.{u2} E)) (ClosureOperator.hasCoeToFun.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) (SDiff.sdiff.{u2} (Set.{u2} E) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} E) (Set.booleanAlgebra.{u2} E)) s (Singleton.singleton.{u2, u2} E (Set.{u2} E) (Set.hasSingleton.{u2} E) x))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : OrderedSemiring.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (OrderedSemiring.toSemiring.{u1} 𝕜 _inst_1) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {s : Set.{u2} E}, Iff (ConvexIndependent.{u1, u2, u2} 𝕜 E (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s)) _inst_1 _inst_2 _inst_3 (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s))) (forall (x : E), (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s) -> (Not (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (OrderHom.toFun.{u2, u2} (Set.{u2} E) (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (ClosureOperator.toOrderHom.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (convexHull.{u1, u2} 𝕜 E _inst_1 (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)) (SDiff.sdiff.{u2} (Set.{u2} E) (Set.instSDiffSet.{u2} E) s (Singleton.singleton.{u2, u2} E (Set.{u2} E) (Set.instSingletonSet.{u2} E) x))))))
Case conversion may be inaccurate. Consider using '#align convex_independent_set_iff_not_mem_convex_hull_diff convexIndependent_set_iff_not_mem_convexHull_diffₓ'. -/
/-- If a set is convex independent, a point in the set is not in the convex hull of the other
points. See `convex_independent_iff_not_mem_convex_hull_diff` for the indexed family version.  -/
theorem convexIndependent_set_iff_not_mem_convexHull_diff {s : Set E} :
    ConvexIndependent 𝕜 (fun x => x : s → E) ↔ ∀ x ∈ s, x ∉ convexHull 𝕜 (s \ {x}) :=
  by
  rw [convexIndependent_set_iff_inter_convexHull_subset]
  constructor
  · rintro hs x hxs hx
    exact (hs _ (Set.diff_subset _ _) ⟨hxs, hx⟩).2 (Set.mem_singleton _)
  · rintro hs t ht x ⟨hxs, hxt⟩
    by_contra h
    exact hs _ hxs (convexHull_mono (Set.subset_diff_singleton ht h) hxt)
#align convex_independent_set_iff_not_mem_convex_hull_diff convexIndependent_set_iff_not_mem_convexHull_diff

end OrderedSemiring

section LinearOrderedField

variable [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

/- warning: convex_independent_iff_finset -> convexIndependent_iff_finset is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} {ι : Type.{u3}} [_inst_1 : LinearOrderedField.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (StrictOrderedRing.toRing.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, Iff (ConvexIndependent.{u1, u2, u3} 𝕜 E ι (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) _inst_2 _inst_3 p) (forall (s : Finset.{u3} ι) (x : ι), (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) (p x) (coeFn.{succ u2, succ u2} (ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (fun (_x : ClosureOperator.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) => (Set.{u2} E) -> (Set.{u2} E)) (ClosureOperator.hasCoeToFun.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (CompleteSemilatticeInf.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.toCompleteSemilatticeInf.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.completeBooleanAlgebra.{u2} E)))))))) (convexHull.{u1, u2} 𝕜 E (StrictOrderedSemiring.toOrderedSemiring.{u1} 𝕜 (StrictOrderedRing.toStrictOrderedSemiring.{u1} 𝕜 (LinearOrderedRing.toStrictOrderedRing.{u1} 𝕜 (LinearOrderedCommRing.toLinearOrderedRing.{u1} 𝕜 (LinearOrderedField.toLinearOrderedCommRing.{u1} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} E) (Set.{u2} E) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} E) (Set.{u2} E) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} E) (Set.{u2} E) (Finset.Set.hasCoeT.{u2} E))) (Finset.image.{u3, u2} ι E (fun (a : E) (b : E) => Classical.propDecidable (Eq.{succ u2} E a b)) p s)))) -> (Membership.Mem.{u3, u3} ι (Finset.{u3} ι) (Finset.hasMem.{u3} ι) x s))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} {ι : Type.{u1}} [_inst_1 : LinearOrderedField.{u3} 𝕜] [_inst_2 : AddCommGroup.{u2} E] [_inst_3 : Module.{u3, u2} 𝕜 E (StrictOrderedSemiring.toSemiring.{u3} 𝕜 (LinearOrderedSemiring.toStrictOrderedSemiring.{u3} 𝕜 (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u3} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u3} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u3} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2)] {p : ι -> E}, Iff (ConvexIndependent.{u3, u2, u1} 𝕜 E ι (OrderedCommSemiring.toOrderedSemiring.{u3} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u3} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u3} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u3} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u3} 𝕜 _inst_1))))) _inst_2 _inst_3 p) (forall (s : Finset.{u1} ι) (x : ι), (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) (p x) (OrderHom.toFun.{u2, u2} (Set.{u2} E) (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (ClosureOperator.toOrderHom.{u2} (Set.{u2} E) (PartialOrder.toPreorder.{u2} (Set.{u2} E) (OmegaCompletePartialOrder.toPartialOrder.{u2} (Set.{u2} E) (CompleteLattice.instOmegaCompletePartialOrder.{u2} (Set.{u2} E) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} E) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} E) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} E) (Set.instCompleteBooleanAlgebraSet.{u2} E))))))) (convexHull.{u3, u2} 𝕜 E (OrderedCommSemiring.toOrderedSemiring.{u3} 𝕜 (StrictOrderedCommSemiring.toOrderedCommSemiring.{u3} 𝕜 (LinearOrderedCommSemiring.toStrictOrderedCommSemiring.{u3} 𝕜 (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u3} 𝕜 (LinearOrderedField.toLinearOrderedSemifield.{u3} 𝕜 _inst_1))))) (AddCommGroup.toAddCommMonoid.{u2} E _inst_2) _inst_3)) (Finset.toSet.{u2} E (Finset.image.{u1, u2} ι E (fun (a : E) (b : E) => Classical.propDecidable (Eq.{succ u2} E a b)) p s)))) -> (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) x s))
Case conversion may be inaccurate. Consider using '#align convex_independent_iff_finset convexIndependent_iff_finsetₓ'. -/
/-- To check convex independence, one only has to check finsets thanks to Carathéodory's theorem. -/
theorem convexIndependent_iff_finset {p : ι → E} :
    ConvexIndependent 𝕜 p ↔
      ∀ (s : Finset ι) (x : ι), p x ∈ convexHull 𝕜 (s.image p : Set E) → x ∈ s :=
  by
  refine' ⟨fun hc s x hx => hc s x _, fun h s x hx => _⟩
  · rwa [Finset.coe_image] at hx
  have hp : injective p := by
    rintro a b hab
    rw [← mem_singleton]
    refine' h {b} a _
    rw [hab, image_singleton, coe_singleton, convexHull_singleton]
    exact Set.mem_singleton _
  rw [convexHull_eq_union_convexHull_finite_subsets] at hx
  simp_rw [Set.mem_iUnion] at hx
  obtain ⟨t, ht, hx⟩ := hx
  rw [← hp.mem_set_image]
  refine' ht _
  suffices x ∈ t.preimage p (hp.inj_on _) by rwa [mem_preimage, ← mem_coe] at this
  refine' h _ x _
  rwa [t.image_preimage p (hp.inj_on _), filter_true_of_mem]
  · exact fun y hy => s.image_subset_range p (ht <| mem_coe.2 hy)
#align convex_independent_iff_finset convexIndependent_iff_finset

/-! ### Extreme points -/


/- warning: convex.convex_independent_extreme_points -> Convex.convexIndependent_extremePoints is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align convex.convex_independent_extreme_points Convex.convexIndependent_extremePointsₓ'. -/
theorem Convex.convexIndependent_extremePoints (hs : Convex 𝕜 s) :
    ConvexIndependent 𝕜 (fun p => p : s.extremePoints 𝕜 → E) :=
  convexIndependent_set_iff_not_mem_convexHull_diff.2 fun x hx h =>
    (extremePoints_convexHull_subset
          (inter_extremePoints_subset_extremePoints_of_subset
            (convexHull_min ((Set.diff_subset _ _).trans extremePoints_subset) hs) ⟨h, hx⟩)).2
      (Set.mem_singleton _)
#align convex.convex_independent_extreme_points Convex.convexIndependent_extremePoints

end LinearOrderedField

