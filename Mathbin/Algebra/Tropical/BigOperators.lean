/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky

! This file was ported from Lean 3 source module algebra.tropical.big_operators
! leanprover-community/mathlib commit dde670c9a3f503647fd5bfdf1037bad526d3397a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.List.MinMax
import Mathbin.Algebra.Tropical.Basic
import Mathbin.Order.ConditionallyCompleteLattice.Finset

/-!

# Tropicalization of finitary operations

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides the "big-op" or notation-based finitary operations on tropicalized types.
This allows easy conversion between sums to Infs and prods to sums. Results here are important
for expressing that evaluation of tropical polynomials are the minimum over a finite piecewise
collection of linear functions.

## Main declarations

* `untrop_sum`

## Implementation notes

No concrete (semi)ring is used here, only ones with inferrable order/lattice structure, to support
real, rat, ereal, and others (erat is not yet defined).

Minima over `list α` are defined as producing a value in `with_top α` so proofs about lists do not
directly transfer to minima over multisets or finsets.

-/


open BigOperators

variable {R S : Type _}

open Tropical Finset

/- warning: list.trop_sum -> List.trop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] (l : List.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (List.sum.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) l)) (List.prod.{u1} (Tropical.{u1} R) (Tropical.hasMul.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) (Tropical.hasOne.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) (List.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] (l : List.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (List.sum.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddMonoid.toZero.{u1} R _inst_1) l)) (List.prod.{u1} (Tropical.{u1} R) (Tropical.instMulTropical.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) (Tropical.instOneTropical.{u1} R (AddMonoid.toZero.{u1} R _inst_1)) (List.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) l))
Case conversion may be inaccurate. Consider using '#align list.trop_sum List.trop_sumₓ'. -/
theorem List.trop_sum [AddMonoid R] (l : List R) : trop l.Sum = List.prod (l.map trop) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [← IH]
#align list.trop_sum List.trop_sum

/- warning: multiset.trop_sum -> Multiset.trop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] (s : Multiset.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Multiset.sum.{u1} R _inst_1 s)) (Multiset.prod.{u1} (Tropical.{u1} R) (Tropical.commMonoid.{u1} R _inst_1) (Multiset.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] (s : Multiset.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Multiset.sum.{u1} R _inst_1 s)) (Multiset.prod.{u1} (Tropical.{u1} R) (Tropical.instCommMonoidTropical.{u1} R _inst_1) (Multiset.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) s))
Case conversion may be inaccurate. Consider using '#align multiset.trop_sum Multiset.trop_sumₓ'. -/
theorem Multiset.trop_sum [AddCommMonoid R] (s : Multiset R) :
    trop s.Sum = Multiset.prod (s.map trop) :=
  Quotient.inductionOn s (by simpa using List.trop_sum)
#align multiset.trop_sum Multiset.trop_sum

/- warning: trop_sum -> trop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} R] (s : Finset.{u2} S) (f : S -> R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Finset.sum.{u1, u2} R S _inst_1 s (fun (i : S) => f i))) (Finset.prod.{u1, u2} (Tropical.{u1} R) S (Tropical.commMonoid.{u1} R _inst_1) s (fun (i : S) => Tropical.trop.{u1} R (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} R] (s : Finset.{u1} S) (f : S -> R), Eq.{succ u2} (Tropical.{u2} R) (Tropical.trop.{u2} R (Finset.sum.{u2, u1} R S _inst_1 s (fun (i : S) => f i))) (Finset.prod.{u2, u1} (Tropical.{u2} R) S (Tropical.instCommMonoidTropical.{u2} R _inst_1) s (fun (i : S) => Tropical.trop.{u2} R (f i)))
Case conversion may be inaccurate. Consider using '#align trop_sum trop_sumₓ'. -/
theorem trop_sum [AddCommMonoid R] (s : Finset S) (f : S → R) :
    trop (∑ i in s, f i) = ∏ i in s, trop (f i) :=
  by
  cases s
  convert Multiset.trop_sum _
  simp
#align trop_sum trop_sum

/- warning: list.untrop_prod -> List.untrop_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] (l : List.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (List.prod.{u1} (Tropical.{u1} R) (Tropical.hasMul.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) (Tropical.hasOne.{u1} R (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) l)) (List.sum.{u1} R (AddZeroClass.toHasAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddZeroClass.toHasZero.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (List.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddMonoid.{u1} R] (l : List.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (List.prod.{u1} (Tropical.{u1} R) (Tropical.instMulTropical.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1))) (Tropical.instOneTropical.{u1} R (AddMonoid.toZero.{u1} R _inst_1)) l)) (List.sum.{u1} R (AddZeroClass.toAdd.{u1} R (AddMonoid.toAddZeroClass.{u1} R _inst_1)) (AddMonoid.toZero.{u1} R _inst_1) (List.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) l))
Case conversion may be inaccurate. Consider using '#align list.untrop_prod List.untrop_prodₓ'. -/
theorem List.untrop_prod [AddMonoid R] (l : List (Tropical R)) :
    untrop l.Prod = List.sum (l.map untrop) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [← IH]
#align list.untrop_prod List.untrop_prod

/- warning: multiset.untrop_prod -> Multiset.untrop_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] (s : Multiset.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Multiset.prod.{u1} (Tropical.{u1} R) (Tropical.commMonoid.{u1} R _inst_1) s)) (Multiset.sum.{u1} R _inst_1 (Multiset.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : AddCommMonoid.{u1} R] (s : Multiset.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Multiset.prod.{u1} (Tropical.{u1} R) (Tropical.instCommMonoidTropical.{u1} R _inst_1) s)) (Multiset.sum.{u1} R _inst_1 (Multiset.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) s))
Case conversion may be inaccurate. Consider using '#align multiset.untrop_prod Multiset.untrop_prodₓ'. -/
theorem Multiset.untrop_prod [AddCommMonoid R] (s : Multiset (Tropical R)) :
    untrop s.Prod = Multiset.sum (s.map untrop) :=
  Quotient.inductionOn s (by simpa using List.untrop_prod)
#align multiset.untrop_prod Multiset.untrop_prod

/- warning: untrop_prod -> untrop_prod is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : AddCommMonoid.{u1} R] (s : Finset.{u2} S) (f : S -> (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Finset.prod.{u1, u2} (Tropical.{u1} R) S (Tropical.commMonoid.{u1} R _inst_1) s (fun (i : S) => f i))) (Finset.sum.{u1, u2} R S _inst_1 s (fun (i : S) => Tropical.untrop.{u1} R (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : AddCommMonoid.{u2} R] (s : Finset.{u1} S) (f : S -> (Tropical.{u2} R)), Eq.{succ u2} R (Tropical.untrop.{u2} R (Finset.prod.{u2, u1} (Tropical.{u2} R) S (Tropical.instCommMonoidTropical.{u2} R _inst_1) s (fun (i : S) => f i))) (Finset.sum.{u2, u1} R S _inst_1 s (fun (i : S) => Tropical.untrop.{u2} R (f i)))
Case conversion may be inaccurate. Consider using '#align untrop_prod untrop_prodₓ'. -/
theorem untrop_prod [AddCommMonoid R] (s : Finset S) (f : S → Tropical R) :
    untrop (∏ i in s, f i) = ∑ i in s, untrop (f i) :=
  by
  cases s
  convert Multiset.untrop_prod _
  simp
#align untrop_prod untrop_prod

#print List.trop_minimum /-
theorem List.trop_minimum [LinearOrder R] (l : List R) :
    trop l.minimum = List.sum (l.map (trop ∘ coe)) :=
  by
  induction' l with hd tl IH
  · simp
  · simp [List.minimum_cons, ← IH]
#align list.trop_minimum List.trop_minimum
-/

/- warning: multiset.trop_inf -> Multiset.trop_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))] (s : Multiset.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Multiset.inf.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)) _inst_2 s)) (Multiset.sum.{u1} (Tropical.{u1} R) (Tropical.addCommMonoid.{u1} R _inst_1 _inst_2) (Multiset.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))] (s : Multiset.{u1} R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Multiset.inf.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))) _inst_2 s)) (Multiset.sum.{u1} (Tropical.{u1} R) (Tropical.instAddCommMonoidTropical.{u1} R _inst_1 _inst_2) (Multiset.map.{u1, u1} R (Tropical.{u1} R) (Tropical.trop.{u1} R) s))
Case conversion may be inaccurate. Consider using '#align multiset.trop_inf Multiset.trop_infₓ'. -/
theorem Multiset.trop_inf [LinearOrder R] [OrderTop R] (s : Multiset R) :
    trop s.inf = Multiset.sum (s.map trop) :=
  by
  induction' s using Multiset.induction with s x IH
  · simp
  · simp [← IH]
#align multiset.trop_inf Multiset.trop_inf

/- warning: finset.trop_inf -> Finset.trop_inf is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))] (s : Finset.{u2} S) (f : S -> R), Eq.{succ u1} (Tropical.{u1} R) (Tropical.trop.{u1} R (Finset.inf.{u1, u2} R S (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)) _inst_2 s f)) (Finset.sum.{u1, u2} (Tropical.{u1} R) S (Tropical.addCommMonoid.{u1} R _inst_1 _inst_2) s (fun (i : S) => Tropical.trop.{u1} R (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : LinearOrder.{u2} R] [_inst_2 : OrderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeInf.toPartialOrder.{u2} R (Lattice.toSemilatticeInf.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R _inst_1))))))] (s : Finset.{u1} S) (f : S -> R), Eq.{succ u2} (Tropical.{u2} R) (Tropical.trop.{u2} R (Finset.inf.{u2, u1} R S (Lattice.toSemilatticeInf.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R _inst_1))) _inst_2 s f)) (Finset.sum.{u2, u1} (Tropical.{u2} R) S (Tropical.instAddCommMonoidTropical.{u2} R _inst_1 _inst_2) s (fun (i : S) => Tropical.trop.{u2} R (f i)))
Case conversion may be inaccurate. Consider using '#align finset.trop_inf Finset.trop_infₓ'. -/
theorem Finset.trop_inf [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → R) :
    trop (s.inf f) = ∑ i in s, trop (f i) := by
  cases s
  convert Multiset.trop_inf _
  simp
#align finset.trop_inf Finset.trop_inf

/- warning: trop_Inf_image -> trop_infₛ_image is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} R] (s : Finset.{u2} S) (f : S -> (WithTop.{u1} R)), Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.trop.{u1} (WithTop.{u1} R) (InfSet.infₛ.{u1} (WithTop.{u1} R) (WithTop.hasInf.{u1} R (ConditionallyCompleteLattice.toHasInf.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1))) (Set.image.{u2, u1} S (WithTop.{u1} R) f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} S) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} S) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} S) (Set.{u2} S) (Finset.Set.hasCoeT.{u2} S))) s)))) (Finset.sum.{u1, u2} (Tropical.{u1} (WithTop.{u1} R)) S (Tropical.addCommMonoid.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} R _inst_1)) (WithTop.orderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (ConditionallyCompleteLattice.toLattice.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1)))))))) s (fun (i : S) => Tropical.trop.{u1} (WithTop.{u1} R) (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u2} R] (s : Finset.{u1} S) (f : S -> (WithTop.{u2} R)), Eq.{succ u2} (Tropical.{u2} (WithTop.{u2} R)) (Tropical.trop.{u2} (WithTop.{u2} R) (InfSet.infₛ.{u2} (WithTop.{u2} R) (instInfSetWithTop.{u2} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R _inst_1))) (Set.image.{u1, u2} S (WithTop.{u2} R) f (Finset.toSet.{u1} S s)))) (Finset.sum.{u2, u1} (Tropical.{u2} (WithTop.{u2} R)) S (Tropical.instAddCommMonoidTropical.{u2} (WithTop.{u2} R) (WithTop.linearOrder.{u2} R (instLinearOrder.{u2} R _inst_1)) (WithTop.orderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeSup.toPartialOrder.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (instLinearOrder.{u2} R _inst_1))))))))) s (fun (i : S) => Tropical.trop.{u2} (WithTop.{u2} R) (f i)))
Case conversion may be inaccurate. Consider using '#align trop_Inf_image trop_infₛ_imageₓ'. -/
theorem trop_infₛ_image [ConditionallyCompleteLinearOrder R] (s : Finset S) (f : S → WithTop R) :
    trop (infₛ (f '' s)) = ∑ i in s, trop (f i) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.infₛ_empty, trop_top]
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, s.trop_inf]
#align trop_Inf_image trop_infₛ_image

/- warning: trop_infi -> trop_infᵢ is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} R] [_inst_2 : Fintype.{u2} S] (f : S -> (WithTop.{u1} R)), Eq.{succ u1} (Tropical.{u1} (WithTop.{u1} R)) (Tropical.trop.{u1} (WithTop.{u1} R) (infᵢ.{u1, succ u2} (WithTop.{u1} R) (WithTop.hasInf.{u1} R (ConditionallyCompleteLattice.toHasInf.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1))) S (fun (i : S) => f i))) (Finset.sum.{u1, u2} (Tropical.{u1} (WithTop.{u1} R)) S (Tropical.addCommMonoid.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} R _inst_1)) (WithTop.orderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (ConditionallyCompleteLattice.toLattice.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1)))))))) (Finset.univ.{u2} S _inst_2) (fun (i : S) => Tropical.trop.{u1} (WithTop.{u1} R) (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u2} R] [_inst_2 : Fintype.{u1} S] (f : S -> (WithTop.{u2} R)), Eq.{succ u2} (Tropical.{u2} (WithTop.{u2} R)) (Tropical.trop.{u2} (WithTop.{u2} R) (infᵢ.{u2, succ u1} (WithTop.{u2} R) (instInfSetWithTop.{u2} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R _inst_1))) S (fun (i : S) => f i))) (Finset.sum.{u2, u1} (Tropical.{u2} (WithTop.{u2} R)) S (Tropical.instAddCommMonoidTropical.{u2} (WithTop.{u2} R) (WithTop.linearOrder.{u2} R (instLinearOrder.{u2} R _inst_1)) (WithTop.orderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeSup.toPartialOrder.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (instLinearOrder.{u2} R _inst_1))))))))) (Finset.univ.{u1} S _inst_2) (fun (i : S) => Tropical.trop.{u2} (WithTop.{u2} R) (f i)))
Case conversion may be inaccurate. Consider using '#align trop_infi trop_infᵢₓ'. -/
theorem trop_infᵢ [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → WithTop R) :
    trop (⨅ i : S, f i) = ∑ i : S, trop (f i) := by
  rw [infᵢ, ← Set.image_univ, ← coe_univ, trop_infₛ_image]
#align trop_infi trop_infᵢ

/- warning: multiset.untrop_sum -> Multiset.untrop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))] (s : Multiset.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Multiset.sum.{u1} (Tropical.{u1} R) (Tropical.addCommMonoid.{u1} R _inst_1 _inst_2) s)) (Multiset.inf.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)) _inst_2 (Multiset.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) s))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))))))] (s : Multiset.{u1} (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Multiset.sum.{u1} (Tropical.{u1} R) (Tropical.instAddCommMonoidTropical.{u1} R _inst_1 _inst_2) s)) (Multiset.inf.{u1} R (Lattice.toSemilatticeInf.{u1} R (DistribLattice.toLattice.{u1} R (instDistribLattice.{u1} R _inst_1))) _inst_2 (Multiset.map.{u1, u1} (Tropical.{u1} R) R (Tropical.untrop.{u1} R) s))
Case conversion may be inaccurate. Consider using '#align multiset.untrop_sum Multiset.untrop_sumₓ'. -/
theorem Multiset.untrop_sum [LinearOrder R] [OrderTop R] (s : Multiset (Tropical R)) :
    untrop s.Sum = Multiset.inf (s.map untrop) :=
  by
  induction' s using Multiset.induction with s x IH
  · simp
  · simpa [← IH]
#align multiset.untrop_sum Multiset.untrop_sum

/- warning: finset.untrop_sum' -> Finset.untrop_sum' is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : LinearOrder.{u1} R] [_inst_2 : OrderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)))))] (s : Finset.{u2} S) (f : S -> (Tropical.{u1} R)), Eq.{succ u1} R (Tropical.untrop.{u1} R (Finset.sum.{u1, u2} (Tropical.{u1} R) S (Tropical.addCommMonoid.{u1} R _inst_1 _inst_2) s (fun (i : S) => f i))) (Finset.inf.{u1, u2} R S (Lattice.toSemilatticeInf.{u1} R (LinearOrder.toLattice.{u1} R _inst_1)) _inst_2 s (Function.comp.{succ u2, succ u1, succ u1} S (Tropical.{u1} R) R (Tropical.untrop.{u1} R) f))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : LinearOrder.{u2} R] [_inst_2 : OrderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeInf.toPartialOrder.{u2} R (Lattice.toSemilatticeInf.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R _inst_1))))))] (s : Finset.{u1} S) (f : S -> (Tropical.{u2} R)), Eq.{succ u2} R (Tropical.untrop.{u2} R (Finset.sum.{u2, u1} (Tropical.{u2} R) S (Tropical.instAddCommMonoidTropical.{u2} R _inst_1 _inst_2) s (fun (i : S) => f i))) (Finset.inf.{u2, u1} R S (Lattice.toSemilatticeInf.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R _inst_1))) _inst_2 s (Function.comp.{succ u1, succ u2, succ u2} S (Tropical.{u2} R) R (Tropical.untrop.{u2} R) f))
Case conversion may be inaccurate. Consider using '#align finset.untrop_sum' Finset.untrop_sum'ₓ'. -/
theorem Finset.untrop_sum' [LinearOrder R] [OrderTop R] (s : Finset S) (f : S → Tropical R) :
    untrop (∑ i in s, f i) = s.inf (untrop ∘ f) :=
  by
  cases s
  convert Multiset.untrop_sum _
  simpa
#align finset.untrop_sum' Finset.untrop_sum'

/- warning: untrop_sum_eq_Inf_image -> untrop_sum_eq_infₛ_image is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} R] (s : Finset.{u2} S) (f : S -> (Tropical.{u1} (WithTop.{u1} R))), Eq.{succ u1} (WithTop.{u1} R) (Tropical.untrop.{u1} (WithTop.{u1} R) (Finset.sum.{u1, u2} (Tropical.{u1} (WithTop.{u1} R)) S (Tropical.addCommMonoid.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} R _inst_1)) (WithTop.orderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (ConditionallyCompleteLattice.toLattice.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1)))))))) s (fun (i : S) => f i))) (InfSet.infₛ.{u1} (WithTop.{u1} R) (WithTop.hasInf.{u1} R (ConditionallyCompleteLattice.toHasInf.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1))) (Set.image.{u2, u1} S (WithTop.{u1} R) (Function.comp.{succ u2, succ u1, succ u1} S (Tropical.{u1} (WithTop.{u1} R)) (WithTop.{u1} R) (Tropical.untrop.{u1} (WithTop.{u1} R)) f) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (Finset.{u2} S) (Set.{u2} S) (HasLiftT.mk.{succ u2, succ u2} (Finset.{u2} S) (Set.{u2} S) (CoeTCₓ.coe.{succ u2, succ u2} (Finset.{u2} S) (Set.{u2} S) (Finset.Set.hasCoeT.{u2} S))) s)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u2} R] (s : Finset.{u1} S) (f : S -> (Tropical.{u2} (WithTop.{u2} R))), Eq.{succ u2} (WithTop.{u2} R) (Tropical.untrop.{u2} (WithTop.{u2} R) (Finset.sum.{u2, u1} (Tropical.{u2} (WithTop.{u2} R)) S (Tropical.instAddCommMonoidTropical.{u2} (WithTop.{u2} R) (WithTop.linearOrder.{u2} R (instLinearOrder.{u2} R _inst_1)) (WithTop.orderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeSup.toPartialOrder.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (instLinearOrder.{u2} R _inst_1))))))))) s (fun (i : S) => f i))) (InfSet.infₛ.{u2} (WithTop.{u2} R) (instInfSetWithTop.{u2} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R _inst_1))) (Set.image.{u1, u2} S (WithTop.{u2} R) (Function.comp.{succ u1, succ u2, succ u2} S (Tropical.{u2} (WithTop.{u2} R)) (WithTop.{u2} R) (Tropical.untrop.{u2} (WithTop.{u2} R)) f) (Finset.toSet.{u1} S s)))
Case conversion may be inaccurate. Consider using '#align untrop_sum_eq_Inf_image untrop_sum_eq_infₛ_imageₓ'. -/
theorem untrop_sum_eq_infₛ_image [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = infₛ (untrop ∘ f '' s) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · simp only [Set.image_empty, coe_empty, sum_empty, WithTop.infₛ_empty, untrop_zero]
  rw [← inf'_eq_cInf_image _ h, inf'_eq_inf, Finset.untrop_sum']
#align untrop_sum_eq_Inf_image untrop_sum_eq_infₛ_image

/- warning: untrop_sum -> untrop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} R] [_inst_2 : Fintype.{u2} S] (f : S -> (Tropical.{u1} (WithTop.{u1} R))), Eq.{succ u1} (WithTop.{u1} R) (Tropical.untrop.{u1} (WithTop.{u1} R) (Finset.sum.{u1, u2} (Tropical.{u1} (WithTop.{u1} R)) S (Tropical.addCommMonoid.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} R _inst_1)) (WithTop.orderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (ConditionallyCompleteLattice.toLattice.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1)))))))) (Finset.univ.{u2} S _inst_2) (fun (i : S) => f i))) (infᵢ.{u1, succ u2} (WithTop.{u1} R) (WithTop.hasInf.{u1} R (ConditionallyCompleteLattice.toHasInf.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1))) S (fun (i : S) => Tropical.untrop.{u1} (WithTop.{u1} R) (f i)))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u2} R] [_inst_2 : Fintype.{u1} S] (f : S -> (Tropical.{u2} (WithTop.{u2} R))), Eq.{succ u2} (WithTop.{u2} R) (Tropical.untrop.{u2} (WithTop.{u2} R) (Finset.sum.{u2, u1} (Tropical.{u2} (WithTop.{u2} R)) S (Tropical.instAddCommMonoidTropical.{u2} (WithTop.{u2} R) (WithTop.linearOrder.{u2} R (instLinearOrder.{u2} R _inst_1)) (WithTop.orderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeSup.toPartialOrder.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (instLinearOrder.{u2} R _inst_1))))))))) (Finset.univ.{u1} S _inst_2) (fun (i : S) => f i))) (infᵢ.{u2, succ u1} (WithTop.{u2} R) (instInfSetWithTop.{u2} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R _inst_1))) S (fun (i : S) => Tropical.untrop.{u2} (WithTop.{u2} R) (f i)))
Case conversion may be inaccurate. Consider using '#align untrop_sum untrop_sumₓ'. -/
theorem untrop_sum [ConditionallyCompleteLinearOrder R] [Fintype S] (f : S → Tropical (WithTop R)) :
    untrop (∑ i : S, f i) = ⨅ i : S, untrop (f i) := by
  rw [infᵢ, ← Set.image_univ, ← coe_univ, untrop_sum_eq_infₛ_image]
#align untrop_sum untrop_sum

/- warning: finset.untrop_sum -> Finset.untrop_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} {S : Type.{u2}} [_inst_1 : ConditionallyCompleteLinearOrder.{u1} R] (s : Finset.{u2} S) (f : S -> (Tropical.{u1} (WithTop.{u1} R))), Eq.{succ u1} (WithTop.{u1} R) (Tropical.untrop.{u1} (WithTop.{u1} R) (Finset.sum.{u1, u2} (Tropical.{u1} (WithTop.{u1} R)) S (Tropical.addCommMonoid.{u1} (WithTop.{u1} R) (WithTop.linearOrder.{u1} R (ConditionallyCompleteLinearOrder.toLinearOrder.{u1} R _inst_1)) (WithTop.orderTop.{u1} R (Preorder.toLE.{u1} R (PartialOrder.toPreorder.{u1} R (SemilatticeInf.toPartialOrder.{u1} R (Lattice.toSemilatticeInf.{u1} R (ConditionallyCompleteLattice.toLattice.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1)))))))) s (fun (i : S) => f i))) (infᵢ.{u1, succ u2} (WithTop.{u1} R) (WithTop.hasInf.{u1} R (ConditionallyCompleteLattice.toHasInf.{u1} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u1} R _inst_1))) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) (fun (i : coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) => Tropical.untrop.{u1} (WithTop.{u1} R) (f ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) S (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) S (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) S (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Finset.{u2} S) Type.{u2} (Finset.hasCoeToSort.{u2} S) s) S (coeSubtype.{succ u2} S (fun (x : S) => Membership.Mem.{u2, u2} S (Finset.{u2} S) (Finset.hasMem.{u2} S) x s))))) i))))
but is expected to have type
  forall {R : Type.{u2}} {S : Type.{u1}} [_inst_1 : ConditionallyCompleteLinearOrder.{u2} R] (s : Finset.{u1} S) (f : S -> (Tropical.{u2} (WithTop.{u2} R))), Eq.{succ u2} (WithTop.{u2} R) (Tropical.untrop.{u2} (WithTop.{u2} R) (Finset.sum.{u2, u1} (Tropical.{u2} (WithTop.{u2} R)) S (Tropical.instAddCommMonoidTropical.{u2} (WithTop.{u2} R) (WithTop.linearOrder.{u2} R (instLinearOrder.{u2} R _inst_1)) (WithTop.orderTop.{u2} R (Preorder.toLE.{u2} R (PartialOrder.toPreorder.{u2} R (SemilatticeSup.toPartialOrder.{u2} R (Lattice.toSemilatticeSup.{u2} R (DistribLattice.toLattice.{u2} R (instDistribLattice.{u2} R (instLinearOrder.{u2} R _inst_1))))))))) s (fun (i : S) => f i))) (infᵢ.{u2, succ u1} (WithTop.{u2} R) (instInfSetWithTop.{u2} R (ConditionallyCompleteLattice.toInfSet.{u2} R (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} R _inst_1))) (Subtype.{succ u1} S (fun (x : S) => Membership.mem.{u1, u1} S (Finset.{u1} S) (Finset.instMembershipFinset.{u1} S) x s)) (fun (i : Subtype.{succ u1} S (fun (x : S) => Membership.mem.{u1, u1} S (Finset.{u1} S) (Finset.instMembershipFinset.{u1} S) x s)) => Tropical.untrop.{u2} (WithTop.{u2} R) (f (Subtype.val.{succ u1} S (fun (x : S) => Membership.mem.{u1, u1} S (Finset.{u1} S) (Finset.instMembershipFinset.{u1} S) x s) i))))
Case conversion may be inaccurate. Consider using '#align finset.untrop_sum Finset.untrop_sumₓ'. -/
/-- Note we cannot use `i ∈ s` instead of `i : s` here
as it is simply not true on conditionally complete lattices! -/
theorem Finset.untrop_sum [ConditionallyCompleteLinearOrder R] (s : Finset S)
    (f : S → Tropical (WithTop R)) : untrop (∑ i in s, f i) = ⨅ i : s, untrop (f i) := by
  simpa [← untrop_sum] using sum_attach.symm
#align finset.untrop_sum Finset.untrop_sum

