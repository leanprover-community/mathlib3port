/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne

! This file was ported from Lean 3 source module analysis.special_functions.log.basic
! leanprover-community/mathlib commit a8b2226cfb0a79f5986492053fc49b1a0c6aeffb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Exp
import Mathbin.Data.Nat.Factorization.Basic

/-!
# Real logarithm

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `real.log` to be the logarithm of a real number. As usual, we extend it from
its domain `(0, +∞)` to a globally defined function. We choose to do it so that `log 0 = 0` and
`log (-x) = log x`.

We prove some basic properties of this function and show that it is continuous.

## Tags

logarithm, continuity
-/


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : ℝ}

#print Real.log /-
/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot]
noncomputable def log (x : ℝ) : ℝ :=
  if hx : x = 0 then 0 else expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩
#align real.log Real.log
-/

/- warning: real.log_of_ne_zero -> Real.log_of_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real} (hx : Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))), Eq.{1} Real (Real.log x) (coeFn.{1, 1} (OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) Real.hasLe) (fun (_x : RelIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (LE.le.{0} Real Real.hasLe)) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> Real) (RelIso.hasCoeToFun.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (LE.le.{0} Real Real.hasLe)) (OrderIso.symm.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.hasLe (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) Real.expOrderIso) (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x) (Iff.mpr (LT.lt.{0} Real (Preorder.toHasLt.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (SubNegMonoid.toAddMonoid.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup))))))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real (SubNegMonoid.toHasNeg.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) (SemilatticeSup.toHasSup.{0} Real (Lattice.toSemilatticeSup.{0} Real (LinearOrder.toLattice.{0} Real Real.linearOrder)))) x)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real (AddZeroClass.toHasZero.{0} Real (AddMonoid.toAddZeroClass.{0} Real (SubNegMonoid.toAddMonoid.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)))))))) (abs_pos.{0} Real Real.addGroup Real.linearOrder (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup) x) hx)))
but is expected to have type
  forall {x : Real} (hx : Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))), Eq.{1} Real (Real.log x) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (_x : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => Real) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (OrderIso.symm.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real.instLEReal (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) Real.expOrderIso) (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x) (Iff.mpr (LT.lt.{0} Real (Preorder.toLT.{0} Real (PartialOrder.toPreorder.{0} Real (SemilatticeInf.toPartialOrder.{0} Real (Lattice.toSemilatticeInf.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder)))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real (NegZeroClass.toZero.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal)))))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real (NegZeroClass.toNeg.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal)))) (SemilatticeSup.toSup.{0} Real (Lattice.toSemilatticeSup.{0} Real (DistribLattice.toLattice.{0} Real (instDistribLattice.{0} Real Real.linearOrder))))) x)) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real (NegZeroClass.toZero.{0} Real (SubNegZeroMonoid.toNegZeroClass.{0} Real (SubtractionMonoid.toSubNegZeroMonoid.{0} Real (AddGroup.toSubtractionMonoid.{0} Real Real.instAddGroupReal))))))) (abs_pos.{0} Real Real.instAddGroupReal Real.linearOrder (OrderedAddCommGroup.to_covariantClass_left_le.{0} Real Real.orderedAddCommGroup) x) hx)))
Case conversion may be inaccurate. Consider using '#align real.log_of_ne_zero Real.log_of_ne_zeroₓ'. -/
theorem log_of_ne_zero (hx : x ≠ 0) : log x = expOrderIso.symm ⟨|x|, abs_pos.2 hx⟩ :=
  dif_neg hx
#align real.log_of_ne_zero Real.log_of_ne_zero

/- warning: real.log_of_pos -> Real.log_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real} (hx : LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x), Eq.{1} Real (Real.log x) (coeFn.{1, 1} (OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) Real.hasLe) (fun (_x : RelIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (LE.le.{0} Real Real.hasLe)) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> Real) (RelIso.hasCoeToFun.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))))) (LE.le.{0} Real Real.hasLe)) (OrderIso.symm.{0, 0} Real (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real.hasLe (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) Real.expOrderIso) (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) x hx))
but is expected to have type
  forall {x : Real} (hx : LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x), Eq.{1} Real (Real.log x) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (fun (_x : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => Real) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Real) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Real) => LE.le.{0} Real Real.instLEReal x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) (OrderIso.symm.{0, 0} Real (Set.Elem.{0} Real (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real.instLEReal (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) Real.expOrderIso) (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) x hx))
Case conversion may be inaccurate. Consider using '#align real.log_of_pos Real.log_of_posₓ'. -/
theorem log_of_pos (hx : 0 < x) : log x = expOrderIso.symm ⟨x, hx⟩ :=
  by
  rw [log_of_ne_zero hx.ne']
  congr
  exact abs_of_pos hx
#align real.log_of_pos Real.log_of_pos

/- warning: real.exp_log_eq_abs -> Real.exp_log_eq_abs is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.exp (Real.log x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x))
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.exp (Real.log x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x))
Case conversion may be inaccurate. Consider using '#align real.exp_log_eq_abs Real.exp_log_eq_absₓ'. -/
theorem exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = |x| := by
  rw [log_of_ne_zero hx, ← coe_exp_order_iso_apply, OrderIso.apply_symm_apply, Subtype.coe_mk]
#align real.exp_log_eq_abs Real.exp_log_eq_abs

/- warning: real.exp_log -> Real.exp_log is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.exp (Real.log x)) x)
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.exp (Real.log x)) x)
Case conversion may be inaccurate. Consider using '#align real.exp_log Real.exp_logₓ'. -/
theorem exp_log (hx : 0 < x) : exp (log x) = x :=
  by
  rw [exp_log_eq_abs hx.ne']
  exact abs_of_pos hx
#align real.exp_log Real.exp_log

/- warning: real.exp_log_of_neg -> Real.exp_log_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.exp (Real.log x)) (Neg.neg.{0} Real Real.hasNeg x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.exp (Real.log x)) (Neg.neg.{0} Real Real.instNegReal x))
Case conversion may be inaccurate. Consider using '#align real.exp_log_of_neg Real.exp_log_of_negₓ'. -/
theorem exp_log_of_neg (hx : x < 0) : exp (log x) = -x :=
  by
  rw [exp_log_eq_abs (ne_of_lt hx)]
  exact abs_of_neg hx
#align real.exp_log_of_neg Real.exp_log_of_neg

/- warning: real.le_exp_log -> Real.le_exp_log is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe x (Real.exp (Real.log x))
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal x (Real.exp (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.le_exp_log Real.le_exp_logₓ'. -/
theorem le_exp_log (x : ℝ) : x ≤ exp (log x) :=
  by
  by_cases h_zero : x = 0
  · rw [h_zero, log, dif_pos rfl, exp_zero]
    exact zero_le_one
  · rw [exp_log_eq_abs h_zero]
    exact le_abs_self _
#align real.le_exp_log Real.le_exp_log

#print Real.log_exp /-
@[simp]
theorem log_exp (x : ℝ) : log (exp x) = x :=
  exp_injective <| exp_log (exp_pos x)
#align real.log_exp Real.log_exp
-/

/- warning: real.surj_on_log -> Real.surjOn_log is a dubious translation:
lean 3 declaration is
  Set.SurjOn.{0, 0} Real Real Real.log (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.univ.{0} Real)
but is expected to have type
  Set.SurjOn.{0, 0} Real Real Real.log (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.univ.{0} Real)
Case conversion may be inaccurate. Consider using '#align real.surj_on_log Real.surjOn_logₓ'. -/
theorem surjOn_log : SurjOn log (Ioi 0) univ := fun x _ => ⟨exp x, exp_pos x, log_exp x⟩
#align real.surj_on_log Real.surjOn_log

#print Real.log_surjective /-
theorem log_surjective : Surjective log := fun x => ⟨exp x, log_exp x⟩
#align real.log_surjective Real.log_surjective
-/

#print Real.range_log /-
@[simp]
theorem range_log : range log = univ :=
  log_surjective.range_eq
#align real.range_log Real.range_log
-/

/- warning: real.log_zero -> Real.log_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.log (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.log (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.log_zero Real.log_zeroₓ'. -/
@[simp]
theorem log_zero : log 0 = 0 :=
  dif_pos rfl
#align real.log_zero Real.log_zero

/- warning: real.log_one -> Real.log_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.log (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.log (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.log_one Real.log_oneₓ'. -/
@[simp]
theorem log_one : log 1 = 0 :=
  exp_injective <| by rw [exp_log zero_lt_one, exp_zero]
#align real.log_one Real.log_one

/- warning: real.log_abs -> Real.log_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.log (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)) (Real.log x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.log (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)) (Real.log x)
Case conversion may be inaccurate. Consider using '#align real.log_abs Real.log_absₓ'. -/
@[simp]
theorem log_abs (x : ℝ) : log (|x|) = log x :=
  by
  by_cases h : x = 0
  · simp [h]
  · rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs]
#align real.log_abs Real.log_abs

/- warning: real.log_neg_eq_log -> Real.log_neg_eq_log is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.log (Neg.neg.{0} Real Real.hasNeg x)) (Real.log x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.log (Neg.neg.{0} Real Real.instNegReal x)) (Real.log x)
Case conversion may be inaccurate. Consider using '#align real.log_neg_eq_log Real.log_neg_eq_logₓ'. -/
@[simp]
theorem log_neg_eq_log (x : ℝ) : log (-x) = log x := by rw [← log_abs x, ← log_abs (-x), abs_neg]
#align real.log_neg_eq_log Real.log_neg_eq_log

/- warning: real.sinh_log -> Real.sinh_log is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.sinh (Real.log x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x (Inv.inv.{0} Real Real.hasInv x)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.sinh (Real.log x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (Inv.inv.{0} Real Real.instInvReal x)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.sinh_log Real.sinh_logₓ'. -/
theorem sinh_log {x : ℝ} (hx : 0 < x) : sinh (log x) = (x - x⁻¹) / 2 := by
  rw [sinh_eq, exp_neg, exp_log hx]
#align real.sinh_log Real.sinh_log

/- warning: real.cosh_log -> Real.cosh_log is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.cosh (Real.log x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x (Inv.inv.{0} Real Real.hasInv x)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.cosh (Real.log x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x (Inv.inv.{0} Real Real.instInvReal x)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.cosh_log Real.cosh_logₓ'. -/
theorem cosh_log {x : ℝ} (hx : 0 < x) : cosh (log x) = (x + x⁻¹) / 2 := by
  rw [cosh_eq, exp_neg, exp_log hx]
#align real.cosh_log Real.cosh_log

/- warning: real.surj_on_log' -> Real.surjOn_log' is a dubious translation:
lean 3 declaration is
  Set.SurjOn.{0, 0} Real Real Real.log (Set.Iio.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Set.univ.{0} Real)
but is expected to have type
  Set.SurjOn.{0, 0} Real Real Real.log (Set.Iio.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Set.univ.{0} Real)
Case conversion may be inaccurate. Consider using '#align real.surj_on_log' Real.surjOn_log'ₓ'. -/
theorem surjOn_log' : SurjOn log (Iio 0) univ := fun x _ =>
  ⟨-exp x, neg_lt_zero.2 <| exp_pos x, by rw [log_neg_eq_log, log_exp]⟩
#align real.surj_on_log' Real.surjOn_log'

/- warning: real.log_mul -> Real.log_mul is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.log (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.log x) (Real.log y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.log (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.log x) (Real.log y)))
Case conversion may be inaccurate. Consider using '#align real.log_mul Real.log_mulₓ'. -/
theorem log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]
#align real.log_mul Real.log_mul

/- warning: real.log_div -> Real.log_div is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (Real.log (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.log x) (Real.log y)))
but is expected to have type
  forall {x : Real} {y : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Ne.{1} Real y (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (Real.log (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.log x) (Real.log y)))
Case conversion may be inaccurate. Consider using '#align real.log_div Real.log_divₓ'. -/
theorem log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y :=
  exp_injective <| by
    rw [exp_log_eq_abs (div_ne_zero hx hy), exp_sub, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_div]
#align real.log_div Real.log_div

/- warning: real.log_inv -> Real.log_inv is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real (Real.log (Inv.inv.{0} Real Real.hasInv x)) (Neg.neg.{0} Real Real.hasNeg (Real.log x))
but is expected to have type
  forall (x : Real), Eq.{1} Real (Real.log (Inv.inv.{0} Real Real.instInvReal x)) (Neg.neg.{0} Real Real.instNegReal (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.log_inv Real.log_invₓ'. -/
@[simp]
theorem log_inv (x : ℝ) : log x⁻¹ = -log x :=
  by
  by_cases hx : x = 0; · simp [hx]
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
#align real.log_inv Real.log_inv

/- warning: real.log_le_log -> Real.log_le_log is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe (Real.log x) (Real.log y)) (LE.le.{0} Real Real.hasLe x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.log x) (Real.log y)) (LE.le.{0} Real Real.instLEReal x y))
Case conversion may be inaccurate. Consider using '#align real.log_le_log Real.log_le_logₓ'. -/
theorem log_le_log (h : 0 < x) (h₁ : 0 < y) : log x ≤ log y ↔ x ≤ y := by
  rw [← exp_le_exp, exp_log h, exp_log h₁]
#align real.log_le_log Real.log_le_log

/- warning: real.log_lt_log -> Real.log_lt_log is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.log x) (Real.log y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.log x) (Real.log y))
Case conversion may be inaccurate. Consider using '#align real.log_lt_log Real.log_lt_logₓ'. -/
theorem log_lt_log (hx : 0 < x) : x < y → log x < log y :=
  by
  intro h
  rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)]
#align real.log_lt_log Real.log_lt_log

/- warning: real.log_lt_log_iff -> Real.log_lt_log_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.log x) (Real.log y)) (LT.lt.{0} Real Real.hasLt x y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.log x) (Real.log y)) (LT.lt.{0} Real Real.instLTReal x y))
Case conversion may be inaccurate. Consider using '#align real.log_lt_log_iff Real.log_lt_log_iffₓ'. -/
theorem log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y := by
  rw [← exp_lt_exp, exp_log hx, exp_log hy]
#align real.log_lt_log_iff Real.log_lt_log_iff

/- warning: real.log_le_iff_le_exp -> Real.log_le_iff_le_exp is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.log x) y) (LE.le.{0} Real Real.hasLe x (Real.exp y)))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.log x) y) (LE.le.{0} Real Real.instLEReal x (Real.exp y)))
Case conversion may be inaccurate. Consider using '#align real.log_le_iff_le_exp Real.log_le_iff_le_expₓ'. -/
theorem log_le_iff_le_exp (hx : 0 < x) : log x ≤ y ↔ x ≤ exp y := by rw [← exp_le_exp, exp_log hx]
#align real.log_le_iff_le_exp Real.log_le_iff_le_exp

/- warning: real.log_lt_iff_lt_exp -> Real.log_lt_iff_lt_exp is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.log x) y) (LT.lt.{0} Real Real.hasLt x (Real.exp y)))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.log x) y) (LT.lt.{0} Real Real.instLTReal x (Real.exp y)))
Case conversion may be inaccurate. Consider using '#align real.log_lt_iff_lt_exp Real.log_lt_iff_lt_expₓ'. -/
theorem log_lt_iff_lt_exp (hx : 0 < x) : log x < y ↔ x < exp y := by rw [← exp_lt_exp, exp_log hx]
#align real.log_lt_iff_lt_exp Real.log_lt_iff_lt_exp

/- warning: real.le_log_iff_exp_le -> Real.le_log_iff_exp_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LE.le.{0} Real Real.hasLe x (Real.log y)) (LE.le.{0} Real Real.hasLe (Real.exp x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LE.le.{0} Real Real.instLEReal x (Real.log y)) (LE.le.{0} Real Real.instLEReal (Real.exp x) y))
Case conversion may be inaccurate. Consider using '#align real.le_log_iff_exp_le Real.le_log_iff_exp_leₓ'. -/
theorem le_log_iff_exp_le (hy : 0 < y) : x ≤ log y ↔ exp x ≤ y := by rw [← exp_le_exp, exp_log hy]
#align real.le_log_iff_exp_le Real.le_log_iff_exp_le

/- warning: real.lt_log_iff_exp_lt -> Real.lt_log_iff_exp_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Iff (LT.lt.{0} Real Real.hasLt x (Real.log y)) (LT.lt.{0} Real Real.hasLt (Real.exp x) y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Iff (LT.lt.{0} Real Real.instLTReal x (Real.log y)) (LT.lt.{0} Real Real.instLTReal (Real.exp x) y))
Case conversion may be inaccurate. Consider using '#align real.lt_log_iff_exp_lt Real.lt_log_iff_exp_ltₓ'. -/
theorem lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp x < y := by rw [← exp_lt_exp, exp_log hy]
#align real.lt_log_iff_exp_lt Real.lt_log_iff_exp_lt

/- warning: real.log_pos_iff -> Real.log_pos_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.log x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.log x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.log_pos_iff Real.log_pos_iffₓ'. -/
theorem log_pos_iff (hx : 0 < x) : 0 < log x ↔ 1 < x :=
  by
  rw [← log_one]
  exact log_lt_log_iff zero_lt_one hx
#align real.log_pos_iff Real.log_pos_iff

/- warning: real.log_pos -> Real.log_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.log x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.log_pos Real.log_posₓ'. -/
theorem log_pos (hx : 1 < x) : 0 < log x :=
  (log_pos_iff (lt_trans zero_lt_one hx)).2 hx
#align real.log_pos Real.log_pos

/- warning: real.log_neg_iff -> Real.log_neg_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LT.lt.{0} Real Real.hasLt (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LT.lt.{0} Real Real.instLTReal (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.log_neg_iff Real.log_neg_iffₓ'. -/
theorem log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 :=
  by
  rw [← log_one]
  exact log_lt_log_iff h zero_lt_one
#align real.log_neg_iff Real.log_neg_iff

/- warning: real.log_neg -> Real.log_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.log_neg Real.log_negₓ'. -/
theorem log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 :=
  (log_neg_iff h0).2 h1
#align real.log_neg Real.log_neg

/- warning: real.log_nonneg_iff -> Real.log_nonneg_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.log x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.log x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.log_nonneg_iff Real.log_nonneg_iffₓ'. -/
theorem log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x := by rw [← not_lt, log_neg_iff hx, not_lt]
#align real.log_nonneg_iff Real.log_nonneg_iff

/- warning: real.log_nonneg -> Real.log_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.log x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.log_nonneg Real.log_nonnegₓ'. -/
theorem log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
  (log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx
#align real.log_nonneg Real.log_nonneg

/- warning: real.log_nonpos_iff -> Real.log_nonpos_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.log_nonpos_iff Real.log_nonpos_iffₓ'. -/
theorem log_nonpos_iff (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 := by rw [← not_lt, log_pos_iff hx, not_lt]
#align real.log_nonpos_iff Real.log_nonpos_iff

/- warning: real.log_nonpos_iff' -> Real.log_nonpos_iff' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Iff (LE.le.{0} Real Real.hasLe (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Iff (LE.le.{0} Real Real.instLEReal (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.log_nonpos_iff' Real.log_nonpos_iff'ₓ'. -/
theorem log_nonpos_iff' (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 :=
  by
  rcases hx.eq_or_lt with (rfl | hx)
  · simp [le_refl, zero_le_one]
  exact log_nonpos_iff hx
#align real.log_nonpos_iff' Real.log_nonpos_iff'

/- warning: real.log_nonpos -> Real.log_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LE.le.{0} Real Real.hasLe (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LE.le.{0} Real Real.instLEReal (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.log_nonpos Real.log_nonposₓ'. -/
theorem log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
  (log_nonpos_iff' hx).2 h'x
#align real.log_nonpos Real.log_nonpos

/- warning: real.strict_mono_on_log -> Real.strictMonoOn_log is a dubious translation:
lean 3 declaration is
  StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder Real.log (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.log (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_log Real.strictMonoOn_logₓ'. -/
theorem strictMonoOn_log : StrictMonoOn log (Set.Ioi 0) := fun x hx y hy hxy => log_lt_log hx hxy
#align real.strict_mono_on_log Real.strictMonoOn_log

/- warning: real.strict_anti_on_log -> Real.strictAntiOn_log is a dubious translation:
lean 3 declaration is
  StrictAntiOn.{0, 0} Real Real Real.preorder Real.preorder Real.log (Set.Iio.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  StrictAntiOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.log (Set.Iio.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.strict_anti_on_log Real.strictAntiOn_logₓ'. -/
theorem strictAntiOn_log : StrictAntiOn log (Set.Iio 0) :=
  by
  rintro x (hx : x < 0) y (hy : y < 0) hxy
  rw [← log_abs y, ← log_abs x]
  refine' log_lt_log (abs_pos.2 hy.ne) _
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
#align real.strict_anti_on_log Real.strictAntiOn_log

/- warning: real.log_inj_on_pos -> Real.log_injOn_pos is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.log (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.log (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.log_inj_on_pos Real.log_injOn_posₓ'. -/
theorem log_injOn_pos : Set.InjOn log (Set.Ioi 0) :=
  strictMonoOn_log.InjOn
#align real.log_inj_on_pos Real.log_injOn_pos

theorem log_lt_sub_one_of_pos (hx1 : 0 < x) (hx2 : x ≠ 1) : log x < x - 1 :=
  by
  have h : log x ≠ 0 := by
    rw [← log_one, log_inj_on_pos.ne_iff hx1 zero_lt_one]
    exact hx2
  linarith [add_one_lt_exp_of_nonzero h, exp_log hx1]
#align real.log_lt_sub_one_of_pos Real.log_lt_sub_one_of_pos

/- warning: real.eq_one_of_pos_of_log_eq_zero -> Real.eq_one_of_pos_of_log_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.eq_one_of_pos_of_log_eq_zero Real.eq_one_of_pos_of_log_eq_zeroₓ'. -/
theorem eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
  log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)
#align real.eq_one_of_pos_of_log_eq_zero Real.eq_one_of_pos_of_log_eq_zero

/- warning: real.log_ne_zero_of_pos_of_ne_one -> Real.log_ne_zero_of_pos_of_ne_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Ne.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Ne.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.log_ne_zero_of_pos_of_ne_one Real.log_ne_zero_of_pos_of_ne_oneₓ'. -/
theorem log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
  mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx
#align real.log_ne_zero_of_pos_of_ne_one Real.log_ne_zero_of_pos_of_ne_one

/- warning: real.log_eq_zero -> Real.log_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real x (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.log x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real x (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))))
Case conversion may be inaccurate. Consider using '#align real.log_eq_zero Real.log_eq_zeroₓ'. -/
@[simp]
theorem log_eq_zero {x : ℝ} : log x = 0 ↔ x = 0 ∨ x = 1 ∨ x = -1 :=
  by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with (x_lt_zero | rfl | x_gt_zero)
    · refine' Or.inr (Or.inr (neg_eq_iff_eq_neg.mp _))
      rw [← log_neg_eq_log x] at h
      exact eq_one_of_pos_of_log_eq_zero (neg_pos.mpr x_lt_zero) h
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (eq_one_of_pos_of_log_eq_zero x_gt_zero h))
  · rintro (rfl | rfl | rfl) <;> simp only [log_one, log_zero, log_neg_eq_log]
#align real.log_eq_zero Real.log_eq_zero

/- warning: real.log_pow -> Real.log_pow is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Real.log x))
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast n) (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.log_pow Real.log_powₓ'. -/
@[simp]
theorem log_pow (x : ℝ) (n : ℕ) : log (x ^ n) = n * log x :=
  by
  induction' n with n ih
  · simp
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  rw [pow_succ', log_mul (pow_ne_zero _ hx) hx, ih, Nat.cast_succ, add_mul, one_mul]
#align real.log_pow Real.log_pow

/- warning: real.log_zpow -> Real.log_zpow is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Int), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n) (Real.log x))
but is expected to have type
  forall (x : Real) (n : Int), Eq.{1} Real (Real.log (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) x n)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast n) (Real.log x))
Case conversion may be inaccurate. Consider using '#align real.log_zpow Real.log_zpowₓ'. -/
@[simp]
theorem log_zpow (x : ℝ) (n : ℤ) : log (x ^ n) = n * log x :=
  by
  induction n
  · rw [Int.ofNat_eq_coe, zpow_ofNat, log_pow, Int.cast_ofNat]
  rw [zpow_negSucc, log_inv, log_pow, Int.cast_negSucc, Nat.cast_add_one, neg_mul_eq_neg_mul]
#align real.log_zpow Real.log_zpow

/- warning: real.log_sqrt -> Real.log_sqrt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} Real (Real.log (Real.sqrt x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} Real (Real.log (Real.sqrt x)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.log_sqrt Real.log_sqrtₓ'. -/
theorem log_sqrt {x : ℝ} (hx : 0 ≤ x) : log (sqrt x) = log x / 2 :=
  by
  rw [eq_div_iff, mul_comm, ← Nat.cast_two, ← log_pow, sq_sqrt hx]
  exact two_ne_zero
#align real.log_sqrt Real.log_sqrt

/- warning: real.log_le_sub_one_of_pos -> Real.log_le_sub_one_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe (Real.log x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal (Real.log x) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.log_le_sub_one_of_pos Real.log_le_sub_one_of_posₓ'. -/
theorem log_le_sub_one_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 :=
  by
  rw [le_sub_iff_add_le]
  convert add_one_le_exp (log x)
  rw [exp_log hx]
#align real.log_le_sub_one_of_pos Real.log_le_sub_one_of_pos

/- warning: real.abs_log_mul_self_lt -> Real.abs_log_mul_self_lt is a dubious translation:
lean 3 declaration is
  forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) x)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) x)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.abs_log_mul_self_lt Real.abs_log_mul_self_ltₓ'. -/
/-- Bound for `|log x * x|` in the interval `(0, 1]`. -/
theorem abs_log_mul_self_lt (x : ℝ) (h1 : 0 < x) (h2 : x ≤ 1) : |log x * x| < 1 :=
  by
  have : 0 < 1 / x := by simpa only [one_div, inv_pos] using h1
  replace := log_le_sub_one_of_pos this
  replace : log (1 / x) < 1 / x := by linarith
  rw [log_div one_ne_zero h1.ne', log_one, zero_sub, lt_div_iff h1] at this
  have aux : 0 ≤ -log x * x := by
    refine' mul_nonneg _ h1.le
    rw [← log_inv]
    apply log_nonneg
    rw [← le_inv h1 zero_lt_one, inv_one]
    exact h2
  rw [← abs_of_nonneg aux, neg_mul, abs_neg] at this
  exact this
#align real.abs_log_mul_self_lt Real.abs_log_mul_self_lt

#print Real.tendsto_log_atTop /-
/-- The real logarithm function tends to `+∞` at `+∞`. -/
theorem tendsto_log_atTop : Tendsto log atTop atTop :=
  tendsto_comp_exp_atTop.1 <| by simpa only [log_exp] using tendsto_id
#align real.tendsto_log_at_top Real.tendsto_log_atTop
-/

/- warning: real.tendsto_log_nhds_within_zero -> Real.tendsto_log_nhdsWithin_zero is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.log (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HasCompl.compl.{0} (Set.{0} Real) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Real) (Set.booleanAlgebra.{0} Real)) (Singleton.singleton.{0, 0} Real (Set.{0} Real) (Set.hasSingleton.{0} Real) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))) (Filter.atBot.{0} Real Real.preorder)
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.log (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HasCompl.compl.{0} (Set.{0} Real) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Real) (Set.instBooleanAlgebraSet.{0} Real)) (Singleton.singleton.{0, 0} Real (Set.{0} Real) (Set.instSingletonSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))) (Filter.atBot.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.tendsto_log_nhds_within_zero Real.tendsto_log_nhdsWithin_zeroₓ'. -/
theorem tendsto_log_nhdsWithin_zero : Tendsto log (𝓝[≠] 0) atBot :=
  by
  rw [← show _ = log from funext log_abs]
  refine' tendsto.comp _ tendsto_abs_nhdsWithin_zero
  simpa [← tendsto_comp_exp_at_bot] using tendsto_id
#align real.tendsto_log_nhds_within_zero Real.tendsto_log_nhdsWithin_zero

/- warning: real.continuous_on_log -> Real.continuousOn_log is a dubious translation:
lean 3 declaration is
  ContinuousOn.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log (HasCompl.compl.{0} (Set.{0} Real) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Real) (Set.booleanAlgebra.{0} Real)) (Singleton.singleton.{0, 0} Real (Set.{0} Real) (Set.hasSingleton.{0} Real) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  ContinuousOn.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log (HasCompl.compl.{0} (Set.{0} Real) (BooleanAlgebra.toHasCompl.{0} (Set.{0} Real) (Set.instBooleanAlgebraSet.{0} Real)) (Singleton.singleton.{0, 0} Real (Set.{0} Real) (Set.instSingletonSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.continuous_on_log Real.continuousOn_logₓ'. -/
theorem continuousOn_log : ContinuousOn log ({0}ᶜ) :=
  by
  rw [continuousOn_iff_continuous_restrict, restrict]
  conv in log _ => rw [log_of_ne_zero (show (x : ℝ) ≠ 0 from x.2)]
  exact exp_order_iso.symm.continuous.comp (continuous_subtype_coe.norm.subtype_mk _)
#align real.continuous_on_log Real.continuousOn_log

/- warning: real.continuous_log -> Real.continuous_log is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (Subtype.topologicalSpace.{0} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) => Real.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (HasLiftT.mk.{1, 1} (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (CoeTCₓ.coe.{1, 1} (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeBase.{1, 1} (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) Real (coeSubtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))))) x))
but is expected to have type
  Continuous.{0, 0} (Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) Real (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Subtype.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) => Real.log (Subtype.val.{1} Real (fun (x : Real) => Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) x))
Case conversion may be inaccurate. Consider using '#align real.continuous_log Real.continuous_logₓ'. -/
@[continuity]
theorem continuous_log : Continuous fun x : { x : ℝ // x ≠ 0 } => log x :=
  continuousOn_iff_continuous_restrict.1 <| continuousOn_log.mono fun x hx => hx
#align real.continuous_log Real.continuous_log

/- warning: real.continuous_log' -> Real.continuous_log' is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) Real (Subtype.topologicalSpace.{0} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) => Real.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) Real (HasLiftT.mk.{1, 1} (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) Real (CoeTCₓ.coe.{1, 1} (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) Real (coeBase.{1, 1} (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) Real (coeSubtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x))))) x))
but is expected to have type
  Continuous.{0, 0} (Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)) Real (instTopologicalSpaceSubtype.{0} Real (fun (x : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : Subtype.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)) => Real.log (Subtype.val.{1} Real (fun (x : Real) => LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) x))
Case conversion may be inaccurate. Consider using '#align real.continuous_log' Real.continuous_log'ₓ'. -/
@[continuity]
theorem continuous_log' : Continuous fun x : { x : ℝ // 0 < x } => log x :=
  continuousOn_iff_continuous_restrict.1 <| continuousOn_log.mono fun x hx => ne_of_gt hx
#align real.continuous_log' Real.continuous_log'

/- warning: real.continuous_at_log -> Real.continuousAt_log is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log x)
but is expected to have type
  forall {x : Real}, (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log x)
Case conversion may be inaccurate. Consider using '#align real.continuous_at_log Real.continuousAt_logₓ'. -/
theorem continuousAt_log (hx : x ≠ 0) : ContinuousAt log x :=
  (continuousOn_log x hx).ContinuousAt <| IsOpen.mem_nhds isOpen_compl_singleton hx
#align real.continuous_at_log Real.continuousAt_log

/- warning: real.continuous_at_log_iff -> Real.continuousAt_log_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log x) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (ContinuousAt.{0, 0} Real Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Real.log x) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.continuous_at_log_iff Real.continuousAt_log_iffₓ'. -/
@[simp]
theorem continuousAt_log_iff : ContinuousAt log x ↔ x ≠ 0 :=
  by
  refine' ⟨_, continuous_at_log⟩
  rintro h rfl
  exact
    not_tendsto_nhds_of_tendsto_atBot tendsto_log_nhds_within_zero _
      (h.tendsto.mono_left inf_le_left)
#align real.continuous_at_log_iff Real.continuousAt_log_iff

open BigOperators

/- warning: real.log_prod -> Real.log_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> Real), (forall (x : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (Eq.{1} Real (Real.log (Finset.prod.{0, u1} Real α Real.commMonoid s (fun (i : α) => f i))) (Finset.sum.{0, u1} Real α Real.addCommMonoid s (fun (i : α) => Real.log (f i))))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> Real), (forall (x : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (Eq.{1} Real (Real.log (Finset.prod.{0, u1} Real α Real.instCommMonoidReal s (fun (i : α) => f i))) (Finset.sum.{0, u1} Real α Real.instAddCommMonoidReal s (fun (i : α) => Real.log (f i))))
Case conversion may be inaccurate. Consider using '#align real.log_prod Real.log_prodₓ'. -/
theorem log_prod {α : Type _} (s : Finset α) (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    log (∏ i in s, f i) = ∑ i in s, log (f i) :=
  by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp
  · rw [Finset.forall_mem_cons] at hf
    simp [ih hf.2, log_mul hf.1 (Finset.prod_ne_zero_iff.2 hf.2)]
#align real.log_prod Real.log_prod

/- warning: real.log_nat_eq_sum_factorization -> Real.log_nat_eq_sum_factorization is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Real (Real.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) (Finsupp.sum.{0, 0, 0} Nat Nat Real Nat.hasZero Real.addCommMonoid (Nat.factorization n) (fun (p : Nat) (t : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) t) (Real.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) p))))
but is expected to have type
  forall (n : Nat), Eq.{1} Real (Real.log (Nat.cast.{0} Real Real.natCast n)) (Finsupp.sum.{0, 0, 0} Nat Nat Real (LinearOrderedCommMonoidWithZero.toZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) Real.instAddCommMonoidReal (Nat.factorization n) (fun (p : Nat) (t : Nat) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Nat.cast.{0} Real Real.natCast t) (Real.log (Nat.cast.{0} Real Real.natCast p))))
Case conversion may be inaccurate. Consider using '#align real.log_nat_eq_sum_factorization Real.log_nat_eq_sum_factorizationₓ'. -/
theorem log_nat_eq_sum_factorization (n : ℕ) : log n = n.factorization.Sum fun p t => t * log p :=
  by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  nth_rw 1 [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.cast_prod, log_prod _ _ fun p hp => _, Finsupp.sum]
  · simp_rw [Nat.cast_pow, log_pow]
  · norm_cast
    exact pow_ne_zero _ (Nat.prime_of_mem_factorization hp).NeZero
#align real.log_nat_eq_sum_factorization Real.log_nat_eq_sum_factorization

/- warning: real.tendsto_pow_log_div_mul_add_at_top -> Real.tendsto_pow_log_div_mul_add_atTop is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real) (n : Nat), (Ne.{1} Real a (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.log x) n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) a x) b)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall (a : Real) (b : Real) (n : Nat), (Ne.{1} Real a (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.log x) n) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) a x) b)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_pow_log_div_mul_add_at_top Real.tendsto_pow_log_div_mul_add_atTopₓ'. -/
theorem tendsto_pow_log_div_mul_add_atTop (a b : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x => log x ^ n / (a * x + b)) atTop (𝓝 0) :=
  ((tendsto_div_pow_mul_exp_add_atTop a b n ha.symm).comp tendsto_log_atTop).congr'
    (by filter_upwards [eventually_gt_at_top (0 : ℝ)]with x hx using by simp [exp_log hx])
#align real.tendsto_pow_log_div_mul_add_at_top Real.tendsto_pow_log_div_mul_add_atTop

/- warning: real.is_o_pow_log_id_at_top -> Real.isLittleO_pow_log_id_atTop is a dubious translation:
lean 3 declaration is
  forall {n : Nat}, Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.log x) n) (id.{1} Real)
but is expected to have type
  forall {n : Nat}, Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) (fun (x : Real) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.log x) n) (id.{1} Real)
Case conversion may be inaccurate. Consider using '#align real.is_o_pow_log_id_at_top Real.isLittleO_pow_log_id_atTopₓ'. -/
theorem isLittleO_pow_log_id_atTop {n : ℕ} : (fun x => log x ^ n) =o[atTop] id :=
  by
  rw [Asymptotics.isLittleO_iff_tendsto']
  · simpa using tendsto_pow_log_div_mul_add_at_top 1 0 n one_ne_zero
  filter_upwards [eventually_ne_at_top (0 : ℝ)]with x h₁ h₂ using(h₁ h₂).elim
#align real.is_o_pow_log_id_at_top Real.isLittleO_pow_log_id_atTop

/- warning: real.is_o_log_id_at_top -> Real.isLittleO_log_id_atTop is a dubious translation:
lean 3 declaration is
  Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.hasNorm Real.hasNorm (Filter.atTop.{0} Real Real.preorder) Real.log (id.{1} Real)
but is expected to have type
  Asymptotics.IsLittleO.{0, 0, 0} Real Real Real Real.norm Real.norm (Filter.atTop.{0} Real Real.instPreorderReal) Real.log (id.{1} Real)
Case conversion may be inaccurate. Consider using '#align real.is_o_log_id_at_top Real.isLittleO_log_id_atTopₓ'. -/
theorem isLittleO_log_id_atTop : log =o[atTop] id :=
  isLittleO_pow_log_id_atTop.congr_left fun x => pow_one _
#align real.is_o_log_id_at_top Real.isLittleO_log_id_atTop

end Real

section Continuity

open Real

variable {α : Type _}

/- warning: filter.tendsto.log -> Filter.Tendsto.log is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> Real} {l : Filter.{u1} α} {x : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Real.log (f x)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.log x)))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> Real} {l : Filter.{u1} α} {x : Real}, (Filter.Tendsto.{u1, 0} α Real f l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) x)) -> (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Filter.Tendsto.{u1, 0} α Real (fun (x : α) => Real.log (f x)) l (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Real.log x)))
Case conversion may be inaccurate. Consider using '#align filter.tendsto.log Filter.Tendsto.logₓ'. -/
theorem Filter.Tendsto.log {f : α → ℝ} {l : Filter α} {x : ℝ} (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun x => log (f x)) l (𝓝 (log x)) :=
  (continuousAt_log hx).Tendsto.comp h
#align filter.tendsto.log Filter.Tendsto.log

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

/- warning: continuous.log -> Continuous.log is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (x : α), Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real}, (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f) -> (forall (x : α), Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Continuous.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)))
Case conversion may be inaccurate. Consider using '#align continuous.log Continuous.logₓ'. -/
theorem Continuous.log (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) : Continuous fun x => log (f x) :=
  continuousOn_log.comp_continuous hf h₀
#align continuous.log Continuous.log

/- warning: continuous_at.log -> ContinuousAt.log is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {a : α}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f a) -> (Ne.{1} Real (f a) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {a : α}, (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f a) -> (Ne.{1} Real (f a) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) a)
Case conversion may be inaccurate. Consider using '#align continuous_at.log ContinuousAt.logₓ'. -/
theorem ContinuousAt.log (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x => log (f x)) a :=
  hf.log h₀
#align continuous_at.log ContinuousAt.log

/- warning: continuous_within_at.log -> ContinuousWithinAt.log is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s a) -> (Ne.{1} Real (f a) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) s a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α} {a : α}, (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s a) -> (Ne.{1} Real (f a) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (ContinuousWithinAt.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) s a)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.log ContinuousWithinAt.logₓ'. -/
theorem ContinuousWithinAt.log (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x => log (f x)) s a :=
  hf.log h₀
#align continuous_within_at.log ContinuousWithinAt.log

/- warning: continuous_on.log -> ContinuousOn.log is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {f : α -> Real} {s : Set.{u1} α}, (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) f s) -> (forall (x : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) x s) -> (Ne.{1} Real (f x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (ContinuousOn.{u1, 0} α Real _inst_1 (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (x : α) => Real.log (f x)) s)
Case conversion may be inaccurate. Consider using '#align continuous_on.log ContinuousOn.logₓ'. -/
theorem ContinuousOn.log (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => log (f x)) s := fun x hx => (hf x hx).log (h₀ x hx)
#align continuous_on.log ContinuousOn.log

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

/- warning: real.tendsto_log_comp_add_sub_log -> Real.tendsto_log_comp_add_sub_log is a dubious translation:
lean 3 declaration is
  forall (y : Real), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.log (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y)) (Real.log x)) (Filter.atTop.{0} Real Real.preorder) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (y : Real), Filter.Tendsto.{0, 0} Real Real (fun (x : Real) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.log (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y)) (Real.log x)) (Filter.atTop.{0} Real Real.instPreorderReal) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_log_comp_add_sub_log Real.tendsto_log_comp_add_sub_logₓ'. -/
theorem tendsto_log_comp_add_sub_log (y : ℝ) :
    Tendsto (fun x : ℝ => log (x + y) - log x) atTop (𝓝 0) :=
  by
  refine' tendsto.congr' (_ : ∀ᶠ x : ℝ in at_top, log (1 + y / x) = _) _
  · refine'
      eventually.mp ((eventually_ne_at_top 0).And (eventually_gt_at_top (-y)))
        (eventually_of_forall fun x hx => _)
    rw [← log_div _ hx.1]
    · congr 1
      field_simp [hx.1]
    · linarith [hx.2]
  · suffices tendsto (fun x : ℝ => log (1 + y / x)) at_top (𝓝 (log (1 + 0))) by simpa
    refine' tendsto.log _ (by simp)
    exact tendsto_const_nhds.add (tendsto_const_nhds.div_at_top tendsto_id)
#align real.tendsto_log_comp_add_sub_log Real.tendsto_log_comp_add_sub_log

/- warning: real.tendsto_log_nat_add_one_sub_log -> Real.tendsto_log_nat_add_one_sub_log is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Nat Real (fun (k : Nat) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.log (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) k) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Real.log ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) k))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring)))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  Filter.Tendsto.{0, 0} Nat Real (fun (k : Nat) => HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.log (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Nat.cast.{0} Real Real.natCast k) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Real.log (Nat.cast.{0} Real Real.natCast k))) (Filter.atTop.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_log_nat_add_one_sub_log Real.tendsto_log_nat_add_one_sub_logₓ'. -/
theorem tendsto_log_nat_add_one_sub_log : Tendsto (fun k : ℕ => log (k + 1) - log k) atTop (𝓝 0) :=
  (tendsto_log_comp_add_sub_log 1).comp tendsto_nat_cast_atTop_atTop
#align real.tendsto_log_nat_add_one_sub_log Real.tendsto_log_nat_add_one_sub_log

end Real

end TendstoCompAddSub

