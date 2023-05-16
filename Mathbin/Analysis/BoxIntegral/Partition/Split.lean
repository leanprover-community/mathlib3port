/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.box_integral.partition.split
! leanprover-community/mathlib commit 9d2f0748e6c50d7a2657c564b1ff2c695b39148d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.BoxIntegral.Partition.Basic

/-!
# Split a box along one or more hyperplanes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : box_integral.box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `box_integral.box`.

We introduce the following definitions.

* `box_integral.box.split_lower I i a` and `box_integral.box.split_upper I i a` are these boxes (as
  `with_bot (box_integral.box ι)`);
* `box_integral.prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
   box `I` if one of these boxes is empty);
* `box_integral.prepartition.split_many I s`, where `s : finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `box_integral.prepartition.exists_Union_eq_diff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.Union`. One of these prepartitions
is available as `box_integral.prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/


noncomputable section

open Classical BigOperators Filter

open Function Set Filter

namespace BoxIntegral

variable {ι M : Type _} {n : ℕ}

namespace Box

variable {I : Box ι} {i : ι} {x : ℝ} {y : ι → ℝ}

#print BoxIntegral.Box.splitLower /-
/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_lower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def splitLower (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' I.lower (update I.upper i (min x (I.upper i)))
#align box_integral.box.split_lower BoxIntegral.Box.splitLower
-/

/- warning: box_integral.box.coe_split_lower -> BoxIntegral.Box.coe_splitLower is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.withBotCoe.{u1} ι))) (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.hasLe (y i) x)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.withBotToSet.{u1} ι (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.instLEReal (y i) x)))
Case conversion may be inaccurate. Consider using '#align box_integral.box.coe_split_lower BoxIntegral.Box.coe_splitLowerₓ'. -/
@[simp]
theorem coe_splitLower : (splitLower I i x : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } :=
  by
  rw [split_lower, coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_set_of_eq, forall_and, ← Pi.le_def,
    le_update_iff, le_min_iff, and_assoc', and_forall_ne i, mem_def]
  rw [and_comm' (y i ≤ x), Pi.le_def]
#align box_integral.box.coe_split_lower BoxIntegral.Box.coe_splitLower

/- warning: box_integral.box.split_lower_le -> BoxIntegral.Box.splitLower_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, LE.le.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) (BoxIntegral.Box.splitLower.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, LE.le.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toLE.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (BoxIntegral.Box.splitLower.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) I)
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_lower_le BoxIntegral.Box.splitLower_leₓ'. -/
theorem splitLower_le : I.splitLower i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp
#align box_integral.box.split_lower_le BoxIntegral.Box.splitLower_le

/- warning: box_integral.box.split_lower_eq_bot -> BoxIntegral.Box.splitLower_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) (Bot.bot.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasBot.{u1} (BoxIntegral.Box.{u1} ι)))) (LE.le.{0} Real Real.hasLe x (BoxIntegral.Box.lower.{u1} ι I i))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) (Bot.bot.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.bot.{u1} (BoxIntegral.Box.{u1} ι)))) (LE.le.{0} Real Real.instLEReal x (BoxIntegral.Box.lower.{u1} ι I i))
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_lower_eq_bot BoxIntegral.Box.splitLower_eq_botₓ'. -/
@[simp]
theorem splitLower_eq_bot {i x} : I.splitLower i x = ⊥ ↔ x ≤ I.lower i :=
  by
  rw [split_lower, mk'_eq_bot, exists_update_iff I.upper fun j y => y ≤ I.lower j]
  simp [(I.lower_lt_upper _).not_le]
#align box_integral.box.split_lower_eq_bot BoxIntegral.Box.splitLower_eq_bot

/- warning: box_integral.box.split_lower_eq_self -> BoxIntegral.Box.splitLower_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I)) (LE.le.{0} Real Real.hasLe (BoxIntegral.Box.upper.{u1} ι I i) x)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) I)) (LE.le.{0} Real Real.instLEReal (BoxIntegral.Box.upper.{u1} ι I i) x)
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_lower_eq_self BoxIntegral.Box.splitLower_eq_selfₓ'. -/
@[simp]
theorem splitLower_eq_self : I.splitLower i x = I ↔ I.upper i ≤ x := by
  simp [split_lower, update_eq_iff]
#align box_integral.box.split_lower_eq_self BoxIntegral.Box.splitLower_eq_self

/- warning: box_integral.box.split_lower_def -> BoxIntegral.Box.splitLower_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : DecidableEq.{succ u1} ι] {i : ι} {x : Real} (h : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) (h' : optParam.{0} (forall (j : ι), LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x j)) (Iff.mpr (forall (x_1 : ι), (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y) x_1 (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x x_1)) (And ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y) i x) (forall (x : ι), (Ne.{succ u1} ι x i) -> ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y) x (BoxIntegral.Box.upper.{u1} ι I x)))) (Function.forall_update_iff.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y)) (And.intro ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y) i x) (forall (x : ι), (Ne.{succ u1} ι x i) -> ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt (BoxIntegral.Box.lower.{u1} ι I j) y) x (BoxIntegral.Box.upper.{u1} ι I x))) (And.left (LT.lt.{0} Real (Preorder.toHasLt.{0} Real Real.preorder) (BoxIntegral.Box.lower.{u1} ι I i) x) (LT.lt.{0} Real (Preorder.toHasLt.{0} Real Real.preorder) x (BoxIntegral.Box.upper.{u1} ι I i)) h) (fun (j : ι) (hne : Ne.{succ u1} ι j i) => BoxIntegral.Box.lower_lt_upper.{u1} ι I j)))), Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) (BoxIntegral.Box.mk.{u1} ι (BoxIntegral.Box.lower.{u1} ι I) (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x) h'))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : DecidableEq.{succ u1} ι] {i : ι} {x : Real} (h : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) (h' : optParam.{0} (forall (j : ι), LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I j) (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x j)) (Iff.mpr (forall (x_1 : ι), LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I x_1) (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x x_1)) (And (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I i) x) (forall (x : ι), (Ne.{succ u1} ι x i) -> (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I x) (BoxIntegral.Box.upper.{u1} ι I x)))) (Function.forall_update_iff.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I j) y)) (And.intro (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I i) x) (forall (x : ι), (Ne.{succ u1} ι x i) -> (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I x) (BoxIntegral.Box.upper.{u1} ι I x))) (And.left (LT.lt.{0} Real (Preorder.toLT.{0} Real Real.instPreorderReal) (BoxIntegral.Box.lower.{u1} ι I i) x) (LT.lt.{0} Real (Preorder.toLT.{0} Real Real.instPreorderReal) x (BoxIntegral.Box.upper.{u1} ι I i)) h) (fun (j : ι) (hne : Ne.{succ u1} ι j i) => BoxIntegral.Box.lower_lt_upper.{u1} ι I j)))), Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.mk.{u1} ι (BoxIntegral.Box.lower.{u1} ι I) (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.upper.{u1} ι I) i x) h'))
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_lower_def BoxIntegral.Box.splitLower_defₓ'. -/
theorem splitLower_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, I.lower j < update I.upper i x j :=
      (forall_update_iff I.upper fun j y => I.lower j < y).2
        ⟨h.1, fun j hne => I.lower_lt_upper _⟩) :
    I.splitLower i x = (⟨I.lower, update I.upper i x, h'⟩ : Box ι) :=
  by
  simp only [split_lower, mk'_eq_coe, min_eq_left h.2.le]
  use rfl
  congr
#align box_integral.box.split_lower_def BoxIntegral.Box.splitLower_def

#print BoxIntegral.Box.splitUpper /-
/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x` is the box `I ∩ {y | x < y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def splitUpper (I : Box ι) (i : ι) (x : ℝ) : WithBot (Box ι) :=
  mk' (update I.lower i (max x (I.lower i))) I.upper
#align box_integral.box.split_upper BoxIntegral.Box.splitUpper
-/

/- warning: box_integral.box.coe_split_upper -> BoxIntegral.Box.coe_splitUpper is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.withBotCoe.{u1} ι))) (BoxIntegral.Box.splitUpper.{u1} ι I i x)) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.hasLt x (y i))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.withBotToSet.{u1} ι (BoxIntegral.Box.splitUpper.{u1} ι I i x)) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.instLTReal x (y i))))
Case conversion may be inaccurate. Consider using '#align box_integral.box.coe_split_upper BoxIntegral.Box.coe_splitUpperₓ'. -/
@[simp]
theorem coe_splitUpper : (splitUpper I i x : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  by
  rw [split_upper, coe_mk']
  ext y
  simp only [mem_univ_pi, mem_Ioc, mem_inter_iff, mem_coe, mem_set_of_eq, forall_and,
    forall_update_iff I.lower fun j z => z < y j, max_lt_iff, and_assoc' (x < y i), and_forall_ne i,
    mem_def]
  exact and_comm' _ _
#align box_integral.box.coe_split_upper BoxIntegral.Box.coe_splitUpper

/- warning: box_integral.box.split_upper_le -> BoxIntegral.Box.splitUpper_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, LE.le.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toHasLe.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)))) (BoxIntegral.Box.splitUpper.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, LE.le.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (Preorder.toLE.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.preorder.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (BoxIntegral.Box.splitUpper.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) I)
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_upper_le BoxIntegral.Box.splitUpper_leₓ'. -/
theorem splitUpper_le : I.splitUpper i x ≤ I :=
  withBotCoe_subset_iff.1 <| by simp
#align box_integral.box.split_upper_le BoxIntegral.Box.splitUpper_le

/- warning: box_integral.box.split_upper_eq_bot -> BoxIntegral.Box.splitUpper_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) (Bot.bot.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasBot.{u1} (BoxIntegral.Box.{u1} ι)))) (LE.le.{0} Real Real.hasLe (BoxIntegral.Box.upper.{u1} ι I i) x)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) (Bot.bot.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.bot.{u1} (BoxIntegral.Box.{u1} ι)))) (LE.le.{0} Real Real.instLEReal (BoxIntegral.Box.upper.{u1} ι I i) x)
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_upper_eq_bot BoxIntegral.Box.splitUpper_eq_botₓ'. -/
@[simp]
theorem splitUpper_eq_bot {i x} : I.splitUpper i x = ⊥ ↔ I.upper i ≤ x :=
  by
  rw [split_upper, mk'_eq_bot, exists_update_iff I.lower fun j y => I.upper j ≤ y]
  simp [(I.lower_lt_upper _).not_le]
#align box_integral.box.split_upper_eq_bot BoxIntegral.Box.splitUpper_eq_bot

/- warning: box_integral.box.split_upper_eq_self -> BoxIntegral.Box.splitUpper_eq_self is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) I)) (LE.le.{0} Real Real.hasLe x (BoxIntegral.Box.lower.{u1} ι I i))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) I)) (LE.le.{0} Real Real.instLEReal x (BoxIntegral.Box.lower.{u1} ι I i))
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_upper_eq_self BoxIntegral.Box.splitUpper_eq_selfₓ'. -/
@[simp]
theorem splitUpper_eq_self : I.splitUpper i x = I ↔ x ≤ I.lower i := by
  simp [split_upper, update_eq_iff]
#align box_integral.box.split_upper_eq_self BoxIntegral.Box.splitUpper_eq_self

/- warning: box_integral.box.split_upper_def -> BoxIntegral.Box.splitUpper_def is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : DecidableEq.{succ u1} ι] {i : ι} {x : Real} (h : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) (h' : optParam.{0} (forall (j : ι), LT.lt.{0} Real Real.hasLt (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x j) (BoxIntegral.Box.upper.{u1} ι I j)) (Iff.mpr (forall (x_1 : ι), (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j)) x_1 (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x x_1)) (And ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j)) i x) (forall (x : ι), (Ne.{succ u1} ι x i) -> ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j)) x (BoxIntegral.Box.lower.{u1} ι I x)))) (Function.forall_update_iff.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j))) (And.intro ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j)) i x) (forall (x : ι), (Ne.{succ u1} ι x i) -> ((fun (j : ι) (y : Real) => LT.lt.{0} Real Real.hasLt y (BoxIntegral.Box.upper.{u1} ι I j)) x (BoxIntegral.Box.lower.{u1} ι I x))) (And.right (LT.lt.{0} Real (Preorder.toHasLt.{0} Real Real.preorder) (BoxIntegral.Box.lower.{u1} ι I i) x) (LT.lt.{0} Real (Preorder.toHasLt.{0} Real Real.preorder) x (BoxIntegral.Box.upper.{u1} ι I i)) h) (fun (j : ι) (hne : Ne.{succ u1} ι j i) => BoxIntegral.Box.lower_lt_upper.{u1} ι I j)))), Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) (BoxIntegral.Box.mk.{u1} ι (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x) (BoxIntegral.Box.upper.{u1} ι I) h'))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : DecidableEq.{succ u1} ι] {i : ι} {x : Real} (h : Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i))) (h' : optParam.{0} (forall (j : ι), LT.lt.{0} Real Real.instLTReal (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x j) (BoxIntegral.Box.upper.{u1} ι I j)) (Iff.mpr (forall (x_1 : ι), LT.lt.{0} Real Real.instLTReal (Function.update.{succ u1, 1} ι (fun (a : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x x_1) (BoxIntegral.Box.upper.{u1} ι I x_1)) (And (LT.lt.{0} Real Real.instLTReal x (BoxIntegral.Box.upper.{u1} ι I i)) (forall (x : ι), (Ne.{succ u1} ι x i) -> (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I x) (BoxIntegral.Box.upper.{u1} ι I x)))) (Function.forall_update_iff.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x (fun (j : ι) (y : Real) => LT.lt.{0} Real Real.instLTReal y (BoxIntegral.Box.upper.{u1} ι I j))) (And.intro (LT.lt.{0} Real Real.instLTReal x (BoxIntegral.Box.upper.{u1} ι I i)) (forall (x : ι), (Ne.{succ u1} ι x i) -> (LT.lt.{0} Real Real.instLTReal (BoxIntegral.Box.lower.{u1} ι I x) (BoxIntegral.Box.upper.{u1} ι I x))) (And.right (LT.lt.{0} Real (Preorder.toLT.{0} Real Real.instPreorderReal) (BoxIntegral.Box.lower.{u1} ι I i) x) (LT.lt.{0} Real (Preorder.toLT.{0} Real Real.instPreorderReal) x (BoxIntegral.Box.upper.{u1} ι I i)) h) (fun (j : ι) (hne : Ne.{succ u1} ι j i) => BoxIntegral.Box.lower_lt_upper.{u1} ι I j)))), Eq.{succ u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (BoxIntegral.Box.splitUpper.{u1} ι I i x) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.mk.{u1} ι (Function.update.{succ u1, 1} ι (fun (ᾰ : ι) => Real) (fun (a : ι) (b : ι) => _inst_1 a b) (BoxIntegral.Box.lower.{u1} ι I) i x) (BoxIntegral.Box.upper.{u1} ι I) h'))
Case conversion may be inaccurate. Consider using '#align box_integral.box.split_upper_def BoxIntegral.Box.splitUpper_defₓ'. -/
theorem splitUpper_def [DecidableEq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
    (h' : ∀ j, update I.lower i x j < I.upper j :=
      (forall_update_iff I.lower fun j y => y < I.upper j).2
        ⟨h.2, fun j hne => I.lower_lt_upper _⟩) :
    I.splitUpper i x = (⟨update I.lower i x, I.upper, h'⟩ : Box ι) :=
  by
  simp only [split_upper, mk'_eq_coe, max_eq_left h.1.le]
  refine' ⟨_, rfl⟩
  congr
#align box_integral.box.split_upper_def BoxIntegral.Box.splitUpper_def

/- warning: box_integral.box.disjoint_split_lower_split_upper -> BoxIntegral.Box.disjoint_splitLower_splitUpper is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) (i : ι) (x : Real), Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) (BoxIntegral.Box.splitLower.{u1} ι I i x) (BoxIntegral.Box.splitUpper.{u1} ι I i x)
but is expected to have type
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) (i : ι) (x : Real), Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (Preorder.toLE.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (BoxIntegral.Box.splitLower.{u1} ι I i x) (BoxIntegral.Box.splitUpper.{u1} ι I i x)
Case conversion may be inaccurate. Consider using '#align box_integral.box.disjoint_split_lower_split_upper BoxIntegral.Box.disjoint_splitLower_splitUpperₓ'. -/
theorem disjoint_splitLower_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    Disjoint (I.splitLower i x) (I.splitUpper i x) :=
  by
  rw [← disjoint_with_bot_coe, coe_split_lower, coe_split_upper]
  refine' (Disjoint.inf_left' _ _).inf_right' _
  rw [Set.disjoint_left]
  exact fun y (hle : y i ≤ x) hlt => not_lt_of_le hle hlt
#align box_integral.box.disjoint_split_lower_split_upper BoxIntegral.Box.disjoint_splitLower_splitUpper

#print BoxIntegral.Box.splitLower_ne_splitUpper /-
theorem splitLower_ne_splitUpper (I : Box ι) (i : ι) (x : ℝ) :
    I.splitLower i x ≠ I.splitUpper i x :=
  by
  cases le_or_lt x (I.lower i)
  · rw [split_upper_eq_self.2 h, split_lower_eq_bot.2 h]
    exact WithBot.bot_ne_coe
  · refine' (disjoint_split_lower_split_upper I i x).Ne _
    rwa [Ne.def, split_lower_eq_bot, not_le]
#align box_integral.box.split_lower_ne_split_upper BoxIntegral.Box.splitLower_ne_splitUpper
-/

end Box

namespace Prepartition

variable {I J : Box ι} {i : ι} {x : ℝ}

#print BoxIntegral.Prepartition.split /-
/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : Box ι) (i : ι) (x : ℝ) : Prepartition I :=
  ofWithBot {I.splitLower i x, I.splitUpper i x}
    (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro J (rfl | rfl)
      exacts[box.split_lower_le, box.split_upper_le])
    (by
      simp only [Finset.coe_insert, Finset.coe_singleton, true_and_iff, Set.mem_singleton_iff,
        pairwise_insert_of_symmetric symmetric_disjoint, pairwise_singleton]
      rintro J rfl -
      exact I.disjoint_split_lower_split_upper i x)
#align box_integral.prepartition.split BoxIntegral.Prepartition.split
-/

#print BoxIntegral.Prepartition.mem_split_iff /-
@[simp]
theorem mem_split_iff : J ∈ split I i x ↔ ↑J = I.splitLower i x ∨ ↑J = I.splitUpper i x := by
  simp [split]
#align box_integral.prepartition.mem_split_iff BoxIntegral.Prepartition.mem_split_iff
-/

/- warning: box_integral.prepartition.mem_split_iff' -> BoxIntegral.Prepartition.mem_split_iff' is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) (Or (Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.hasLe (y i) x)))) (Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.hasLt x (y i))))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, Iff (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) (Or (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.instLEReal (y i) x)))) (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.instLTReal x (y i))))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.mem_split_iff' BoxIntegral.Prepartition.mem_split_iff'ₓ'. -/
theorem mem_split_iff' :
    J ∈ split I i x ↔
      (J : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } ∨ (J : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  by simp [mem_split_iff, ← box.with_bot_coe_inj]
#align box_integral.prepartition.mem_split_iff' BoxIntegral.Prepartition.mem_split_iff'

#print BoxIntegral.Prepartition.iUnion_split /-
@[simp]
theorem iUnion_split (I : Box ι) (i : ι) (x : ℝ) : (split I i x).iUnion = I := by
  simp [split, ← inter_union_distrib_left, ← set_of_or, le_or_lt]
#align box_integral.prepartition.Union_split BoxIntegral.Prepartition.iUnion_split
-/

#print BoxIntegral.Prepartition.isPartitionSplit /-
theorem isPartitionSplit (I : Box ι) (i : ι) (x : ℝ) : IsPartition (split I i x) :=
  isPartition_iff_iUnion_eq.2 <| iUnion_split I i x
#align box_integral.prepartition.is_partition_split BoxIntegral.Prepartition.isPartitionSplit
-/

/- warning: box_integral.prepartition.sum_split_boxes -> BoxIntegral.Prepartition.sum_split_boxes is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] (I : BoxIntegral.Box.{u1} ι) (i : ι) (x : Real) (f : (BoxIntegral.Box.{u1} ι) -> M), Eq.{succ u2} M (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.Prepartition.split.{u1} ι I i x)) (fun (J : BoxIntegral.Box.{u1} ι) => f J)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toHasAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) f (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (OfNat.mk.{u2} M 0 (Zero.zero.{u2} M (AddZeroClass.toHasZero.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))))) f (BoxIntegral.Box.splitUpper.{u1} ι I i x)))
but is expected to have type
  forall {ι : Type.{u1}} {M : Type.{u2}} [_inst_1 : AddCommMonoid.{u2} M] (I : BoxIntegral.Box.{u1} ι) (i : ι) (x : Real) (f : (BoxIntegral.Box.{u1} ι) -> M), Eq.{succ u2} M (Finset.sum.{u2, u1} M (BoxIntegral.Box.{u1} ι) _inst_1 (BoxIntegral.Prepartition.boxes.{u1} ι I (BoxIntegral.Prepartition.split.{u1} ι I i x)) (fun (J : BoxIntegral.Box.{u1} ι) => f J)) (HAdd.hAdd.{u2, u2, u2} M M M (instHAdd.{u2} M (AddZeroClass.toAdd.{u2} M (AddMonoid.toAddZeroClass.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) f (BoxIntegral.Box.splitLower.{u1} ι I i x)) (Option.elim'.{u1, u2} (BoxIntegral.Box.{u1} ι) M (OfNat.ofNat.{u2} M 0 (Zero.toOfNat0.{u2} M (AddMonoid.toZero.{u2} M (AddCommMonoid.toAddMonoid.{u2} M _inst_1)))) f (BoxIntegral.Box.splitUpper.{u1} ι I i x)))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.sum_split_boxes BoxIntegral.Prepartition.sum_split_boxesₓ'. -/
theorem sum_split_boxes {M : Type _} [AddCommMonoid M] (I : Box ι) (i : ι) (x : ℝ) (f : Box ι → M) :
    (∑ J in (split I i x).boxes, f J) = (I.splitLower i x).elim 0 f + (I.splitUpper i x).elim 0 f :=
  by rw [split, sum_of_with_bot, Finset.sum_pair (I.split_lower_ne_split_upper i x)]
#align box_integral.prepartition.sum_split_boxes BoxIntegral.Prepartition.sum_split_boxes

/- warning: box_integral.prepartition.split_of_not_mem_Ioo -> BoxIntegral.Prepartition.split_of_not_mem_Ioo is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, (Not (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i)))) -> (Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.split.{u1} ι I i x) (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toHasTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.orderTop.{u1} ι I))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real}, (Not (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (BoxIntegral.Box.lower.{u1} ι I i) (BoxIntegral.Box.upper.{u1} ι I i)))) -> (Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.split.{u1} ι I i x) (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.instOrderTopPrepartitionInstLEPrepartition.{u1} ι I))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.split_of_not_mem_Ioo BoxIntegral.Prepartition.split_of_not_mem_Iooₓ'. -/
/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
theorem split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ :=
  by
  refine' ((is_partition_top I).eq_of_boxes_subset fun J hJ => _).symm
  rcases mem_top.1 hJ with rfl; clear hJ
  rw [mem_boxes, mem_split_iff]
  rw [mem_Ioo, not_and_or, not_lt, not_lt] at h
  cases h <;> [right, left]
  · rwa [eq_comm, box.split_upper_eq_self]
  · rwa [eq_comm, box.split_lower_eq_self]
#align box_integral.prepartition.split_of_not_mem_Ioo BoxIntegral.Prepartition.split_of_not_mem_Ioo

/- warning: box_integral.prepartition.coe_eq_of_mem_split_of_mem_le -> BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real} {y : ι -> Real}, (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) -> (Membership.Mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasMem.{u1} ι) y J) -> (LE.le.{0} Real Real.hasLe (y i) x) -> (Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.hasLe (y i) x))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real} {y : ι -> Real}, (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) -> (Membership.mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instMembershipForAllRealBox.{u1} ι) y J) -> (LE.le.{0} Real Real.instLEReal (y i) x) -> (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LE.le.{0} Real Real.instLEReal (y i) x))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.coe_eq_of_mem_split_of_mem_le BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_leₓ'. -/
theorem coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : y i ≤ x) : (J : Set (ι → ℝ)) = I ∩ { y | y i ≤ x } :=
  (mem_split_iff'.1 h₁).resolve_right fun H =>
    by
    rw [← box.mem_coe, H] at h₂
    exact h₃.not_lt h₂.2
#align box_integral.prepartition.coe_eq_of_mem_split_of_mem_le BoxIntegral.Prepartition.coe_eq_of_mem_split_of_mem_le

/- warning: box_integral.prepartition.coe_eq_of_mem_split_of_lt_mem -> BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_mem is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real} {y : ι -> Real}, (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) -> (Membership.Mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasMem.{u1} ι) y J) -> (LT.lt.{0} Real Real.hasLt x (y i)) -> (Eq.{succ u1} (Set.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.hasInter.{u1} (ι -> Real)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.hasLt x (y i)))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {i : ι} {x : Real} {y : ι -> Real}, (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J (BoxIntegral.Prepartition.split.{u1} ι I i x)) -> (Membership.mem.{u1, u1} (ι -> Real) (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instMembershipForAllRealBox.{u1} ι) y J) -> (LT.lt.{0} Real Real.instLTReal x (y i)) -> (Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι J) (Inter.inter.{u1} (Set.{u1} (ι -> Real)) (Set.instInterSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (setOf.{u1} (ι -> Real) (fun (y : ι -> Real) => LT.lt.{0} Real Real.instLTReal x (y i)))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.coe_eq_of_mem_split_of_lt_mem BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_memₓ'. -/
theorem coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J)
    (h₃ : x < y i) : (J : Set (ι → ℝ)) = I ∩ { y | x < y i } :=
  (mem_split_iff'.1 h₁).resolve_left fun H =>
    by
    rw [← box.mem_coe, H] at h₂
    exact h₃.not_le h₂.2
#align box_integral.prepartition.coe_eq_of_mem_split_of_lt_mem BoxIntegral.Prepartition.coe_eq_of_mem_split_of_lt_mem

#print BoxIntegral.Prepartition.restrict_split /-
@[simp]
theorem restrict_split (h : I ≤ J) (i : ι) (x : ℝ) : (split J i x).restrict I = split I i x :=
  by
  refine' ((is_partition_split J i x).restrict h).eq_of_boxes_subset _
  simp only [Finset.subset_iff, mem_boxes, mem_restrict', exists_prop, mem_split_iff']
  have : ∀ s, (I ∩ s : Set (ι → ℝ)) ⊆ J := fun s => (inter_subset_left _ _).trans h
  rintro J₁ ⟨J₂, H₂ | H₂, H₁⟩ <;> [left, right] <;> simp [H₁, H₂, inter_left_comm ↑I, this]
#align box_integral.prepartition.restrict_split BoxIntegral.Prepartition.restrict_split
-/

#print BoxIntegral.Prepartition.inf_split /-
theorem inf_split (π : Prepartition I) (i : ι) (x : ℝ) :
    π ⊓ split I i x = π.biUnion fun J => split J i x :=
  biUnion_congr_of_le rfl fun J hJ => restrict_split hJ i x
#align box_integral.prepartition.inf_split BoxIntegral.Prepartition.inf_split
-/

#print BoxIntegral.Prepartition.splitMany /-
/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def splitMany (I : Box ι) (s : Finset (ι × ℝ)) : Prepartition I :=
  s.inf fun p => split I p.1 p.2
#align box_integral.prepartition.split_many BoxIntegral.Prepartition.splitMany
-/

/- warning: box_integral.prepartition.split_many_empty -> BoxIntegral.Prepartition.splitMany_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι), Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.hasEmptyc.{u1} (Prod.{u1, 0} ι Real)))) (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toHasTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.orderTop.{u1} ι I)))
but is expected to have type
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι), Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I (EmptyCollection.emptyCollection.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.instEmptyCollectionFinset.{u1} (Prod.{u1, 0} ι Real)))) (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.instOrderTopPrepartitionInstLEPrepartition.{u1} ι I)))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.split_many_empty BoxIntegral.Prepartition.splitMany_emptyₓ'. -/
@[simp]
theorem splitMany_empty (I : Box ι) : splitMany I ∅ = ⊤ :=
  Finset.inf_empty
#align box_integral.prepartition.split_many_empty BoxIntegral.Prepartition.splitMany_empty

#print BoxIntegral.Prepartition.splitMany_insert /-
@[simp]
theorem splitMany_insert (I : Box ι) (s : Finset (ι × ℝ)) (p : ι × ℝ) :
    splitMany I (insert p s) = splitMany I s ⊓ split I p.1 p.2 := by
  rw [split_many, Finset.inf_insert, inf_comm, split_many]
#align box_integral.prepartition.split_many_insert BoxIntegral.Prepartition.splitMany_insert
-/

/- warning: box_integral.prepartition.split_many_le_split -> BoxIntegral.Prepartition.splitMany_le_split is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) {s : Finset.{u1} (Prod.{u1, 0} ι Real)} {p : Prod.{u1, 0} ι Real}, (Membership.Mem.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.hasMem.{u1} (Prod.{u1, 0} ι Real)) p s) -> (LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I s) (BoxIntegral.Prepartition.split.{u1} ι I (Prod.fst.{u1, 0} ι Real p) (Prod.snd.{u1, 0} ι Real p)))
but is expected to have type
  forall {ι : Type.{u1}} (I : BoxIntegral.Box.{u1} ι) {s : Finset.{u1} (Prod.{u1, 0} ι Real)} {p : Prod.{u1, 0} ι Real}, (Membership.mem.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.instMembershipFinset.{u1} (Prod.{u1, 0} ι Real)) p s) -> (LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I s) (BoxIntegral.Prepartition.split.{u1} ι I (Prod.fst.{u1, 0} ι Real p) (Prod.snd.{u1, 0} ι Real p)))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.split_many_le_split BoxIntegral.Prepartition.splitMany_le_splitₓ'. -/
theorem splitMany_le_split (I : Box ι) {s : Finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
    splitMany I s ≤ split I p.1 p.2 :=
  Finset.inf_le hp
#align box_integral.prepartition.split_many_le_split BoxIntegral.Prepartition.splitMany_le_split

#print BoxIntegral.Prepartition.isPartition_splitMany /-
theorem isPartition_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : IsPartition (splitMany I s) :=
  Finset.induction_on s (by simp only [split_many_empty, is_partition_top]) fun a s ha hs => by
    simpa only [split_many_insert, inf_split] using hs.bUnion fun J hJ => is_partition_split _ _ _
#align box_integral.prepartition.is_partition_split_many BoxIntegral.Prepartition.isPartition_splitMany
-/

#print BoxIntegral.Prepartition.iUnion_splitMany /-
@[simp]
theorem iUnion_splitMany (I : Box ι) (s : Finset (ι × ℝ)) : (splitMany I s).iUnion = I :=
  (isPartition_splitMany I s).iUnion_eq
#align box_integral.prepartition.Union_split_many BoxIntegral.Prepartition.iUnion_splitMany
-/

#print BoxIntegral.Prepartition.inf_splitMany /-
theorem inf_splitMany {I : Box ι} (π : Prepartition I) (s : Finset (ι × ℝ)) :
    π ⊓ splitMany I s = π.biUnion fun J => splitMany J s :=
  by
  induction' s using Finset.induction_on with p s hp ihp
  · simp
  · simp_rw [split_many_insert, ← inf_assoc, ihp, inf_split, bUnion_assoc]
#align box_integral.prepartition.inf_split_many BoxIntegral.Prepartition.inf_splitMany
-/

/- warning: box_integral.prepartition.not_disjoint_imp_le_of_subset_of_mem_split_many -> BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {Js : BoxIntegral.Box.{u1} ι} {s : Finset.{u1} (Prod.{u1, 0} ι Real)}, (forall (i : ι), HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.hasSubset.{u1} (Prod.{u1, 0} ι Real)) (Insert.insert.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.hasInsert.{u1} (Prod.{u1, 0} ι Real) (fun (a : Prod.{u1, 0} ι Real) (b : Prod.{u1, 0} ι Real) => Prod.Lex.decidableEq.{u1, 0} ι Real (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b)) (Prod.mk.{u1, 0} ι Real i (BoxIntegral.Box.lower.{u1} ι J i)) (Singleton.singleton.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.hasSingleton.{u1} (Prod.{u1, 0} ι Real)) (Prod.mk.{u1, 0} ι Real i (BoxIntegral.Box.upper.{u1} ι J i)))) s) -> (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) Js (BoxIntegral.Prepartition.splitMany.{u1} ι I s)) -> (Not (Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) J) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) Js))) -> (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) Js J)
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} {J : BoxIntegral.Box.{u1} ι} {Js : BoxIntegral.Box.{u1} ι} {s : Finset.{u1} (Prod.{u1, 0} ι Real)}, (forall (i : ι), HasSubset.Subset.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.instHasSubsetFinset.{u1} (Prod.{u1, 0} ι Real)) (Insert.insert.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.instInsertFinset.{u1} (Prod.{u1, 0} ι Real) (fun (a : Prod.{u1, 0} ι Real) (b : Prod.{u1, 0} ι Real) => instDecidableEqProd.{u1, 0} ι Real (fun (a : ι) (b : ι) => Classical.propDecidable (Eq.{succ u1} ι a b)) (fun (a : Real) (b : Real) => Real.decidableEq a b) a b)) (Prod.mk.{u1, 0} ι Real i (BoxIntegral.Box.lower.{u1} ι J i)) (Singleton.singleton.{u1, u1} (Prod.{u1, 0} ι Real) (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.instSingletonFinset.{u1} (Prod.{u1, 0} ι Real)) (Prod.mk.{u1, 0} ι Real i (BoxIntegral.Box.upper.{u1} ι J i)))) s) -> (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) Js (BoxIntegral.Prepartition.splitMany.{u1} ι I s)) -> (Not (Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (Preorder.toLE.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) J) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) Js))) -> (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) Js J)
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.not_disjoint_imp_le_of_subset_of_mem_split_many BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitManyₓ'. -/
/-- Let `s : finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι → ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyperplanes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty intersection, then
`Js` is a subbox of `J`.  -/
theorem not_disjoint_imp_le_of_subset_of_mem_splitMany {I J Js : Box ι} {s : Finset (ι × ℝ)}
    (H : ∀ i, {(i, J i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ splitMany I s)
    (Hn : ¬Disjoint (J : WithBot (Box ι)) Js) : Js ≤ J :=
  by
  simp only [Finset.insert_subset, Finset.singleton_subset_iff] at H
  rcases box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩
  refine' fun y hy i => ⟨_, _⟩
  · rcases split_many_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.lower i), Hle⟩
    have := Hle hxs
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle
    exact (Hle hy).2
  · rcases split_many_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.upper i), Hle⟩
    have := Hle hxs
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle
    exact (Hle hy).2
#align box_integral.prepartition.not_disjoint_imp_le_of_subset_of_mem_split_many BoxIntegral.Prepartition.not_disjoint_imp_le_of_subset_of_mem_splitMany

section Fintype

variable [Finite ι]

/- warning: box_integral.prepartition.eventually_not_disjoint_imp_le_of_mem_split_many -> BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] (s : Finset.{u1} (BoxIntegral.Box.{u1} ι)), Filter.Eventually.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (fun (t : Finset.{u1} (Prod.{u1, 0} ι Real)) => forall (I : BoxIntegral.Box.{u1} ι) (J : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.hasMem.{u1} (BoxIntegral.Box.{u1} ι)) J s) -> (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.Mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasMem.{u1} ι I) J' (BoxIntegral.Prepartition.splitMany.{u1} ι I t)) -> (Not (Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.partialOrder.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι)) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) J) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.hasCoeT.{u1} (BoxIntegral.Box.{u1} ι)))) J'))) -> (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.hasLe.{u1} ι) J' J))) (Filter.atTop.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.partialOrder.{u1} (Prod.{u1, 0} ι Real))))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] (s : Finset.{u1} (BoxIntegral.Box.{u1} ι)), Filter.Eventually.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (fun (t : Finset.{u1} (Prod.{u1, 0} ι Real)) => forall (I : BoxIntegral.Box.{u1} ι) (J : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (Finset.{u1} (BoxIntegral.Box.{u1} ι)) (Finset.instMembershipFinset.{u1} (BoxIntegral.Box.{u1} ι)) J s) -> (forall (J' : BoxIntegral.Box.{u1} ι), (Membership.mem.{u1, u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instMembershipBoxPrepartition.{u1} ι I) J' (BoxIntegral.Prepartition.splitMany.{u1} ι I t)) -> (Not (Disjoint.{u1} (WithBot.{u1} (BoxIntegral.Box.{u1} ι)) (WithBot.partialOrder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)) (WithBot.orderBot.{u1} (BoxIntegral.Box.{u1} ι) (Preorder.toLE.{u1} (BoxIntegral.Box.{u1} ι) (PartialOrder.toPreorder.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instPartialOrderBox.{u1} ι)))) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) J) (WithBot.some.{u1} (BoxIntegral.Box.{u1} ι) J'))) -> (LE.le.{u1} (BoxIntegral.Box.{u1} ι) (BoxIntegral.Box.instLEBox.{u1} ι) J' J))) (Filter.atTop.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (PartialOrder.toPreorder.{u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (Finset.partialOrder.{u1} (Prod.{u1, 0} ι Real))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.eventually_not_disjoint_imp_le_of_mem_split_many BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitManyₓ'. -/
/-- Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for any `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes have a nonempty
intersection, then `J' ≤ J`. -/
theorem eventually_not_disjoint_imp_le_of_mem_splitMany (s : Finset (Box ι)) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop,
      ∀ (I : Box ι), ∀ J ∈ s, ∀ J' ∈ splitMany I t, ¬Disjoint (J : WithBot (Box ι)) J' → J' ≤ J :=
  by
  cases nonempty_fintype ι
  refine'
    eventually_at_top.2
      ⟨s.bUnion fun J => finset.univ.bUnion fun i => {(i, J i), (i, J.upper i)},
        fun t ht I J hJ J' hJ' => not_disjoint_imp_le_of_subset_of_mem_split_many (fun i => _) hJ'⟩
  exact fun p hp =>
    ht (Finset.mem_biUnion.2 ⟨J, hJ, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩⟩)
#align box_integral.prepartition.eventually_not_disjoint_imp_le_of_mem_split_many BoxIntegral.Prepartition.eventually_not_disjoint_imp_le_of_mem_splitMany

#print BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter /-
theorem eventually_splitMany_inf_eq_filter (π : Prepartition I) :
    ∀ᶠ t : Finset (ι × ℝ) in atTop,
      π ⊓ splitMany I t = (splitMany I t).filterₓ fun J => ↑J ⊆ π.iUnion :=
  by
  refine' (eventually_not_disjoint_imp_le_of_mem_split_many π.boxes).mono fun t ht => _
  refine' le_antisymm ((bUnion_le_iff _).2 fun J hJ => _) (le_inf (fun J hJ => _) (filter_le _ _))
  · refine' of_with_bot_mono _
    simp only [Finset.mem_image, exists_prop, mem_boxes, mem_filter]
    rintro _ ⟨J₁, h₁, rfl⟩ hne
    refine' ⟨_, ⟨J₁, ⟨h₁, subset.trans _ (π.subset_Union hJ)⟩, rfl⟩, le_rfl⟩
    exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne)
  · rw [mem_filter] at hJ
    rcases Set.mem_iUnion₂.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩
    refine' ⟨J', hJ', ht I _ hJ' _ hJ.1 <| box.not_disjoint_coe_iff_nonempty_inter.2 _⟩
    exact ⟨J.upper, hmem, J.upper_mem⟩
#align box_integral.prepartition.eventually_split_many_inf_eq_filter BoxIntegral.Prepartition.eventually_splitMany_inf_eq_filter
-/

#print BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite /-
theorem exists_splitMany_inf_eq_filter_of_finite (s : Set (Prepartition I)) (hs : s.Finite) :
    ∃ t : Finset (ι × ℝ),
      ∀ π ∈ s, π ⊓ splitMany I t = (splitMany I t).filterₓ fun J => ↑J ⊆ π.iUnion :=
  haveI := fun π (hπ : π ∈ s) => eventually_split_many_inf_eq_filter π
  (hs.eventually_all.2 this).exists
#align box_integral.prepartition.exists_split_many_inf_eq_filter_of_finite BoxIntegral.Prepartition.exists_splitMany_inf_eq_filter_of_finite
-/

/- warning: box_integral.prepartition.is_partition.exists_split_many_le -> BoxIntegral.Prepartition.IsPartition.exists_splitMany_le is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.Prepartition.{u1} ι I}, (BoxIntegral.Prepartition.IsPartition.{u1} ι I π) -> (Exists.{succ u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (fun (s : Finset.{u1} (Prod.{u1, 0} ι Real)) => LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I s) π))
but is expected to have type
  forall {ι : Type.{u1}} [_inst_1 : Finite.{succ u1} ι] {I : BoxIntegral.Box.{u1} ι} {π : BoxIntegral.Prepartition.{u1} ι I}, (BoxIntegral.Prepartition.IsPartition.{u1} ι I π) -> (Exists.{succ u1} (Finset.{u1} (Prod.{u1, 0} ι Real)) (fun (s : Finset.{u1} (Prod.{u1, 0} ι Real)) => LE.le.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.splitMany.{u1} ι I s) π))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.is_partition.exists_split_many_le BoxIntegral.Prepartition.IsPartition.exists_splitMany_leₓ'. -/
/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`split_many I s ≤ π`. -/
theorem IsPartition.exists_splitMany_le {I : Box ι} {π : Prepartition I} (h : IsPartition π) :
    ∃ s, splitMany I s ≤ π :=
  (eventually_splitMany_inf_eq_filter π).exists.imp fun s hs =>
    by
    rwa [h.Union_eq, filter_of_true, inf_eq_right] at hs
    exact fun J hJ => le_of_mem _ hJ
#align box_integral.prepartition.is_partition.exists_split_many_le BoxIntegral.Prepartition.IsPartition.exists_splitMany_le

/- warning: box_integral.prepartition.exists_Union_eq_diff -> BoxIntegral.Prepartition.exists_iUnion_eq_diff is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I), Exists.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (fun (π' : BoxIntegral.Prepartition.{u1} ι I) => Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π') (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I), Exists.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (fun (π' : BoxIntegral.Prepartition.{u1} ι I) => Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I π') (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.Prepartition.iUnion.{u1} ι I π)))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.exists_Union_eq_diff BoxIntegral.Prepartition.exists_iUnion_eq_diffₓ'. -/
/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.Union`. -/
theorem exists_iUnion_eq_diff (π : Prepartition I) :
    ∃ π' : Prepartition I, π'.iUnion = I \ π.iUnion :=
  by
  rcases π.eventually_split_many_inf_eq_filter.exists with ⟨s, hs⟩
  use (split_many I s).filterₓ fun J => ¬(J : Set (ι → ℝ)) ⊆ π.Union
  simp [← hs]
#align box_integral.prepartition.exists_Union_eq_diff BoxIntegral.Prepartition.exists_iUnion_eq_diff

#print BoxIntegral.Prepartition.compl /-
/-- If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.Union = I \ π.Union`. -/
def compl (π : Prepartition I) : Prepartition I :=
  π.exists_iUnion_eq_diff.some
#align box_integral.prepartition.compl BoxIntegral.Prepartition.compl
-/

/- warning: box_integral.prepartition.Union_compl -> BoxIntegral.Prepartition.iUnion_compl is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 π)) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (BooleanAlgebra.toHasSdiff.{u1} (Set.{u1} (ι -> Real)) (Set.booleanAlgebra.{u1} (ι -> Real))) ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (HasLiftT.mk.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (CoeTCₓ.coe.{succ u1, succ u1} (BoxIntegral.Box.{u1} ι) (Set.{u1} (ι -> Real)) (BoxIntegral.Box.Set.hasCoeT.{u1} ι))) I) (BoxIntegral.Prepartition.iUnion.{u1} ι I π))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] (π : BoxIntegral.Prepartition.{u1} ι I), Eq.{succ u1} (Set.{u1} (ι -> Real)) (BoxIntegral.Prepartition.iUnion.{u1} ι I (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 π)) (SDiff.sdiff.{u1} (Set.{u1} (ι -> Real)) (Set.instSDiffSet.{u1} (ι -> Real)) (BoxIntegral.Box.toSet.{u1} ι I) (BoxIntegral.Prepartition.iUnion.{u1} ι I π))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.Union_compl BoxIntegral.Prepartition.iUnion_complₓ'. -/
@[simp]
theorem iUnion_compl (π : Prepartition I) : π.compl.iUnion = I \ π.iUnion :=
  π.exists_iUnion_eq_diff.choose_spec
#align box_integral.prepartition.Union_compl BoxIntegral.Prepartition.iUnion_compl

#print BoxIntegral.Prepartition.compl_congr /-
/-- Since the definition of `box_integral.prepartition.compl` uses `Exists.some`,
the result depends only on `π.Union`. -/
theorem compl_congr {π₁ π₂ : Prepartition I} (h : π₁.iUnion = π₂.iUnion) : π₁.compl = π₂.compl :=
  by
  dsimp only [compl]
  congr 1
  rw [h]
#align box_integral.prepartition.compl_congr BoxIntegral.Prepartition.compl_congr
-/

/- warning: box_integral.prepartition.is_partition.compl_eq_bot -> BoxIntegral.Prepartition.IsPartition.compl_eq_bot is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] {π : BoxIntegral.Prepartition.{u1} ι I}, (BoxIntegral.Prepartition.IsPartition.{u1} ι I π) -> (Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 π) (Bot.bot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderBot.toHasBot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.orderBot.{u1} ι I))))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι] {π : BoxIntegral.Prepartition.{u1} ι I}, (BoxIntegral.Prepartition.IsPartition.{u1} ι I π) -> (Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 π) (Bot.bot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderBot.toBot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.instOrderBotPrepartitionInstLEPrepartition.{u1} ι I))))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.is_partition.compl_eq_bot BoxIntegral.Prepartition.IsPartition.compl_eq_botₓ'. -/
theorem IsPartition.compl_eq_bot {π : Prepartition I} (h : IsPartition π) : π.compl = ⊥ := by
  rw [← Union_eq_empty, Union_compl, h.Union_eq, diff_self]
#align box_integral.prepartition.is_partition.compl_eq_bot BoxIntegral.Prepartition.IsPartition.compl_eq_bot

/- warning: box_integral.prepartition.compl_top -> BoxIntegral.Prepartition.compl_top is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι], Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toHasTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.orderTop.{u1} ι I)))) (Bot.bot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderBot.toHasBot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.hasLe.{u1} ι I) (BoxIntegral.Prepartition.orderBot.{u1} ι I)))
but is expected to have type
  forall {ι : Type.{u1}} {I : BoxIntegral.Box.{u1} ι} [_inst_1 : Finite.{succ u1} ι], Eq.{succ u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.compl.{u1} ι I _inst_1 (Top.top.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderTop.toTop.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.instOrderTopPrepartitionInstLEPrepartition.{u1} ι I)))) (Bot.bot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (OrderBot.toBot.{u1} (BoxIntegral.Prepartition.{u1} ι I) (BoxIntegral.Prepartition.instLEPrepartition.{u1} ι I) (BoxIntegral.Prepartition.instOrderBotPrepartitionInstLEPrepartition.{u1} ι I)))
Case conversion may be inaccurate. Consider using '#align box_integral.prepartition.compl_top BoxIntegral.Prepartition.compl_topₓ'. -/
@[simp]
theorem compl_top : (⊤ : Prepartition I).compl = ⊥ :=
  (isPartitionTop I).compl_eq_bot
#align box_integral.prepartition.compl_top BoxIntegral.Prepartition.compl_top

end Fintype

end Prepartition

end BoxIntegral

