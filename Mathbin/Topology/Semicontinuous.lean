/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.semicontinuous
! leanprover-community/mathlib commit 10bf4f825ad729c5653adc039dafa3622e7f93c9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Topology.ContinuousOn
import Mathbin.Topology.Instances.Ennreal

/-!
# Semicontinuous maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A function `f` from a topological space `α` to an ordered space `β` is lower semicontinuous at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it can not jump down.

Upper semicontinuous functions are defined similarly.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 definitions related to lower semicontinuity:
* `lower_semicontinuous_within_at f s x`
* `lower_semicontinuous_at f x`
* `lower_semicontinuous_on f s`
* `lower_semicontinuous f`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are lower semicontinuous;
* `indicator s (λ _, y)` is lower semicontinuous when `s` is open and `0 ≤ y`, or when `s` is closed
  and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `order_dual`.

-/


open Topology BigOperators ENNReal

open Set Function Filter

variable {α : Type _} [TopologicalSpace α] {β : Type _} [Preorder β] {f g : α → β} {x : α}
  {s t : Set α} {y z : β}

/-! ### Main definitions -/


#print LowerSemicontinuousWithinAt /-
/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝[s] x, y < f x'
#align lower_semicontinuous_within_at LowerSemicontinuousWithinAt
-/

#print LowerSemicontinuousOn /-
/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`.-/
def LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, LowerSemicontinuousWithinAt f s x
#align lower_semicontinuous_on LowerSemicontinuousOn
-/

#print LowerSemicontinuousAt /-
/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y < f x, ∀ᶠ x' in 𝓝 x, y < f x'
#align lower_semicontinuous_at LowerSemicontinuousAt
-/

#print LowerSemicontinuous /-
/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
def LowerSemicontinuous (f : α → β) :=
  ∀ x, LowerSemicontinuousAt f x
#align lower_semicontinuous LowerSemicontinuous
-/

#print UpperSemicontinuousWithinAt /-
/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in  `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y
#align upper_semicontinuous_within_at UpperSemicontinuousWithinAt
-/

#print UpperSemicontinuousOn /-
/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  ∀ x ∈ s, UpperSemicontinuousWithinAt f s x
#align upper_semicontinuous_on UpperSemicontinuousOn
-/

#print UpperSemicontinuousAt /-
/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
def UpperSemicontinuousAt (f : α → β) (x : α) :=
  ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y
#align upper_semicontinuous_at UpperSemicontinuousAt
-/

#print UpperSemicontinuous /-
/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`.-/
def UpperSemicontinuous (f : α → β) :=
  ∀ x, UpperSemicontinuousAt f x
#align upper_semicontinuous UpperSemicontinuous
-/

/-!
### Lower semicontinuous functions
-/


/-! #### Basic dot notation interface for lower semicontinuity -/


/- warning: lower_semicontinuous_within_at.mono -> LowerSemicontinuousWithinAt.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α} {t : Set.{u2} α}, (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t s) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f t x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at.mono LowerSemicontinuousWithinAt.monoₓ'. -/
theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
#align lower_semicontinuous_within_at.mono LowerSemicontinuousWithinAt.mono

/- warning: lower_semicontinuous_within_at_univ_iff -> lowerSemicontinuousWithinAt_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α}, Iff (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f (Set.univ.{u1} α) x) (LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α}, Iff (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f (Set.univ.{u2} α) x) (LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_univ_iff lowerSemicontinuousWithinAt_univ_iffₓ'. -/
theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x := by
  simp [LowerSemicontinuousWithinAt, LowerSemicontinuousAt, nhdsWithin_univ]
#align lower_semicontinuous_within_at_univ_iff lowerSemicontinuousWithinAt_univ_iff

/- warning: lower_semicontinuous_at.lower_semicontinuous_within_at -> LowerSemicontinuousAt.lowerSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} (s : Set.{u1} α), (LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} (s : Set.{u2} α), (LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at.lower_semicontinuous_within_at LowerSemicontinuousAt.lowerSemicontinuousWithinAtₓ'. -/
theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
#align lower_semicontinuous_at.lower_semicontinuous_within_at LowerSemicontinuousAt.lowerSemicontinuousWithinAt

/- warning: lower_semicontinuous_on.lower_semicontinuous_within_at -> LowerSemicontinuousOn.lowerSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on.lower_semicontinuous_within_at LowerSemicontinuousOn.lowerSemicontinuousWithinAtₓ'. -/
theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x ∈ s) : LowerSemicontinuousWithinAt f s x :=
  h x hx
#align lower_semicontinuous_on.lower_semicontinuous_within_at LowerSemicontinuousOn.lowerSemicontinuousWithinAt

/- warning: lower_semicontinuous_on.mono -> LowerSemicontinuousOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t s) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f t)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on.mono LowerSemicontinuousOn.monoₓ'. -/
theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
    LowerSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst
#align lower_semicontinuous_on.mono LowerSemicontinuousOn.mono

/- warning: lower_semicontinuous_on_univ_iff -> lowerSemicontinuousOn_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, Iff (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f (Set.univ.{u1} α)) (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, Iff (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f (Set.univ.{u2} α)) (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_univ_iff lowerSemicontinuousOn_univ_iffₓ'. -/
theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f := by
  simp [LowerSemicontinuousOn, LowerSemicontinuous, lowerSemicontinuousWithinAt_univ_iff]
#align lower_semicontinuous_on_univ_iff lowerSemicontinuousOn_univ_iff

/- warning: lower_semicontinuous.lower_semicontinuous_at -> LowerSemicontinuous.lowerSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (x : α), LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (x : α), LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.lower_semicontinuous_at LowerSemicontinuous.lowerSemicontinuousAtₓ'. -/
theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x
#align lower_semicontinuous.lower_semicontinuous_at LowerSemicontinuous.lowerSemicontinuousAt

/- warning: lower_semicontinuous.lower_semicontinuous_within_at -> LowerSemicontinuous.lowerSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u1} α) (x : α), LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u2} α) (x : α), LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.lower_semicontinuous_within_at LowerSemicontinuous.lowerSemicontinuousWithinAtₓ'. -/
theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).LowerSemicontinuousWithinAt s
#align lower_semicontinuous.lower_semicontinuous_within_at LowerSemicontinuous.lowerSemicontinuousWithinAt

/- warning: lower_semicontinuous.lower_semicontinuous_on -> LowerSemicontinuous.lowerSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u1} α), LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u2} α), LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.lower_semicontinuous_on LowerSemicontinuous.lowerSemicontinuousOnₓ'. -/
theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s := fun x hx => h.LowerSemicontinuousWithinAt s x
#align lower_semicontinuous.lower_semicontinuous_on LowerSemicontinuous.lowerSemicontinuousOn

/-! #### Constants -/


/- warning: lower_semicontinuous_within_at_const -> lowerSemicontinuousWithinAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {z : β}, LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) s x
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {z : β}, LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) s x
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_const lowerSemicontinuousWithinAt_constₓ'. -/
theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun x => z) s x :=
  fun y hy => Filter.eventually_of_forall fun x => hy
#align lower_semicontinuous_within_at_const lowerSemicontinuousWithinAt_const

/- warning: lower_semicontinuous_at_const -> lowerSemicontinuousAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {z : β}, LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) x
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {z : β}, LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) x
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_const lowerSemicontinuousAt_constₓ'. -/
theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun x => z) x := fun y hy =>
  Filter.eventually_of_forall fun x => hy
#align lower_semicontinuous_at_const lowerSemicontinuousAt_const

/- warning: lower_semicontinuous_on_const -> lowerSemicontinuousOn_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {z : β}, LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) s
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {z : β}, LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) s
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_const lowerSemicontinuousOn_constₓ'. -/
theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun x => z) s := fun x hx =>
  lowerSemicontinuousWithinAt_const
#align lower_semicontinuous_on_const lowerSemicontinuousOn_const

/- warning: lower_semicontinuous_const -> lowerSemicontinuous_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {z : β}, LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {z : β}, LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_const lowerSemicontinuous_constₓ'. -/
theorem lowerSemicontinuous_const : LowerSemicontinuous fun x : α => z := fun x =>
  lowerSemicontinuousAt_const
#align lower_semicontinuous_const lowerSemicontinuous_const

/-! #### Indicators -/


section

variable [Zero β]

/- warning: is_open.lower_semicontinuous_indicator -> IsOpen.lowerSemicontinuous_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)))
Case conversion may be inaccurate. Consider using '#align is_open.lower_semicontinuous_indicator IsOpen.lowerSemicontinuous_indicatorₓ'. -/
theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuous (indicator s fun x => y) :=
  by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp (config := { contextual := true }) [hz]
  · apply Filter.eventually_of_forall fun x' => _
    by_cases h' : x' ∈ s <;> simp [h', hz.trans_le hy, hz]
#align is_open.lower_semicontinuous_indicator IsOpen.lowerSemicontinuous_indicator

/- warning: is_open.lower_semicontinuous_on_indicator -> IsOpen.lowerSemicontinuousOn_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t)
Case conversion may be inaccurate. Consider using '#align is_open.lower_semicontinuous_on_indicator IsOpen.lowerSemicontinuousOn_indicatorₓ'. -/
theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousOn (indicator s fun x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousOn t
#align is_open.lower_semicontinuous_on_indicator IsOpen.lowerSemicontinuousOn_indicator

/- warning: is_open.lower_semicontinuous_at_indicator -> IsOpen.lowerSemicontinuousAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) x)
Case conversion may be inaccurate. Consider using '#align is_open.lower_semicontinuous_at_indicator IsOpen.lowerSemicontinuousAt_indicatorₓ'. -/
theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousAt (indicator s fun x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousAt x
#align is_open.lower_semicontinuous_at_indicator IsOpen.lowerSemicontinuousAt_indicator

/- warning: is_open.lower_semicontinuous_within_at_indicator -> IsOpen.lowerSemicontinuousWithinAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t x)
Case conversion may be inaccurate. Consider using '#align is_open.lower_semicontinuous_within_at_indicator IsOpen.lowerSemicontinuousWithinAt_indicatorₓ'. -/
theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 ≤ y) :
    LowerSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousWithinAt t x
#align is_open.lower_semicontinuous_within_at_indicator IsOpen.lowerSemicontinuousWithinAt_indicator

/- warning: is_closed.lower_semicontinuous_indicator -> IsClosed.lowerSemicontinuous_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)))
Case conversion may be inaccurate. Consider using '#align is_closed.lower_semicontinuous_indicator IsClosed.lowerSemicontinuous_indicatorₓ'. -/
theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuous (indicator s fun x => y) :=
  by
  intro x z hz
  by_cases h : x ∈ s <;> simp [h] at hz
  · apply Filter.eventually_of_forall fun x' => _
    by_cases h' : x' ∈ s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.is_open_compl.mem_nhds h]
    simp (config := { contextual := true }) [hz]
#align is_closed.lower_semicontinuous_indicator IsClosed.lowerSemicontinuous_indicator

/- warning: is_closed.lower_semicontinuous_on_indicator -> IsClosed.lowerSemicontinuousOn_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t)
Case conversion may be inaccurate. Consider using '#align is_closed.lower_semicontinuous_on_indicator IsClosed.lowerSemicontinuousOn_indicatorₓ'. -/
theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousOn (indicator s fun x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousOn t
#align is_closed.lower_semicontinuous_on_indicator IsClosed.lowerSemicontinuousOn_indicator

/- warning: is_closed.lower_semicontinuous_at_indicator -> IsClosed.lowerSemicontinuousAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) x)
Case conversion may be inaccurate. Consider using '#align is_closed.lower_semicontinuous_at_indicator IsClosed.lowerSemicontinuousAt_indicatorₓ'. -/
theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousAt (indicator s fun x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousAt x
#align is_closed.lower_semicontinuous_at_indicator IsClosed.lowerSemicontinuousAt_indicator

/- warning: is_closed.lower_semicontinuous_within_at_indicator -> IsClosed.lowerSemicontinuousWithinAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t x)
Case conversion may be inaccurate. Consider using '#align is_closed.lower_semicontinuous_within_at_indicator IsClosed.lowerSemicontinuousWithinAt_indicatorₓ'. -/
theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y ≤ 0) :
    LowerSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).LowerSemicontinuousWithinAt t x
#align is_closed.lower_semicontinuous_within_at_indicator IsClosed.lowerSemicontinuousWithinAt_indicator

end

/-! #### Relationship with continuity -/


/- warning: lower_semicontinuous_iff_is_open_preimage -> lowerSemicontinuous_iff_isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, Iff (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) (forall (y : β), IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f (Set.Ioi.{u2} β _inst_2 y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, Iff (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) (forall (y : β), IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f (Set.Ioi.{u1} β _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_iff_is_open_preimage lowerSemicontinuous_iff_isOpen_preimageₓ'. -/
theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
#align lower_semicontinuous_iff_is_open_preimage lowerSemicontinuous_iff_isOpen_preimage

/- warning: lower_semicontinuous.is_open_preimage -> LowerSemicontinuous.isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (LowerSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (y : β), IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f (Set.Ioi.{u2} β _inst_2 y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (LowerSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (y : β), IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f (Set.Ioi.{u1} β _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.is_open_preimage LowerSemicontinuous.isOpen_preimageₓ'. -/
theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y
#align lower_semicontinuous.is_open_preimage LowerSemicontinuous.isOpen_preimage

section

variable {γ : Type _} [LinearOrder γ]

/- warning: lower_semicontinuous_iff_is_closed_preimage -> lowerSemicontinuous_iff_isClosed_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] {f : α -> γ}, Iff (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) (forall (y : γ), IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α γ f (Set.Iic.{u2} γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] {f : α -> γ}, Iff (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f) (forall (y : γ), IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α γ f (Set.Iic.{u1} γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) y)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_iff_is_closed_preimage lowerSemicontinuous_iff_isClosed_preimageₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ y, (_ : exprProp())]] -/
theorem lowerSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    LowerSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Iic y) :=
  by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ y, (_ : exprProp())]]"
  rw [← isOpen_compl_iff, ← preimage_compl, compl_Iic]
#align lower_semicontinuous_iff_is_closed_preimage lowerSemicontinuous_iff_isClosed_preimage

/- warning: lower_semicontinuous.is_closed_preimage -> LowerSemicontinuous.isClosed_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] {f : α -> γ}, (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (forall (y : γ), IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α γ f (Set.Iic.{u2} γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] {f : α -> γ}, (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f) -> (forall (y : γ), IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α γ f (Set.Iic.{u1} γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) y)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.is_closed_preimage LowerSemicontinuous.isClosed_preimageₓ'. -/
theorem LowerSemicontinuous.isClosed_preimage {f : α → γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y
#align lower_semicontinuous.is_closed_preimage LowerSemicontinuous.isClosed_preimage

variable [TopologicalSpace γ] [OrderTopology γ]

/- warning: continuous_within_at.lower_semicontinuous_within_at -> ContinuousWithinAt.lowerSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_4 f s x) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousWithinAt.{u2, u1} α γ _inst_1 _inst_4 f s x) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.lower_semicontinuous_within_at ContinuousWithinAt.lowerSemicontinuousWithinAtₓ'. -/
theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun y hy => h (Ioi_mem_nhds hy)
#align continuous_within_at.lower_semicontinuous_within_at ContinuousWithinAt.lowerSemicontinuousWithinAt

/- warning: continuous_at.lower_semicontinuous_at -> ContinuousAt.lowerSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousAt.{u1, u2} α γ _inst_1 _inst_4 f x) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousAt.{u2, u1} α γ _inst_1 _inst_4 f x) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f x)
Case conversion may be inaccurate. Consider using '#align continuous_at.lower_semicontinuous_at ContinuousAt.lowerSemicontinuousAtₓ'. -/
theorem ContinuousAt.lowerSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun y hy => h (Ioi_mem_nhds hy)
#align continuous_at.lower_semicontinuous_at ContinuousAt.lowerSemicontinuousAt

/- warning: continuous_on.lower_semicontinuous_on -> ContinuousOn.lowerSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousOn.{u1, u2} α γ _inst_1 _inst_4 f s) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousOn.{u2, u1} α γ _inst_1 _inst_4 f s) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s)
Case conversion may be inaccurate. Consider using '#align continuous_on.lower_semicontinuous_on ContinuousOn.lowerSemicontinuousOnₓ'. -/
theorem ContinuousOn.lowerSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).LowerSemicontinuousWithinAt
#align continuous_on.lower_semicontinuous_on ContinuousOn.lowerSemicontinuousOn

/- warning: continuous.lower_semicontinuous -> Continuous.lowerSemicontinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (Continuous.{u1, u2} α γ _inst_1 _inst_4 f) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (Continuous.{u2, u1} α γ _inst_1 _inst_4 f) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f)
Case conversion may be inaccurate. Consider using '#align continuous.lower_semicontinuous Continuous.lowerSemicontinuousₓ'. -/
theorem Continuous.lowerSemicontinuous {f : α → γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun x => h.ContinuousAt.LowerSemicontinuousAt
#align continuous.lower_semicontinuous Continuous.lowerSemicontinuous

end

/-! ### Composition -/


section

variable {γ : Type _} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

variable {δ : Type _} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]

/- warning: continuous_at.comp_lower_semicontinuous_within_at -> ContinuousAt.comp_lowerSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s x) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_lower_semicontinuous_within_at ContinuousAt.comp_lowerSemicontinuousWithinAtₓ'. -/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  by
  intro y hy
  by_cases h : ∃ l, l < f x
  · obtain ⟨z, zlt, hz⟩ : ∃ z < f x, Ioc z (f x) ⊆ g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt]with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha, le_refl])
      _ ≤ g (f a) := gmon (min_le_right _ _)
      
  · simp only [not_exists, not_lt] at h
    exact Filter.eventually_of_forall fun a => hy.trans_le (gmon (h (f a)))
#align continuous_at.comp_lower_semicontinuous_within_at ContinuousAt.comp_lowerSemicontinuousWithinAt

/- warning: continuous_at.comp_lower_semicontinuous_at -> ContinuousAt.comp_lowerSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f x) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_lower_semicontinuous_at ContinuousAt.comp_lowerSemicontinuousAtₓ'. -/
theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x :=
  by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf⊢
  exact hg.comp_lower_semicontinuous_within_at hf gmon
#align continuous_at.comp_lower_semicontinuous_at ContinuousAt.comp_lowerSemicontinuousAt

/- warning: continuous.comp_lower_semicontinuous_on -> Continuous.comp_lowerSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous.comp_lower_semicontinuous_on Continuous.comp_lowerSemicontinuousOnₓ'. -/
theorem Continuous.comp_lowerSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.ContinuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon
#align continuous.comp_lower_semicontinuous_on Continuous.comp_lowerSemicontinuousOn

/- warning: continuous.comp_lower_semicontinuous -> Continuous.comp_lowerSemicontinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuous.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f))
Case conversion may be inaccurate. Consider using '#align continuous.comp_lower_semicontinuous Continuous.comp_lowerSemicontinuousₓ'. -/
theorem Continuous.comp_lowerSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_lowerSemicontinuousAt (hf x) gmon
#align continuous.comp_lower_semicontinuous Continuous.comp_lowerSemicontinuous

/- warning: continuous_at.comp_lower_semicontinuous_within_at_antitone -> ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s x) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_lower_semicontinuous_within_at_antitone ContinuousAt.comp_lowerSemicontinuousWithinAt_antitoneₓ'. -/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_lower_semicontinuous_within_at_antitone ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone

/- warning: continuous_at.comp_lower_semicontinuous_at_antitone -> ContinuousAt.comp_lowerSemicontinuousAt_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f x) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_lower_semicontinuous_at_antitone ContinuousAt.comp_lowerSemicontinuousAt_antitoneₓ'. -/
theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_lower_semicontinuous_at_antitone ContinuousAt.comp_lowerSemicontinuousAt_antitone

/- warning: continuous.comp_lower_semicontinuous_on_antitone -> Continuous.comp_lowerSemicontinuousOn_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous.comp_lower_semicontinuous_on_antitone Continuous.comp_lowerSemicontinuousOn_antitoneₓ'. -/
theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon
#align continuous.comp_lower_semicontinuous_on_antitone Continuous.comp_lowerSemicontinuousOn_antitone

/- warning: continuous.comp_lower_semicontinuous_antitone -> Continuous.comp_lowerSemicontinuous_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (LowerSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuous.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f))
Case conversion may be inaccurate. Consider using '#align continuous.comp_lower_semicontinuous_antitone Continuous.comp_lowerSemicontinuous_antitoneₓ'. -/
theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon
#align continuous.comp_lower_semicontinuous_antitone Continuous.comp_lowerSemicontinuous_antitone

end

/-! #### Addition -/


section

variable {ι : Type _} {γ : Type _} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ]
  [OrderTopology γ]

/- warning: lower_semicontinuous_within_at.add' -> LowerSemicontinuousWithinAt.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s x) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s x) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s x) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s x) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at.add' LowerSemicontinuousWithinAt.add'ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousWithinAt.add' {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    ∃ u v : Set γ,
      IsOpen u ∧ f x ∈ u ∧ IsOpen v ∧ g x ∈ v ∧ u ×ˢ v ⊆ { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (is_open_Ioi.mem_nhds hy))
  by_cases hx₁ : ∃ l, l < f x
  · obtain ⟨z₁, z₁lt, h₁⟩ : ∃ z₁ < f x, Ioc z₁ (f x) ⊆ u :=
      exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt]with z h₁z h₂z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases H : f z ≤ f x
        · simp [H]
          exact h₁ ⟨h₁z, H⟩
        · simp [le_of_not_le H]
          exact h₁ ⟨z₁lt, le_rfl⟩
      have A2 : min (g z) (g x) ∈ v := by
        by_cases H : g z ≤ g x
        · simp [H]
          exact h₂ ⟨h₂z, H⟩
        · simp [le_of_not_le H]
          exact h₂ ⟨z₂lt, le_rfl⟩
      have : (min (f z) (f x), min (g z) (g x)) ∈ u ×ˢ v := ⟨A1, A2⟩
      calc
        y < min (f z) (f x) + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (min_le_left _ _)
        
    · simp only [not_exists, not_lt] at hx₂
      filter_upwards [hf z₁ z₁lt]with z h₁z
      have A1 : min (f z) (f x) ∈ u := by
        by_cases H : f z ≤ f x
        · simp [H]
          exact h₁ ⟨h₁z, H⟩
        · simp [le_of_not_le H]
          exact h₁ ⟨z₁lt, le_rfl⟩
      have : (min (f z) (f x), g x) ∈ u ×ˢ v := ⟨A1, xv⟩
      calc
        y < min (f z) (f x) + g x := h this
        _ ≤ f z + g z := add_le_add (min_le_left _ _) (hx₂ (g z))
        
  · simp only [not_exists, not_lt] at hx₁
    by_cases hx₂ : ∃ l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : ∃ z₂ < g x, Ioc z₂ (g x) ⊆ v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hg z₂ z₂lt]with z h₂z
      have A2 : min (g z) (g x) ∈ v := by
        by_cases H : g z ≤ g x
        · simp [H]
          exact h₂ ⟨h₂z, H⟩
        · simp [le_of_not_le H]
          exact h₂ ⟨z₂lt, le_rfl⟩
      have : (f x, min (g z) (g x)) ∈ u ×ˢ v := ⟨xu, A2⟩
      calc
        y < f x + min (g z) (g x) := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (min_le_left _ _)
        
    · simp only [not_exists, not_lt] at hx₁ hx₂
      apply Filter.eventually_of_forall
      intro z
      have : (f x, g x) ∈ u ×ˢ v := ⟨xu, xv⟩
      calc
        y < f x + g x := h this
        _ ≤ f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))
        
#align lower_semicontinuous_within_at.add' LowerSemicontinuousWithinAt.add'

/- warning: lower_semicontinuous_at.add' -> LowerSemicontinuousAt.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f x) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g x) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f x) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g x) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at.add' LowerSemicontinuousAt.add'ₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousAt.add' {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousAt (fun z => f z + g z) x :=
  by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont
#align lower_semicontinuous_at.add' LowerSemicontinuousAt.add'

/- warning: lower_semicontinuous_on.add' -> LowerSemicontinuousOn.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x)))) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x)))) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on.add' LowerSemicontinuousOn.add'ₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuousOn.add' {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)
#align lower_semicontinuous_on.add' LowerSemicontinuousOn.add'

/- warning: lower_semicontinuous.add' -> LowerSemicontinuous.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g) -> (forall (x : α), ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g) -> (forall (x : α), ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.add' LowerSemicontinuous.add'ₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem LowerSemicontinuous.add' {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)
#align lower_semicontinuous.add' LowerSemicontinuous.add'

variable [ContinuousAdd γ]

/- warning: lower_semicontinuous_within_at.add -> LowerSemicontinuousWithinAt.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s x) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s x) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s x) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s x) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at.add LowerSemicontinuousWithinAt.addₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousWithinAt.add {f g : α → γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.ContinuousAt
#align lower_semicontinuous_within_at.add LowerSemicontinuousWithinAt.add

/- warning: lower_semicontinuous_at.add -> LowerSemicontinuousAt.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f x) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g x) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f x) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g x) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at.add LowerSemicontinuousAt.addₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousAt.add {f g : α → γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.ContinuousAt
#align lower_semicontinuous_at.add LowerSemicontinuousAt.add

/- warning: lower_semicontinuous_on.add -> LowerSemicontinuousOn.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on.add LowerSemicontinuousOn.addₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuousOn.add {f g : α → γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt
#align lower_semicontinuous_on.add LowerSemicontinuousOn.add

/- warning: lower_semicontinuous.add -> LowerSemicontinuous.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g) -> (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous.add LowerSemicontinuous.addₓ'. -/
/-- The sum of two lower semicontinuous functions is lower semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem LowerSemicontinuous.add {f g : α → γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt
#align lower_semicontinuous.add LowerSemicontinuous.add

/- warning: lower_semicontinuous_within_at_sum -> lowerSemicontinuousWithinAt_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) s x)) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) s x)) -> (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_sum lowerSemicontinuousWithinAt_sumₓ'. -/
theorem lowerSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x := by
  classical
    induction' a using Finset.induction_on with i a ia IH generalizing ha
    · exact lowerSemicontinuousWithinAt_const
    · simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self i a))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))
#align lower_semicontinuous_within_at_sum lowerSemicontinuousWithinAt_sum

/- warning: lower_semicontinuous_at_sum -> lowerSemicontinuousAt_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) x)) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) x)) -> (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_sum lowerSemicontinuousAt_sumₓ'. -/
theorem lowerSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i in a, f i z) x :=
  by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha
#align lower_semicontinuous_at_sum lowerSemicontinuousAt_sum

/- warning: lower_semicontinuous_on_sum -> lowerSemicontinuousOn_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) s)) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) s)) -> (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_sum lowerSemicontinuousOn_sumₓ'. -/
theorem lowerSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
#align lower_semicontinuous_on_sum lowerSemicontinuousOn_sum

/- warning: lower_semicontinuous_sum -> lowerSemicontinuous_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (LowerSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i))) -> (LowerSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i))) -> (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_sum lowerSemicontinuous_sumₓ'. -/
theorem lowerSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i in a, f i z :=
  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x
#align lower_semicontinuous_sum lowerSemicontinuous_sum

end

/-! #### Supremum -/


section

variable {ι : Sort _} {δ δ' : Type _} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/- warning: lower_semicontinuous_within_at_csupr -> lowerSemicontinuousWithinAt_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u1} α (fun (y : α) => BddAbove.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i y))) (nhdsWithin.{u1} α _inst_1 x s)) -> (forall (i : ι), LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iSup.{u3, u2} δ' (ConditionallyCompleteLattice.toHasSup.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u3} α (fun (y : α) => BddAbove.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i y))) (nhdsWithin.{u3} α _inst_1 x s)) -> (forall (i : ι), LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iSup.{u2, u1} δ' (ConditionallyCompleteLattice.toSupSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_csupr lowerSemicontinuousWithinAt_ciSupₓ'. -/
theorem lowerSemicontinuousWithinAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y))
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd]with y hy hy' using hy.trans_le (le_ciSup hy' i)
#align lower_semicontinuous_within_at_csupr lowerSemicontinuousWithinAt_ciSup

/- warning: lower_semicontinuous_within_at_supr -> lowerSemicontinuousWithinAt_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_supr lowerSemicontinuousWithinAt_iSupₓ'. -/
theorem lowerSemicontinuousWithinAt_iSup {f : ι → α → δ}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (by simp) h
#align lower_semicontinuous_within_at_supr lowerSemicontinuousWithinAt_iSup

/- warning: lower_semicontinuous_within_at_bsupr -> lowerSemicontinuousWithinAt_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) s x) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iSup.{u3, 0} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) s x) -> (LowerSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iSup.{u2, 0} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_bsupr lowerSemicontinuousWithinAt_biSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem lowerSemicontinuousWithinAt_biSup {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi
#align lower_semicontinuous_within_at_bsupr lowerSemicontinuousWithinAt_biSup

/- warning: lower_semicontinuous_at_csupr -> lowerSemicontinuousAt_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u1} α (fun (y : α) => BddAbove.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i y))) (nhds.{u1} α _inst_1 x)) -> (forall (i : ι), LowerSemicontinuousAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) x) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iSup.{u3, u2} δ' (ConditionallyCompleteLattice.toHasSup.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u3} α (fun (y : α) => BddAbove.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i y))) (nhds.{u3} α _inst_1 x)) -> (forall (i : ι), LowerSemicontinuousAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) x) -> (LowerSemicontinuousAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iSup.{u2, u1} δ' (ConditionallyCompleteLattice.toSupSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_csupr lowerSemicontinuousAt_ciSupₓ'. -/
theorem lowerSemicontinuousAt_ciSup {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h
#align lower_semicontinuous_at_csupr lowerSemicontinuousAt_ciSup

/- warning: lower_semicontinuous_at_supr -> lowerSemicontinuousAt_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) x) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) x) -> (LowerSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_supr lowerSemicontinuousAt_iSupₓ'. -/
theorem lowerSemicontinuousAt_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  lowerSemicontinuousAt_ciSup (by simp) h
#align lower_semicontinuous_at_supr lowerSemicontinuousAt_iSup

/- warning: lower_semicontinuous_at_bsupr -> lowerSemicontinuousAt_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) x) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iSup.{u3, 0} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) x) -> (LowerSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iSup.{u2, 0} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_bsupr lowerSemicontinuousAt_biSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem lowerSemicontinuousAt_biSup {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousAt (f i hi) x) :
    LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi
#align lower_semicontinuous_at_bsupr lowerSemicontinuousAt_biSup

/- warning: lower_semicontinuous_on_csupr -> lowerSemicontinuousOn_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (BddAbove.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x)))) -> (forall (i : ι), LowerSemicontinuousOn.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) s) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iSup.{u3, u2} δ' (ConditionallyCompleteLattice.toHasSup.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) -> (BddAbove.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i x)))) -> (forall (i : ι), LowerSemicontinuousOn.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) s) -> (LowerSemicontinuousOn.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iSup.{u2, u1} δ' (ConditionallyCompleteLattice.toSupSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_csupr lowerSemicontinuousOn_ciSupₓ'. -/
theorem lowerSemicontinuousOn_ciSup {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddAbove (range fun i => f i x)) (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
#align lower_semicontinuous_on_csupr lowerSemicontinuousOn_ciSup

/- warning: lower_semicontinuous_on_supr -> lowerSemicontinuousOn_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) s) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) s) -> (LowerSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_supr lowerSemicontinuousOn_iSupₓ'. -/
theorem lowerSemicontinuousOn_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s :=
  lowerSemicontinuousOn_ciSup (by simp) h
#align lower_semicontinuous_on_supr lowerSemicontinuousOn_iSup

/- warning: lower_semicontinuous_on_bsupr -> lowerSemicontinuousOn_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) s) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iSup.{u3, 0} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) s) -> (LowerSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iSup.{u2, 0} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_bsupr lowerSemicontinuousOn_biSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem lowerSemicontinuousOn_biSup {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuousOn (f i hi) s) :
    LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi
#align lower_semicontinuous_on_bsupr lowerSemicontinuousOn_biSup

/- warning: lower_semicontinuous_csupr -> lowerSemicontinuous_ciSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), BddAbove.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x))) -> (forall (i : ι), LowerSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i)) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iSup.{u3, u2} δ' (ConditionallyCompleteLattice.toHasSup.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), BddAbove.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x))) -> (forall (i : ι), LowerSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i)) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iSup.{u3, u2} δ' (ConditionallyCompleteLattice.toSupSet.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_csupr lowerSemicontinuous_ciSupₓ'. -/
theorem lowerSemicontinuous_ciSup {f : ι → α → δ'} (bdd : ∀ x, BddAbove (range fun i => f i x))
    (h : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x =>
  lowerSemicontinuousAt_ciSup (eventually_of_forall bdd) fun i => h i x
#align lower_semicontinuous_csupr lowerSemicontinuous_ciSup

/- warning: lower_semicontinuous_supr -> lowerSemicontinuous_iSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i)) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), LowerSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i)) -> (LowerSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_supr lowerSemicontinuous_iSupₓ'. -/
theorem lowerSemicontinuous_iSup {f : ι → α → δ} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' :=
  lowerSemicontinuous_ciSup (by simp) h
#align lower_semicontinuous_supr lowerSemicontinuous_iSup

/- warning: lower_semicontinuous_bsupr -> lowerSemicontinuous_biSup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi)) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iSup.{u3, u2} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iSup.{u3, 0} δ (ConditionallyCompleteLattice.toHasSup.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), LowerSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi)) -> (LowerSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iSup.{u2, u1} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iSup.{u2, 0} δ (ConditionallyCompleteLattice.toSupSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_bsupr lowerSemicontinuous_biSupₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem lowerSemicontinuous_biSup {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, LowerSemicontinuous (f i hi)) :
    LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi
#align lower_semicontinuous_bsupr lowerSemicontinuous_biSup

end

/-! #### Infinite sums -/


section

variable {ι : Type _}

/- warning: lower_semicontinuous_within_at_tsum -> lowerSemicontinuousWithinAt_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Type.{u2}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousWithinAt.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (fun (x' : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => f i x')) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {ι : Type.{u1}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousWithinAt.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (f i) s x) -> (LowerSemicontinuousWithinAt.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (fun (x' : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => f i x')) s x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_within_at_tsum lowerSemicontinuousWithinAt_tsumₓ'. -/
theorem lowerSemicontinuousWithinAt_tsum {f : ι → α → ℝ≥0∞}
    (h : ∀ i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ∑' i, f i x') s x :=
  by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  apply lowerSemicontinuousWithinAt_iSup fun b => _
  exact lowerSemicontinuousWithinAt_sum fun i hi => h i
#align lower_semicontinuous_within_at_tsum lowerSemicontinuousWithinAt_tsum

/- warning: lower_semicontinuous_at_tsum -> lowerSemicontinuousAt_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Type.{u2}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousAt.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (f i) x) -> (LowerSemicontinuousAt.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (fun (x' : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => f i x')) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {ι : Type.{u1}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousAt.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (f i) x) -> (LowerSemicontinuousAt.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (fun (x' : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => f i x')) x)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_at_tsum lowerSemicontinuousAt_tsumₓ'. -/
theorem lowerSemicontinuousAt_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x :=
  by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h
#align lower_semicontinuous_at_tsum lowerSemicontinuousAt_tsum

/- warning: lower_semicontinuous_on_tsum -> lowerSemicontinuousOn_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Type.{u2}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousOn.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (f i) s) -> (LowerSemicontinuousOn.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (fun (x' : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => f i x')) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {ι : Type.{u1}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuousOn.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (f i) s) -> (LowerSemicontinuousOn.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (fun (x' : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => f i x')) s)
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_on_tsum lowerSemicontinuousOn_tsumₓ'. -/
theorem lowerSemicontinuousOn_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx
#align lower_semicontinuous_on_tsum lowerSemicontinuousOn_tsum

/- warning: lower_semicontinuous_tsum -> lowerSemicontinuous_tsum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuous.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (f i)) -> (LowerSemicontinuous.{u1, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedAddCommMonoid.toPartialOrder.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))) (fun (x' : α) => tsum.{0, u2} ENNReal (OrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (OrderedSemiring.toOrderedAddCommMonoid.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))) ENNReal.topologicalSpace ι (fun (i : ι) => f i x')))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u1}} {f : ι -> α -> ENNReal}, (forall (i : ι), LowerSemicontinuous.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (f i)) -> (LowerSemicontinuous.{u2, 0} α _inst_1 ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (fun (x' : α) => tsum.{0, u1} ENNReal (LinearOrderedAddCommMonoid.toAddCommMonoid.{0} ENNReal (LinearOrderedAddCommMonoidWithTop.toLinearOrderedAddCommMonoid.{0} ENNReal ENNReal.instLinearOrderedAddCommMonoidWithTopENNReal)) ENNReal.instTopologicalSpaceENNReal ι (fun (i : ι) => f i x')))
Case conversion may be inaccurate. Consider using '#align lower_semicontinuous_tsum lowerSemicontinuous_tsumₓ'. -/
theorem lowerSemicontinuous_tsum {f : ι → α → ℝ≥0∞} (h : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lowerSemicontinuousAt_tsum fun i => h i x
#align lower_semicontinuous_tsum lowerSemicontinuous_tsum

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


/- warning: upper_semicontinuous_within_at.mono -> UpperSemicontinuousWithinAt.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α} {t : Set.{u1} α}, (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α} {t : Set.{u2} α}, (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t s) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f t x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at.mono UpperSemicontinuousWithinAt.monoₓ'. -/
theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
#align upper_semicontinuous_within_at.mono UpperSemicontinuousWithinAt.mono

/- warning: upper_semicontinuous_within_at_univ_iff -> upperSemicontinuousWithinAt_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α}, Iff (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f (Set.univ.{u1} α) x) (UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α}, Iff (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f (Set.univ.{u2} α) x) (UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_univ_iff upperSemicontinuousWithinAt_univ_iffₓ'. -/
theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x := by
  simp [UpperSemicontinuousWithinAt, UpperSemicontinuousAt, nhdsWithin_univ]
#align upper_semicontinuous_within_at_univ_iff upperSemicontinuousWithinAt_univ_iff

/- warning: upper_semicontinuous_at.upper_semicontinuous_within_at -> UpperSemicontinuousAt.upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} (s : Set.{u1} α), (UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} (s : Set.{u2} α), (UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at.upper_semicontinuous_within_at UpperSemicontinuousAt.upperSemicontinuousWithinAtₓ'. -/
theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
#align upper_semicontinuous_at.upper_semicontinuous_within_at UpperSemicontinuousAt.upperSemicontinuousWithinAt

/- warning: upper_semicontinuous_on.upper_semicontinuous_within_at -> UpperSemicontinuousOn.upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {x : α} {s : Set.{u1} α}, (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {x : α} {s : Set.{u2} α}, (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on.upper_semicontinuous_within_at UpperSemicontinuousOn.upperSemicontinuousWithinAtₓ'. -/
theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x ∈ s) : UpperSemicontinuousWithinAt f s x :=
  h x hx
#align upper_semicontinuous_on.upper_semicontinuous_within_at UpperSemicontinuousOn.upperSemicontinuousWithinAt

/- warning: upper_semicontinuous_on.mono -> UpperSemicontinuousOn.mono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β} {s : Set.{u1} α} {t : Set.{u1} α}, (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s) -> (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) t s) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β} {s : Set.{u2} α} {t : Set.{u2} α}, (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s) -> (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) t s) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f t)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on.mono UpperSemicontinuousOn.monoₓ'. -/
theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
    UpperSemicontinuousOn f t := fun x hx => (h x (hst hx)).mono hst
#align upper_semicontinuous_on.mono UpperSemicontinuousOn.mono

/- warning: upper_semicontinuous_on_univ_iff -> upperSemicontinuousOn_univ_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, Iff (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f (Set.univ.{u1} α)) (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, Iff (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f (Set.univ.{u2} α)) (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_univ_iff upperSemicontinuousOn_univ_iffₓ'. -/
theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f := by
  simp [UpperSemicontinuousOn, UpperSemicontinuous, upperSemicontinuousWithinAt_univ_iff]
#align upper_semicontinuous_on_univ_iff upperSemicontinuousOn_univ_iff

/- warning: upper_semicontinuous.upper_semicontinuous_at -> UpperSemicontinuous.upperSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (x : α), UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (x : α), UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 f x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.upper_semicontinuous_at UpperSemicontinuous.upperSemicontinuousAtₓ'. -/
theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x
#align upper_semicontinuous.upper_semicontinuous_at UpperSemicontinuous.upperSemicontinuousAt

/- warning: upper_semicontinuous.upper_semicontinuous_within_at -> UpperSemicontinuous.upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u1} α) (x : α), UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u2} α) (x : α), UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 f s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.upper_semicontinuous_within_at UpperSemicontinuous.upperSemicontinuousWithinAtₓ'. -/
theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).UpperSemicontinuousWithinAt s
#align upper_semicontinuous.upper_semicontinuous_within_at UpperSemicontinuous.upperSemicontinuousWithinAt

/- warning: upper_semicontinuous.upper_semicontinuous_on -> UpperSemicontinuous.upperSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u1} α), UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 f s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (s : Set.{u2} α), UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 f s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.upper_semicontinuous_on UpperSemicontinuous.upperSemicontinuousOnₓ'. -/
theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s := fun x hx => h.UpperSemicontinuousWithinAt s x
#align upper_semicontinuous.upper_semicontinuous_on UpperSemicontinuous.upperSemicontinuousOn

/-! #### Constants -/


/- warning: upper_semicontinuous_within_at_const -> upperSemicontinuousWithinAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {z : β}, UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) s x
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {z : β}, UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) s x
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_const upperSemicontinuousWithinAt_constₓ'. -/
theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun x => z) s x :=
  fun y hy => Filter.eventually_of_forall fun x => hy
#align upper_semicontinuous_within_at_const upperSemicontinuousWithinAt_const

/- warning: upper_semicontinuous_at_const -> upperSemicontinuousAt_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {z : β}, UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) x
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {z : β}, UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) x
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at_const upperSemicontinuousAt_constₓ'. -/
theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun x => z) x := fun y hy =>
  Filter.eventually_of_forall fun x => hy
#align upper_semicontinuous_at_const upperSemicontinuousAt_const

/- warning: upper_semicontinuous_on_const -> upperSemicontinuousOn_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {z : β}, UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z) s
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {z : β}, UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z) s
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_const upperSemicontinuousOn_constₓ'. -/
theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun x => z) s := fun x hx =>
  upperSemicontinuousWithinAt_const
#align upper_semicontinuous_on_const upperSemicontinuousOn_const

/- warning: upper_semicontinuous_const -> upperSemicontinuous_const is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {z : β}, UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (fun (x : α) => z)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {z : β}, UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (fun (x : α) => z)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_const upperSemicontinuous_constₓ'. -/
theorem upperSemicontinuous_const : UpperSemicontinuous fun x : α => z := fun x =>
  upperSemicontinuousAt_const
#align upper_semicontinuous_const upperSemicontinuous_const

/-! #### Indicators -/


section

variable [Zero β]

/- warning: is_open.upper_semicontinuous_indicator -> IsOpen.upperSemicontinuous_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)))
Case conversion may be inaccurate. Consider using '#align is_open.upper_semicontinuous_indicator IsOpen.upperSemicontinuous_indicatorₓ'. -/
theorem IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuous (indicator s fun x => y) :=
  @IsOpen.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy
#align is_open.upper_semicontinuous_indicator IsOpen.upperSemicontinuous_indicator

/- warning: is_open.upper_semicontinuous_on_indicator -> IsOpen.upperSemicontinuousOn_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t)
Case conversion may be inaccurate. Consider using '#align is_open.upper_semicontinuous_on_indicator IsOpen.upperSemicontinuousOn_indicatorₓ'. -/
theorem IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousOn (indicator s fun x => y) t :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousOn t
#align is_open.upper_semicontinuous_on_indicator IsOpen.upperSemicontinuousOn_indicator

/- warning: is_open.upper_semicontinuous_at_indicator -> IsOpen.upperSemicontinuousAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) x)
Case conversion may be inaccurate. Consider using '#align is_open.upper_semicontinuous_at_indicator IsOpen.upperSemicontinuousAt_indicatorₓ'. -/
theorem IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousAt (indicator s fun x => y) x :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousAt x
#align is_open.upper_semicontinuous_at_indicator IsOpen.upperSemicontinuousAt_indicator

/- warning: is_open.upper_semicontinuous_within_at_indicator -> IsOpen.upperSemicontinuousWithinAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsOpen.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) y (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3)))) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsOpen.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) y (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3))) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t x)
Case conversion may be inaccurate. Consider using '#align is_open.upper_semicontinuous_within_at_indicator IsOpen.upperSemicontinuousWithinAt_indicatorₓ'. -/
theorem IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y ≤ 0) :
    UpperSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousWithinAt t x
#align is_open.upper_semicontinuous_within_at_indicator IsOpen.upperSemicontinuousWithinAt_indicator

/- warning: is_closed.upper_semicontinuous_indicator -> IsClosed.upperSemicontinuous_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)))
Case conversion may be inaccurate. Consider using '#align is_closed.upper_semicontinuous_indicator IsClosed.upperSemicontinuous_indicatorₓ'. -/
theorem IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuous (indicator s fun x => y) :=
  @IsClosed.lowerSemicontinuous_indicator α _ βᵒᵈ _ s y _ hs hy
#align is_closed.upper_semicontinuous_indicator IsClosed.upperSemicontinuous_indicator

/- warning: is_closed.upper_semicontinuous_on_indicator -> IsClosed.upperSemicontinuousOn_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t)
Case conversion may be inaccurate. Consider using '#align is_closed.upper_semicontinuous_on_indicator IsClosed.upperSemicontinuousOn_indicatorₓ'. -/
theorem IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousOn (indicator s fun x => y) t :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousOn t
#align is_closed.upper_semicontinuous_on_indicator IsClosed.upperSemicontinuousOn_indicator

/- warning: is_closed.upper_semicontinuous_at_indicator -> IsClosed.upperSemicontinuousAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) x)
Case conversion may be inaccurate. Consider using '#align is_closed.upper_semicontinuous_at_indicator IsClosed.upperSemicontinuousAt_indicatorₓ'. -/
theorem IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousAt (indicator s fun x => y) x :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousAt x
#align is_closed.upper_semicontinuous_at_indicator IsClosed.upperSemicontinuousAt_indicator

/- warning: is_closed.upper_semicontinuous_within_at_indicator -> IsClosed.upperSemicontinuousWithinAt_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {x : α} {s : Set.{u1} α} {t : Set.{u1} α} {y : β} [_inst_3 : Zero.{u2} β], (IsClosed.{u1} α _inst_1 s) -> (LE.le.{u2} β (Preorder.toHasLe.{u2} β _inst_2) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_3))) y) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 β _inst_2 (Set.indicator.{u1, u2} α β _inst_3 s (fun (x : α) => y)) t x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {x : α} {s : Set.{u2} α} {t : Set.{u2} α} {y : β} [_inst_3 : Zero.{u1} β], (IsClosed.{u2} α _inst_1 s) -> (LE.le.{u1} β (Preorder.toLE.{u1} β _inst_2) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_3)) y) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 β _inst_2 (Set.indicator.{u2, u1} α β _inst_3 s (fun (x : α) => y)) t x)
Case conversion may be inaccurate. Consider using '#align is_closed.upper_semicontinuous_within_at_indicator IsClosed.upperSemicontinuousWithinAt_indicatorₓ'. -/
theorem IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 ≤ y) :
    UpperSemicontinuousWithinAt (indicator s fun x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).UpperSemicontinuousWithinAt t x
#align is_closed.upper_semicontinuous_within_at_indicator IsClosed.upperSemicontinuousWithinAt_indicator

end

/-! #### Relationship with continuity -/


/- warning: upper_semicontinuous_iff_is_open_preimage -> upperSemicontinuous_iff_isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, Iff (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) (forall (y : β), IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f (Set.Iio.{u2} β _inst_2 y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, Iff (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) (forall (y : β), IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f (Set.Iio.{u1} β _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_iff_is_open_preimage upperSemicontinuous_iff_isOpen_preimageₓ'. -/
theorem upperSemicontinuous_iff_isOpen_preimage :
    UpperSemicontinuous f ↔ ∀ y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩
#align upper_semicontinuous_iff_is_open_preimage upperSemicontinuous_iff_isOpen_preimage

/- warning: upper_semicontinuous.is_open_preimage -> UpperSemicontinuous.isOpen_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {β : Type.{u2}} [_inst_2 : Preorder.{u2} β] {f : α -> β}, (UpperSemicontinuous.{u1, u2} α _inst_1 β _inst_2 f) -> (forall (y : β), IsOpen.{u1} α _inst_1 (Set.preimage.{u1, u2} α β f (Set.Iio.{u2} β _inst_2 y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {β : Type.{u1}} [_inst_2 : Preorder.{u1} β] {f : α -> β}, (UpperSemicontinuous.{u2, u1} α _inst_1 β _inst_2 f) -> (forall (y : β), IsOpen.{u2} α _inst_1 (Set.preimage.{u2, u1} α β f (Set.Iio.{u1} β _inst_2 y)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.is_open_preimage UpperSemicontinuous.isOpen_preimageₓ'. -/
theorem UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Iio y) :=
  upperSemicontinuous_iff_isOpen_preimage.1 hf y
#align upper_semicontinuous.is_open_preimage UpperSemicontinuous.isOpen_preimage

section

variable {γ : Type _} [LinearOrder γ]

/- warning: upper_semicontinuous_iff_is_closed_preimage -> upperSemicontinuous_iff_isClosed_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] {f : α -> γ}, Iff (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) (forall (y : γ), IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α γ f (Set.Ici.{u2} γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] {f : α -> γ}, Iff (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f) (forall (y : γ), IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α γ f (Set.Ici.{u1} γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) y)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_iff_is_closed_preimage upperSemicontinuous_iff_isClosed_preimageₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ y, (_ : exprProp())]] -/
theorem upperSemicontinuous_iff_isClosed_preimage {f : α → γ} :
    UpperSemicontinuous f ↔ ∀ y, IsClosed (f ⁻¹' Ici y) :=
  by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  trace
    "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:73:14: unsupported tactic `congrm #[[expr ∀ y, (_ : exprProp())]]"
  rw [← isOpen_compl_iff, ← preimage_compl, compl_Ici]
#align upper_semicontinuous_iff_is_closed_preimage upperSemicontinuous_iff_isClosed_preimage

/- warning: upper_semicontinuous.is_closed_preimage -> UpperSemicontinuous.isClosed_preimage is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] {f : α -> γ}, (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (forall (y : γ), IsClosed.{u1} α _inst_1 (Set.preimage.{u1, u2} α γ f (Set.Ici.{u2} γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) y)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] {f : α -> γ}, (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f) -> (forall (y : γ), IsClosed.{u2} α _inst_1 (Set.preimage.{u2, u1} α γ f (Set.Ici.{u1} γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) y)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.is_closed_preimage UpperSemicontinuous.isClosed_preimageₓ'. -/
theorem UpperSemicontinuous.isClosed_preimage {f : α → γ} (hf : UpperSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Ici y) :=
  upperSemicontinuous_iff_isClosed_preimage.1 hf y
#align upper_semicontinuous.is_closed_preimage UpperSemicontinuous.isClosed_preimage

variable [TopologicalSpace γ] [OrderTopology γ]

/- warning: continuous_within_at.upper_semicontinuous_within_at -> ContinuousWithinAt.upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_4 f s x) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousWithinAt.{u2, u1} α γ _inst_1 _inst_4 f s x) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s x)
Case conversion may be inaccurate. Consider using '#align continuous_within_at.upper_semicontinuous_within_at ContinuousWithinAt.upperSemicontinuousWithinAtₓ'. -/
theorem ContinuousWithinAt.upperSemicontinuousWithinAt {f : α → γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun y hy => h (Iio_mem_nhds hy)
#align continuous_within_at.upper_semicontinuous_within_at ContinuousWithinAt.upperSemicontinuousWithinAt

/- warning: continuous_at.upper_semicontinuous_at -> ContinuousAt.upperSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousAt.{u1, u2} α γ _inst_1 _inst_4 f x) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousAt.{u2, u1} α γ _inst_1 _inst_4 f x) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f x)
Case conversion may be inaccurate. Consider using '#align continuous_at.upper_semicontinuous_at ContinuousAt.upperSemicontinuousAtₓ'. -/
theorem ContinuousAt.upperSemicontinuousAt {f : α → γ} (h : ContinuousAt f x) :
    UpperSemicontinuousAt f x := fun y hy => h (Iio_mem_nhds hy)
#align continuous_at.upper_semicontinuous_at ContinuousAt.upperSemicontinuousAt

/- warning: continuous_on.upper_semicontinuous_on -> ContinuousOn.upperSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (ContinuousOn.{u1, u2} α γ _inst_1 _inst_4 f s) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (ContinuousOn.{u2, u1} α γ _inst_1 _inst_4 f s) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s)
Case conversion may be inaccurate. Consider using '#align continuous_on.upper_semicontinuous_on ContinuousOn.upperSemicontinuousOnₓ'. -/
theorem ContinuousOn.upperSemicontinuousOn {f : α → γ} (h : ContinuousOn f s) :
    UpperSemicontinuousOn f s := fun x hx => (h x hx).UpperSemicontinuousWithinAt
#align continuous_on.upper_semicontinuous_on ContinuousOn.upperSemicontinuousOn

/- warning: continuous.upper_semicontinuous -> Continuous.upperSemicontinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, (Continuous.{u1, u2} α γ _inst_1 _inst_4 f) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, (Continuous.{u2, u1} α γ _inst_1 _inst_4 f) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f)
Case conversion may be inaccurate. Consider using '#align continuous.upper_semicontinuous Continuous.upperSemicontinuousₓ'. -/
theorem Continuous.upperSemicontinuous {f : α → γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun x => h.ContinuousAt.UpperSemicontinuousAt
#align continuous.upper_semicontinuous Continuous.upperSemicontinuous

end

/-! ### Composition -/


section

variable {γ : Type _} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

variable {δ : Type _} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]

/- warning: continuous_at.comp_upper_semicontinuous_within_at -> ContinuousAt.comp_upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s x) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_upper_semicontinuous_within_at ContinuousAt.comp_upperSemicontinuousWithinAtₓ'. -/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_lowerSemicontinuousWithinAt α _ x s γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual
#align continuous_at.comp_upper_semicontinuous_within_at ContinuousAt.comp_upperSemicontinuousWithinAt

/- warning: continuous_at.comp_upper_semicontinuous_at -> ContinuousAt.comp_upperSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f x) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_upper_semicontinuous_at ContinuousAt.comp_upperSemicontinuousAtₓ'. -/
theorem ContinuousAt.comp_upperSemicontinuousAt {g : γ → δ} {f : α → γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_lowerSemicontinuousAt α _ x γᵒᵈ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon.dual
#align continuous_at.comp_upper_semicontinuous_at ContinuousAt.comp_upperSemicontinuousAt

/- warning: continuous.comp_upper_semicontinuous_on -> Continuous.comp_upperSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous.comp_upper_semicontinuous_on Continuous.comp_upperSemicontinuousOnₓ'. -/
theorem Continuous.comp_upperSemicontinuousOn {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.ContinuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon
#align continuous.comp_upper_semicontinuous_on Continuous.comp_upperSemicontinuousOn

/- warning: continuous.comp_upper_semicontinuous -> Continuous.comp_upperSemicontinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (Monotone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f) -> (Monotone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (UpperSemicontinuous.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f))
Case conversion may be inaccurate. Consider using '#align continuous.comp_upper_semicontinuous Continuous.comp_upperSemicontinuousₓ'. -/
theorem Continuous.comp_upperSemicontinuous {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_upperSemicontinuousAt (hf x) gmon
#align continuous.comp_upper_semicontinuous Continuous.comp_upperSemicontinuous

/- warning: continuous_at.comp_upper_semicontinuous_within_at_antitone -> ContinuousAt.comp_upperSemicontinuousWithinAt_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s x) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_upper_semicontinuous_within_at_antitone ContinuousAt.comp_upperSemicontinuousWithinAt_antitoneₓ'. -/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  @ContinuousAt.comp_upperSemicontinuousWithinAt α _ x s γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_upper_semicontinuous_within_at_antitone ContinuousAt.comp_upperSemicontinuousWithinAt_antitone

/- warning: continuous_at.comp_upper_semicontinuous_at_antitone -> ContinuousAt.comp_upperSemicontinuousAt_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u2, u3} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) x)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (ContinuousAt.{u3, u2} γ δ _inst_4 _inst_7 g (f x)) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f x) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousAt.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) x)
Case conversion may be inaccurate. Consider using '#align continuous_at.comp_upper_semicontinuous_at_antitone ContinuousAt.comp_upperSemicontinuousAt_antitoneₓ'. -/
theorem ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ → δ} {f : α → γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) :
    LowerSemicontinuousAt (g ∘ f) x :=
  @ContinuousAt.comp_upperSemicontinuousAt α _ x γ _ _ _ δᵒᵈ _ _ _ g f hg hf gmon
#align continuous_at.comp_upper_semicontinuous_at_antitone ContinuousAt.comp_upperSemicontinuousAt_antitone

/- warning: continuous.comp_upper_semicontinuous_on_antitone -> Continuous.comp_upperSemicontinuousOn_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f) s)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f s) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuousOn.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f) s)
Case conversion may be inaccurate. Consider using '#align continuous.comp_upper_semicontinuous_on_antitone Continuous.comp_upperSemicontinuousOn_antitoneₓ'. -/
theorem Continuous.comp_upperSemicontinuousOn_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.ContinuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon
#align continuous.comp_upper_semicontinuous_on_antitone Continuous.comp_upperSemicontinuousOn_antitone

/- warning: continuous.comp_upper_semicontinuous_antitone -> Continuous.comp_upperSemicontinuous_antitone is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {δ : Type.{u3}} [_inst_6 : LinearOrder.{u3} δ] [_inst_7 : TopologicalSpace.{u3} δ] [_inst_8 : OrderTopology.{u3} δ _inst_7 (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u2, u3} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) -> (Antitone.{u2, u3} γ δ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) g) -> (LowerSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (SemilatticeInf.toPartialOrder.{u3} δ (Lattice.toSemilatticeInf.{u3} δ (LinearOrder.toLattice.{u3} δ _inst_6)))) (Function.comp.{succ u1, succ u2, succ u3} α γ δ g f))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u3}} [_inst_3 : LinearOrder.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3)))))] {δ : Type.{u2}} [_inst_6 : LinearOrder.{u2} δ] [_inst_7 : TopologicalSpace.{u2} δ] [_inst_8 : OrderTopology.{u2} δ _inst_7 (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6)))))] {g : γ -> δ} {f : α -> γ}, (Continuous.{u3, u2} γ δ _inst_4 _inst_7 g) -> (UpperSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) f) -> (Antitone.{u3, u2} γ δ (PartialOrder.toPreorder.{u3} γ (SemilatticeInf.toPartialOrder.{u3} γ (Lattice.toSemilatticeInf.{u3} γ (DistribLattice.toLattice.{u3} γ (instDistribLattice.{u3} γ _inst_3))))) (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) g) -> (LowerSemicontinuous.{u1, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (SemilatticeInf.toPartialOrder.{u2} δ (Lattice.toSemilatticeInf.{u2} δ (DistribLattice.toLattice.{u2} δ (instDistribLattice.{u2} δ _inst_6))))) (Function.comp.{succ u1, succ u3, succ u2} α γ δ g f))
Case conversion may be inaccurate. Consider using '#align continuous.comp_upper_semicontinuous_antitone Continuous.comp_upperSemicontinuous_antitoneₓ'. -/
theorem Continuous.comp_upperSemicontinuous_antitone {g : γ → δ} {f : α → γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.ContinuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon
#align continuous.comp_upper_semicontinuous_antitone Continuous.comp_upperSemicontinuous_antitone

end

/-! #### Addition -/


section

variable {ι : Type _} {γ : Type _} [LinearOrderedAddCommMonoid γ] [TopologicalSpace γ]
  [OrderTopology γ]

/- warning: upper_semicontinuous_within_at.add' -> UpperSemicontinuousWithinAt.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s x) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s x) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s x) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s x) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at.add' UpperSemicontinuousWithinAt.add'ₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousWithinAt.add' {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  @LowerSemicontinuousWithinAt.add' α _ x s γᵒᵈ _ _ _ _ _ hf hg hcont
#align upper_semicontinuous_within_at.add' UpperSemicontinuousWithinAt.add'

/- warning: upper_semicontinuous_at.add' -> UpperSemicontinuousAt.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f x) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g x) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f x) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g x) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at.add' UpperSemicontinuousAt.add'ₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousAt.add' {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousAt (fun z => f z + g z) x :=
  by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont
#align upper_semicontinuous_at.add' UpperSemicontinuousAt.add'

/- warning: upper_semicontinuous_on.add' -> UpperSemicontinuousOn.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s) -> (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x)))) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s) -> (forall (x : α), (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) x s) -> (ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x)))) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on.add' UpperSemicontinuousOn.add'ₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuousOn.add' {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s)
    (hcont : ∀ x ∈ s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  (hf x hx).add' (hg x hx) (hcont x hx)
#align upper_semicontinuous_on.add' UpperSemicontinuousOn.add'

/- warning: upper_semicontinuous.add' -> UpperSemicontinuous.add' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g) -> (forall (x : α), ContinuousAt.{u2, u2} (Prod.{u2, u2} γ γ) γ (Prod.topologicalSpace.{u2, u2} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u2, u2} γ γ) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (Prod.fst.{u2, u2} γ γ p) (Prod.snd.{u2, u2} γ γ p)) (Prod.mk.{u2, u2} γ γ (f x) (g x))) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g) -> (forall (x : α), ContinuousAt.{u1, u1} (Prod.{u1, u1} γ γ) γ (instTopologicalSpaceProd.{u1, u1} γ γ _inst_4 _inst_4) _inst_4 (fun (p : Prod.{u1, u1} γ γ) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (Prod.fst.{u1, u1} γ γ p) (Prod.snd.{u1, u1} γ γ p)) (Prod.mk.{u1, u1} γ γ (f x) (g x))) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.add' UpperSemicontinuous.add'ₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with an
explicit continuity assumption on addition, for application to `ereal`. The unprimed version of
the lemma uses `[has_continuous_add]`. -/
theorem UpperSemicontinuous.add' {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g)
    (hcont : ∀ x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuous fun z => f z + g z := fun x => (hf x).add' (hg x) (hcont x)
#align upper_semicontinuous.add' UpperSemicontinuous.add'

variable [ContinuousAdd γ]

/- warning: upper_semicontinuous_within_at.add -> UpperSemicontinuousWithinAt.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s x) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s x) -> (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s x) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s x) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at.add UpperSemicontinuousWithinAt.addₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousWithinAt.add {f g : α → γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.ContinuousAt
#align upper_semicontinuous_within_at.add UpperSemicontinuousWithinAt.add

/- warning: upper_semicontinuous_at.add -> UpperSemicontinuousAt.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f x) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g x) -> (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f x) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g x) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at.add UpperSemicontinuousAt.addₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousAt.add {f g : α → γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.ContinuousAt
#align upper_semicontinuous_at.add UpperSemicontinuousAt.add

/- warning: upper_semicontinuous_on.add -> UpperSemicontinuousOn.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f s) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g s) -> (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f s) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g s) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on.add UpperSemicontinuousOn.addₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuousOn.add {f g : α → γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun x hx => continuous_add.ContinuousAt
#align upper_semicontinuous_on.add UpperSemicontinuousOn.add

/- warning: upper_semicontinuous.add -> UpperSemicontinuous.add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrderedAddCommMonoid.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u2} γ _inst_4 (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) f) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) g) -> (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (OrderedAddCommMonoid.toPartialOrder.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u2, u2, u2} γ γ γ (instHAdd.{u2} γ (AddZeroClass.toHasAdd.{u2} γ (AddMonoid.toAddZeroClass.{u2} γ (AddCommMonoid.toAddMonoid.{u2} γ (OrderedAddCommMonoid.toAddCommMonoid.{u2} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u2} γ _inst_3)))))) (f z) (g z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : α -> γ} {g : α -> γ}, (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) f) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) g) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => HAdd.hAdd.{u1, u1, u1} γ γ γ (instHAdd.{u1} γ (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))) (f z) (g z)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous.add UpperSemicontinuous.addₓ'. -/
/-- The sum of two upper semicontinuous functions is upper semicontinuous. Formulated with
`[has_continuous_add]`. The primed version of the lemma uses an explicit continuity assumption on
addition, for application to `ereal`. -/
theorem UpperSemicontinuous.add {f g : α → γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun x => continuous_add.ContinuousAt
#align upper_semicontinuous.add UpperSemicontinuous.add

/- warning: upper_semicontinuous_within_at_sum -> upperSemicontinuousWithinAt_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) s x)) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) s x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) s x)) -> (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_sum upperSemicontinuousWithinAt_sumₓ'. -/
theorem upperSemicontinuousWithinAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x :=
  @lowerSemicontinuousWithinAt_sum α _ x s ι γᵒᵈ _ _ _ _ f a ha
#align upper_semicontinuous_within_at_sum upperSemicontinuousWithinAt_sum

/- warning: upper_semicontinuous_at_sum -> upperSemicontinuousAt_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) x)) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) x)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) x)) -> (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at_sum upperSemicontinuousAt_sumₓ'. -/
theorem upperSemicontinuousAt_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i in a, f i z) x :=
  by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha
#align upper_semicontinuous_at_sum upperSemicontinuousAt_sum

/- warning: upper_semicontinuous_on_sum -> upperSemicontinuousOn_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i) s)) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)) s)
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i) s)) -> (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_sum upperSemicontinuousOn_sumₓ'. -/
theorem upperSemicontinuousOn_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
#align upper_semicontinuous_on_sum upperSemicontinuousOn_sum

/- warning: upper_semicontinuous_sum -> upperSemicontinuous_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Type.{u2}} {γ : Type.{u3}} [_inst_3 : LinearOrderedAddCommMonoid.{u3} γ] [_inst_4 : TopologicalSpace.{u3} γ] [_inst_5 : OrderTopology.{u3} γ _inst_4 (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u3} γ _inst_4 (AddZeroClass.toHasAdd.{u3} γ (AddMonoid.toAddZeroClass.{u3} γ (AddCommMonoid.toAddMonoid.{u3} γ (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)))))] {f : ι -> α -> γ} {a : Finset.{u2} ι}, (forall (i : ι), (Membership.Mem.{u2, u2} ι (Finset.{u2} ι) (Finset.hasMem.{u2} ι) i a) -> (UpperSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (f i))) -> (UpperSemicontinuous.{u1, u3} α _inst_1 γ (PartialOrder.toPreorder.{u3} γ (OrderedAddCommMonoid.toPartialOrder.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3))) (fun (z : α) => Finset.sum.{u3, u2} γ ι (OrderedAddCommMonoid.toAddCommMonoid.{u3} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u3} γ _inst_3)) a (fun (i : ι) => f i z)))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {ι : Type.{u3}} {γ : Type.{u1}} [_inst_3 : LinearOrderedAddCommMonoid.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3)))] [_inst_6 : ContinuousAdd.{u1} γ _inst_4 (AddZeroClass.toAdd.{u1} γ (AddMonoid.toAddZeroClass.{u1} γ (AddCommMonoid.toAddMonoid.{u1} γ (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3))))] {f : ι -> α -> γ} {a : Finset.{u3} ι}, (forall (i : ι), (Membership.mem.{u3, u3} ι (Finset.{u3} ι) (Finset.instMembershipFinset.{u3} ι) i a) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (f i))) -> (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (OrderedAddCommMonoid.toPartialOrder.{u1} γ (LinearOrderedAddCommMonoid.toOrderedAddCommMonoid.{u1} γ _inst_3))) (fun (z : α) => Finset.sum.{u1, u3} γ ι (LinearOrderedAddCommMonoid.toAddCommMonoid.{u1} γ _inst_3) a (fun (i : ι) => f i z)))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_sum upperSemicontinuous_sumₓ'. -/
theorem upperSemicontinuous_sum {f : ι → α → γ} {a : Finset ι}
    (ha : ∀ i ∈ a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i in a, f i z :=
  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x
#align upper_semicontinuous_sum upperSemicontinuous_sum

end

/-! #### Infimum -/


section

variable {ι : Sort _} {δ δ' : Type _} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/- warning: upper_semicontinuous_within_at_cinfi -> upperSemicontinuousWithinAt_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u1} α (fun (y : α) => BddBelow.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i y))) (nhdsWithin.{u1} α _inst_1 x s)) -> (forall (i : ι), UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) s x) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iInf.{u3, u2} δ' (ConditionallyCompleteLattice.toHasInf.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u3} α (fun (y : α) => BddBelow.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i y))) (nhdsWithin.{u3} α _inst_1 x s)) -> (forall (i : ι), UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) s x) -> (UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iInf.{u2, u1} δ' (ConditionallyCompleteLattice.toInfSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_cinfi upperSemicontinuousWithinAt_ciInfₓ'. -/
theorem upperSemicontinuousWithinAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y))
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_ciSup α _ x s ι δ'ᵒᵈ _ f bdd h
#align upper_semicontinuous_within_at_cinfi upperSemicontinuousWithinAt_ciInf

/- warning: upper_semicontinuous_within_at_infi -> upperSemicontinuousWithinAt_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) s x) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) s x) -> (UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_infi upperSemicontinuousWithinAt_iInfₓ'. -/
theorem upperSemicontinuousWithinAt_iInf {f : ι → α → δ}
    (h : ∀ i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  @lowerSemicontinuousWithinAt_iSup α _ x s ι δᵒᵈ _ f h
#align upper_semicontinuous_within_at_infi upperSemicontinuousWithinAt_iInf

/- warning: upper_semicontinuous_within_at_binfi -> upperSemicontinuousWithinAt_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) s x) -> (UpperSemicontinuousWithinAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iInf.{u3, 0} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) s x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) s x) -> (UpperSemicontinuousWithinAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iInf.{u2, 0} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) s x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_within_at_binfi upperSemicontinuousWithinAt_biInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem upperSemicontinuousWithinAt_biInf {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi
#align upper_semicontinuous_within_at_binfi upperSemicontinuousWithinAt_biInf

/- warning: upper_semicontinuous_at_cinfi -> upperSemicontinuousAt_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u1} α (fun (y : α) => BddBelow.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i y))) (nhds.{u1} α _inst_1 x)) -> (forall (i : ι), UpperSemicontinuousAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) x) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iInf.{u3, u2} δ' (ConditionallyCompleteLattice.toHasInf.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (Filter.Eventually.{u3} α (fun (y : α) => BddBelow.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i y))) (nhds.{u3} α _inst_1 x)) -> (forall (i : ι), UpperSemicontinuousAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) x) -> (UpperSemicontinuousAt.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iInf.{u2, u1} δ' (ConditionallyCompleteLattice.toInfSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at_cinfi upperSemicontinuousAt_ciInfₓ'. -/
theorem upperSemicontinuousAt_ciInf {f : ι → α → δ'}
    (bdd : ∀ᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h
#align upper_semicontinuous_at_cinfi upperSemicontinuousAt_ciInf

/- warning: upper_semicontinuous_at_infi -> upperSemicontinuousAt_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) x) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) x) -> (UpperSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at_infi upperSemicontinuousAt_iInfₓ'. -/
theorem upperSemicontinuousAt_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h
#align upper_semicontinuous_at_infi upperSemicontinuousAt_iInf

/- warning: upper_semicontinuous_at_binfi -> upperSemicontinuousAt_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) x) -> (UpperSemicontinuousAt.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iInf.{u3, 0} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) x)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {x : α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) x) -> (UpperSemicontinuousAt.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iInf.{u2, 0} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) x)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_at_binfi upperSemicontinuousAt_biInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem upperSemicontinuousAt_biInf {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousAt (f i hi) x) :
    UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi
#align upper_semicontinuous_at_binfi upperSemicontinuousAt_biInf

/- warning: upper_semicontinuous_on_cinfi -> upperSemicontinuousOn_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) x s) -> (BddBelow.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x)))) -> (forall (i : ι), UpperSemicontinuousOn.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i) s) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iInf.{u3, u2} δ' (ConditionallyCompleteLattice.toHasInf.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ' : Type.{u2}} [_inst_4 : ConditionallyCompleteLinearOrder.{u2} δ'] {f : ι -> α -> δ'}, (forall (x : α), (Membership.mem.{u3, u3} α (Set.{u3} α) (Set.instMembershipSet.{u3} α) x s) -> (BddBelow.{u2} δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (Set.range.{u2, u1} δ' ι (fun (i : ι) => f i x)))) -> (forall (i : ι), UpperSemicontinuousOn.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (f i) s) -> (UpperSemicontinuousOn.{u3, u2} α _inst_1 δ' (PartialOrder.toPreorder.{u2} δ' (SemilatticeInf.toPartialOrder.{u2} δ' (Lattice.toSemilatticeInf.{u2} δ' (ConditionallyCompleteLattice.toLattice.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4))))) (fun (x' : α) => iInf.{u2, u1} δ' (ConditionallyCompleteLattice.toInfSet.{u2} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ' _inst_4)) ι (fun (i : ι) => f i x')) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_cinfi upperSemicontinuousOn_ciInfₓ'. -/
theorem upperSemicontinuousOn_ciInf {f : ι → α → δ'}
    (bdd : ∀ x ∈ s, BddBelow (range fun i => f i x)) (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
#align upper_semicontinuous_on_cinfi upperSemicontinuousOn_ciInf

/- warning: upper_semicontinuous_on_infi -> upperSemicontinuousOn_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i) s) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i) s) -> (UpperSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_infi upperSemicontinuousOn_iInfₓ'. -/
theorem upperSemicontinuousOn_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx
#align upper_semicontinuous_on_infi upperSemicontinuousOn_iInf

/- warning: upper_semicontinuous_on_binfi -> upperSemicontinuousOn_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi) s) -> (UpperSemicontinuousOn.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iInf.{u3, 0} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))) s)
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {s : Set.{u3} α} {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi) s) -> (UpperSemicontinuousOn.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iInf.{u2, 0} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))) s)
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_on_binfi upperSemicontinuousOn_biInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem upperSemicontinuousOn_biInf {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuousOn (f i hi) s) :
    UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi
#align upper_semicontinuous_on_binfi upperSemicontinuousOn_biInf

/- warning: upper_semicontinuous_cinfi -> upperSemicontinuous_ciInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), BddBelow.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x))) -> (forall (i : ι), UpperSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i)) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iInf.{u3, u2} δ' (ConditionallyCompleteLattice.toHasInf.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ' : Type.{u3}} [_inst_4 : ConditionallyCompleteLinearOrder.{u3} δ'] {f : ι -> α -> δ'}, (forall (x : α), BddBelow.{u3} δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (Set.range.{u3, u2} δ' ι (fun (i : ι) => f i x))) -> (forall (i : ι), UpperSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (f i)) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ' (PartialOrder.toPreorder.{u3} δ' (SemilatticeInf.toPartialOrder.{u3} δ' (Lattice.toSemilatticeInf.{u3} δ' (ConditionallyCompleteLattice.toLattice.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4))))) (fun (x' : α) => iInf.{u3, u2} δ' (ConditionallyCompleteLattice.toInfSet.{u3} δ' (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u3} δ' _inst_4)) ι (fun (i : ι) => f i x')))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_cinfi upperSemicontinuous_ciInfₓ'. -/
theorem upperSemicontinuous_ciInf {f : ι → α → δ'} (bdd : ∀ x, BddBelow (range fun i => f i x))
    (h : ∀ i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x =>
  upperSemicontinuousAt_ciInf (eventually_of_forall bdd) fun i => h i x
#align upper_semicontinuous_cinfi upperSemicontinuous_ciInf

/- warning: upper_semicontinuous_infi -> upperSemicontinuous_iInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i)) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => f i x')))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {f : ι -> α -> δ}, (forall (i : ι), UpperSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i)) -> (UpperSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => f i x')))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_infi upperSemicontinuous_iInfₓ'. -/
theorem upperSemicontinuous_iInf {f : ι → α → δ} (h : ∀ i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upperSemicontinuousAt_iInf fun i => h i x
#align upper_semicontinuous_infi upperSemicontinuous_iInf

/- warning: upper_semicontinuous_binfi -> upperSemicontinuous_biInf is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {ι : Sort.{u2}} {δ : Type.{u3}} [_inst_3 : CompleteLinearOrder.{u3} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (f i hi)) -> (UpperSemicontinuous.{u1, u3} α _inst_1 δ (PartialOrder.toPreorder.{u3} δ (CompleteSemilatticeInf.toPartialOrder.{u3} δ (CompleteLattice.toCompleteSemilatticeInf.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3)))) (fun (x' : α) => iInf.{u3, u2} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) ι (fun (i : ι) => iInf.{u3, 0} δ (ConditionallyCompleteLattice.toHasInf.{u3} δ (CompleteLattice.toConditionallyCompleteLattice.{u3} δ (CompleteLinearOrder.toCompleteLattice.{u3} δ _inst_3))) (p i) (fun (hi : p i) => f i hi x'))))
but is expected to have type
  forall {α : Type.{u3}} [_inst_1 : TopologicalSpace.{u3} α] {ι : Sort.{u1}} {δ : Type.{u2}} [_inst_3 : CompleteLinearOrder.{u2} δ] {p : ι -> Prop} {f : forall (i : ι), (p i) -> α -> δ}, (forall (i : ι) (hi : p i), UpperSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (f i hi)) -> (UpperSemicontinuous.{u3, u2} α _inst_1 δ (PartialOrder.toPreorder.{u2} δ (CompleteSemilatticeInf.toPartialOrder.{u2} δ (CompleteLattice.toCompleteSemilatticeInf.{u2} δ (CompleteLinearOrder.toCompleteLattice.{u2} δ _inst_3)))) (fun (x' : α) => iInf.{u2, u1} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) ι (fun (i : ι) => iInf.{u2, 0} δ (ConditionallyCompleteLattice.toInfSet.{u2} δ (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{u2} δ (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{u2} δ (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{u2} δ _inst_3)))) (p i) (fun (hi : p i) => f i hi x'))))
Case conversion may be inaccurate. Consider using '#align upper_semicontinuous_binfi upperSemicontinuous_biInfₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i hi) -/
theorem upperSemicontinuous_biInf {p : ι → Prop} {f : ∀ (i) (h : p i), α → δ}
    (h : ∀ i hi, UpperSemicontinuous (f i hi)) :
    UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi
#align upper_semicontinuous_binfi upperSemicontinuous_biInf

end

section

variable {γ : Type _} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

/- warning: continuous_within_at_iff_lower_upper_semicontinuous_within_at -> continuousWithinAt_iff_lower_upperSemicontinuousWithinAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, Iff (ContinuousWithinAt.{u1, u2} α γ _inst_1 _inst_4 f s x) (And (LowerSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x) (UpperSemicontinuousWithinAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s x))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, Iff (ContinuousWithinAt.{u2, u1} α γ _inst_1 _inst_4 f s x) (And (LowerSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s x) (UpperSemicontinuousWithinAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s x))
Case conversion may be inaccurate. Consider using '#align continuous_within_at_iff_lower_upper_semicontinuous_within_at continuousWithinAt_iff_lower_upperSemicontinuousWithinAtₓ'. -/
theorem continuousWithinAt_iff_lower_upperSemicontinuousWithinAt {f : α → γ} :
    ContinuousWithinAt f s x ↔
      LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuousWithinAt f s x :=
  by
  refine' ⟨fun h => ⟨h.LowerSemicontinuousWithinAt, h.UpperSemicontinuousWithinAt⟩, _⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases Hl : ∃ l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₁ l lfx, h₂ u fxu]with a lfa fau
      cases' le_or_gt (f a) (f x) with h h
      · exact hl ⟨lfa, h⟩
      · exact hu ⟨le_of_lt h, fau⟩
    · simp only [not_exists, not_lt] at Hu
      filter_upwards [h₁ l lfx]with a lfa using hl ⟨lfa, Hu (f a)⟩
  · simp only [not_exists, not_lt] at Hl
    by_cases Hu : ∃ u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₂ u fxu]with a lfa
      apply hu
      exact ⟨Hl (f a), lfa⟩
    · simp only [not_exists, not_lt] at Hu
      apply Filter.eventually_of_forall
      intro a
      have : f a = f x := le_antisymm (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv
#align continuous_within_at_iff_lower_upper_semicontinuous_within_at continuousWithinAt_iff_lower_upperSemicontinuousWithinAt

/- warning: continuous_at_iff_lower_upper_semicontinuous_at -> continuousAt_iff_lower_upperSemicontinuousAt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {x : α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, Iff (ContinuousAt.{u1, u2} α γ _inst_1 _inst_4 f x) (And (LowerSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x) (UpperSemicontinuousAt.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f x))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {x : α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, Iff (ContinuousAt.{u2, u1} α γ _inst_1 _inst_4 f x) (And (LowerSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f x) (UpperSemicontinuousAt.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f x))
Case conversion may be inaccurate. Consider using '#align continuous_at_iff_lower_upper_semicontinuous_at continuousAt_iff_lower_upperSemicontinuousAtₓ'. -/
theorem continuousAt_iff_lower_upperSemicontinuousAt {f : α → γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
#align continuous_at_iff_lower_upper_semicontinuous_at continuousAt_iff_lower_upperSemicontinuousAt

/- warning: continuous_on_iff_lower_upper_semicontinuous_on -> continuousOn_iff_lower_upperSemicontinuousOn is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {s : Set.{u1} α} {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, Iff (ContinuousOn.{u1, u2} α γ _inst_1 _inst_4 f s) (And (LowerSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s) (UpperSemicontinuousOn.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f s))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {s : Set.{u2} α} {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, Iff (ContinuousOn.{u2, u1} α γ _inst_1 _inst_4 f s) (And (LowerSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s) (UpperSemicontinuousOn.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f s))
Case conversion may be inaccurate. Consider using '#align continuous_on_iff_lower_upper_semicontinuous_on continuousOn_iff_lower_upperSemicontinuousOnₓ'. -/
theorem continuousOn_iff_lower_upperSemicontinuousOn {f : α → γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s :=
  by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩
#align continuous_on_iff_lower_upper_semicontinuous_on continuousOn_iff_lower_upperSemicontinuousOn

/- warning: continuous_iff_lower_upper_semicontinuous -> continuous_iff_lower_upperSemicontinuous is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : TopologicalSpace.{u1} α] {γ : Type.{u2}} [_inst_3 : LinearOrder.{u2} γ] [_inst_4 : TopologicalSpace.{u2} γ] [_inst_5 : OrderTopology.{u2} γ _inst_4 (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3))))] {f : α -> γ}, Iff (Continuous.{u1, u2} α γ _inst_1 _inst_4 f) (And (LowerSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f) (UpperSemicontinuous.{u1, u2} α _inst_1 γ (PartialOrder.toPreorder.{u2} γ (SemilatticeInf.toPartialOrder.{u2} γ (Lattice.toSemilatticeInf.{u2} γ (LinearOrder.toLattice.{u2} γ _inst_3)))) f))
but is expected to have type
  forall {α : Type.{u2}} [_inst_1 : TopologicalSpace.{u2} α] {γ : Type.{u1}} [_inst_3 : LinearOrder.{u1} γ] [_inst_4 : TopologicalSpace.{u1} γ] [_inst_5 : OrderTopology.{u1} γ _inst_4 (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3)))))] {f : α -> γ}, Iff (Continuous.{u2, u1} α γ _inst_1 _inst_4 f) (And (LowerSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f) (UpperSemicontinuous.{u2, u1} α _inst_1 γ (PartialOrder.toPreorder.{u1} γ (SemilatticeInf.toPartialOrder.{u1} γ (Lattice.toSemilatticeInf.{u1} γ (DistribLattice.toLattice.{u1} γ (instDistribLattice.{u1} γ _inst_3))))) f))
Case conversion may be inaccurate. Consider using '#align continuous_iff_lower_upper_semicontinuous continuous_iff_lower_upperSemicontinuousₓ'. -/
theorem continuous_iff_lower_upperSemicontinuous {f : α → γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [continuous_iff_continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]
#align continuous_iff_lower_upper_semicontinuous continuous_iff_lower_upperSemicontinuous

end

