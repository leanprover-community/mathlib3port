/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

! This file was ported from Lean 3 source module data.real.nnreal
! leanprover-community/mathlib commit b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Group
import Mathbin.Algebra.Algebra.Basic
import Mathbin.Algebra.Order.Nonneg.Field
import Mathbin.Algebra.Order.Field.Canonical.Basic
import Mathbin.Data.Real.Pointwise
import Mathbin.Tactic.Positivity

/-!
# Nonnegative real numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a conditionally
  complete linear ordered archimedean commutative semifield; we have no typeclass for this in
  `mathlib` yet, so we define the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `ordered_comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `canonically_linear_ordered_add_monoid ℝ≥0`;
  - `archimedean ℝ≥0`;
  - `conditionally_complete_linear_order_bot ℝ≥0`.

  These instances are derived from corresponding instances about the type `{x : α // 0 ≤ x}` in an
  appropriate ordered field/ring/group/monoid `α`. See `algebra/order/nonneg`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/


open Classical BigOperators

#print NNReal /-
-- to ensure these instances are computable
/-- Nonnegative real numbers. -/
def NNReal :=
  { r : ℝ // 0 ≤ r }deriving StrictOrderedSemiring, CommMonoidWithZero, FloorSemiring, CommSemiring,
  Semiring, SemilatticeInf, SemilatticeSup, DistribLattice, DenselyOrdered, OrderBot,
  CanonicallyLinearOrderedSemifield, LinearOrderedCommGroupWithZero, Archimedean,
  LinearOrderedSemiring, OrderedCommSemiring, CanonicallyOrderedCommSemiring, Sub, OrderedSub, Div,
  Inhabited
#align nnreal NNReal
-/

-- mathport name: nnreal
scoped[NNReal] notation "ℝ≥0" => NNReal

namespace NNReal

instance : Coe ℝ≥0 ℝ :=
  ⟨Subtype.val⟩

/- warning: nnreal.val_eq_coe -> NNReal.val_eq_coe is a dubious translation:
lean 3 declaration is
  forall (n : NNReal), Eq.{1} Real (Subtype.val.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) n)
but is expected to have type
  forall (n : NNReal), Eq.{1} Real (Subtype.val.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) n) (NNReal.toReal n)
Case conversion may be inaccurate. Consider using '#align nnreal.val_eq_coe NNReal.val_eq_coeₓ'. -/
-- Simp lemma to put back `n.val` into the normal form given by the coercion.
@[simp]
theorem val_eq_coe (n : ℝ≥0) : n.val = n :=
  rfl
#align nnreal.val_eq_coe NNReal.val_eq_coe

/- warning: nnreal.can_lift -> NNReal.canLift is a dubious translation:
lean 3 declaration is
  CanLift.{1, 1} Real NNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)
but is expected to have type
  CanLift.{1, 1} Real NNReal NNReal.toReal (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r)
Case conversion may be inaccurate. Consider using '#align nnreal.can_lift NNReal.canLiftₓ'. -/
instance canLift : CanLift ℝ ℝ≥0 coe fun r => 0 ≤ r :=
  Subtype.canLift _
#align nnreal.can_lift NNReal.canLift

/- warning: nnreal.eq -> NNReal.eq is a dubious translation:
lean 3 declaration is
  forall {n : NNReal} {m : NNReal}, (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) m)) -> (Eq.{1} NNReal n m)
but is expected to have type
  forall {n : NNReal} {m : NNReal}, (Eq.{1} Real (NNReal.toReal n) (NNReal.toReal m)) -> (Eq.{1} NNReal n m)
Case conversion may be inaccurate. Consider using '#align nnreal.eq NNReal.eqₓ'. -/
protected theorem eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m :=
  Subtype.eq
#align nnreal.eq NNReal.eq

/- warning: nnreal.eq_iff -> NNReal.eq_iff is a dubious translation:
lean 3 declaration is
  forall {n : NNReal} {m : NNReal}, Iff (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) n) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) m)) (Eq.{1} NNReal n m)
but is expected to have type
  forall {n : NNReal} {m : NNReal}, Iff (Eq.{1} Real (NNReal.toReal n) (NNReal.toReal m)) (Eq.{1} NNReal n m)
Case conversion may be inaccurate. Consider using '#align nnreal.eq_iff NNReal.eq_iffₓ'. -/
protected theorem eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
  Iff.intro NNReal.eq (congr_arg coe)
#align nnreal.eq_iff NNReal.eq_iff

/- warning: nnreal.ne_iff -> NNReal.ne_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, Iff (Ne.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) y)) (Ne.{1} NNReal x y)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, Iff (Ne.{1} Real (NNReal.toReal x) (NNReal.toReal y)) (Ne.{1} NNReal x y)
Case conversion may be inaccurate. Consider using '#align nnreal.ne_iff NNReal.ne_iffₓ'. -/
theorem ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
  not_congr <| NNReal.eq_iff
#align nnreal.ne_iff NNReal.ne_iff

/- warning: nnreal.forall -> NNReal.forall is a dubious translation:
lean 3 declaration is
  forall {p : NNReal -> Prop}, Iff (forall (x : NNReal), p x) (forall (x : Real) (hx : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x), p (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) x hx))
but is expected to have type
  forall {p : NNReal -> Prop}, Iff (forall (x : NNReal), p x) (forall (x : Real) (hx : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x), p (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) x hx))
Case conversion may be inaccurate. Consider using '#align nnreal.forall NNReal.forallₓ'. -/
protected theorem forall {p : ℝ≥0 → Prop} : (∀ x : ℝ≥0, p x) ↔ ∀ (x : ℝ) (hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.forall
#align nnreal.forall NNReal.forall

/- warning: nnreal.exists -> NNReal.exists is a dubious translation:
lean 3 declaration is
  forall {p : NNReal -> Prop}, Iff (Exists.{1} NNReal (fun (x : NNReal) => p x)) (Exists.{1} Real (fun (x : Real) => Exists.{0} (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (hx : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) => p (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) x hx))))
but is expected to have type
  forall {p : NNReal -> Prop}, Iff (Exists.{1} NNReal (fun (x : NNReal) => p x)) (Exists.{1} Real (fun (x : Real) => Exists.{0} (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (fun (hx : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) => p (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) x hx))))
Case conversion may be inaccurate. Consider using '#align nnreal.exists NNReal.existsₓ'. -/
protected theorem exists {p : ℝ≥0 → Prop} : (∃ x : ℝ≥0, p x) ↔ ∃ (x : ℝ)(hx : 0 ≤ x), p ⟨x, hx⟩ :=
  Subtype.exists
#align nnreal.exists NNReal.exists

#print Real.toNNReal /-
/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
noncomputable def Real.toNNReal (r : ℝ) : ℝ≥0 :=
  ⟨max r 0, le_max_right _ _⟩
#align real.to_nnreal Real.toNNReal
-/

/- warning: real.coe_to_nnreal -> Real.coe_toNNReal is a dubious translation:
lean 3 declaration is
  forall (r : Real), (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Real.toNNReal r)) r)
but is expected to have type
  forall (r : Real), (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (NNReal.toReal (Real.toNNReal r)) r)
Case conversion may be inaccurate. Consider using '#align real.coe_to_nnreal Real.coe_toNNRealₓ'. -/
theorem Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (Real.toNNReal r : ℝ) = r :=
  max_eq_left hr
#align real.coe_to_nnreal Real.coe_toNNReal

/- warning: real.to_nnreal_of_nonneg -> Real.toNNReal_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {r : Real} (hr : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r), Eq.{1} NNReal (Real.toNNReal r) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) r hr)
but is expected to have type
  forall {r : Real} (hr : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r), Eq.{1} NNReal (Real.toNNReal r) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) r hr)
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_of_nonneg Real.toNNReal_of_nonnegₓ'. -/
theorem Real.toNNReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : r.toNNReal = ⟨r, hr⟩ := by
  simp_rw [Real.toNNReal, max_eq_left hr]
#align real.to_nnreal_of_nonneg Real.toNNReal_of_nonneg

/- warning: real.le_coe_to_nnreal -> Real.le_coe_toNNReal is a dubious translation:
lean 3 declaration is
  forall (r : Real), LE.le.{0} Real Real.hasLe r ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Real.toNNReal r))
but is expected to have type
  forall (r : Real), LE.le.{0} Real Real.instLEReal r (NNReal.toReal (Real.toNNReal r))
Case conversion may be inaccurate. Consider using '#align real.le_coe_to_nnreal Real.le_coe_toNNRealₓ'. -/
theorem Real.le_coe_toNNReal (r : ℝ) : r ≤ Real.toNNReal r :=
  le_max_left r 0
#align real.le_coe_to_nnreal Real.le_coe_toNNReal

/- warning: nnreal.coe_nonneg -> NNReal.coe_nonneg is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)
but is expected to have type
  forall (r : NNReal), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal r)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_nonneg NNReal.coe_nonnegₓ'. -/
theorem coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r :=
  r.2
#align nnreal.coe_nonneg NNReal.coe_nonneg

/- warning: nnreal.coe_mk -> NNReal.coe_mk is a dubious translation:
lean 3 declaration is
  forall (a : Real) (ha : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) Real (HasLiftT.mk.{1, 1} (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) Real (CoeTCₓ.coe.{1, 1} (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) Real (coeBase.{1, 1} (Subtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)) Real (coeSubtype.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r))))) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) a ha)) a
but is expected to have type
  forall (a : Real) (ha : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a), Eq.{1} Real (NNReal.toReal (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) a ha)) a
Case conversion may be inaccurate. Consider using '#align nnreal.coe_mk NNReal.coe_mkₓ'. -/
@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0) : ℝ) = a :=
  rfl
#align nnreal.coe_mk NNReal.coe_mk

example : Zero ℝ≥0 := by infer_instance

example : One ℝ≥0 := by infer_instance

example : Add ℝ≥0 := by infer_instance

noncomputable example : Sub ℝ≥0 := by infer_instance

example : Mul ℝ≥0 := by infer_instance

noncomputable example : Inv ℝ≥0 := by infer_instance

noncomputable example : Div ℝ≥0 := by infer_instance

example : LE ℝ≥0 := by infer_instance

example : Bot ℝ≥0 := by infer_instance

example : Inhabited ℝ≥0 := by infer_instance

example : Nontrivial ℝ≥0 := by infer_instance

/- warning: nnreal.coe_injective -> NNReal.coe_injective is a dubious translation:
lean 3 declaration is
  Function.Injective.{1, 1} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))))
but is expected to have type
  Function.Injective.{1, 1} NNReal Real NNReal.toReal
Case conversion may be inaccurate. Consider using '#align nnreal.coe_injective NNReal.coe_injectiveₓ'. -/
protected theorem coe_injective : Function.Injective (coe : ℝ≥0 → ℝ) :=
  Subtype.coe_injective
#align nnreal.coe_injective NNReal.coe_injective

/- warning: nnreal.coe_eq -> NNReal.coe_eq is a dubious translation:
lean 3 declaration is
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂)) (Eq.{1} NNReal r₁ r₂)
but is expected to have type
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (Eq.{1} Real (NNReal.toReal r₁) (NNReal.toReal r₂)) (Eq.{1} NNReal r₁ r₂)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_eq NNReal.coe_eqₓ'. -/
@[simp, norm_cast]
protected theorem coe_eq {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
  NNReal.coe_injective.eq_iff
#align nnreal.coe_eq NNReal.coe_eq

/- warning: nnreal.coe_zero -> NNReal.coe_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (NNReal.toReal (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_zero NNReal.coe_zeroₓ'. -/
protected theorem coe_zero : ((0 : ℝ≥0) : ℝ) = 0 :=
  rfl
#align nnreal.coe_zero NNReal.coe_zero

/- warning: nnreal.coe_one -> NNReal.coe_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (NNReal.toReal (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_one NNReal.coe_oneₓ'. -/
protected theorem coe_one : ((1 : ℝ≥0) : ℝ) = 1 :=
  rfl
#align nnreal.coe_one NNReal.coe_one

/- warning: nnreal.coe_add -> NNReal.coe_add is a dubious translation:
lean 3 declaration is
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r₁ r₂)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂))
but is expected to have type
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real (NNReal.toReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) r₁ r₂)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (NNReal.toReal r₁) (NNReal.toReal r₂))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_add NNReal.coe_addₓ'. -/
protected theorem coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ :=
  rfl
#align nnreal.coe_add NNReal.coe_add

/- warning: nnreal.coe_mul -> NNReal.coe_mul is a dubious translation:
lean 3 declaration is
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r₁ r₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂))
but is expected to have type
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real (NNReal.toReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r₁ r₂)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (NNReal.toReal r₁) (NNReal.toReal r₂))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_mul NNReal.coe_mulₓ'. -/
protected theorem coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ :=
  rfl
#align nnreal.coe_mul NNReal.coe_mul

/- warning: nnreal.coe_inv -> NNReal.coe_inv is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) r)) (Inv.inv.{0} Real Real.hasInv ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))
but is expected to have type
  forall (r : NNReal), Eq.{1} Real (NNReal.toReal (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) r)) (Inv.inv.{0} Real Real.instInvReal (NNReal.toReal r))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_inv NNReal.coe_invₓ'. -/
protected theorem coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ :=
  rfl
#align nnreal.coe_inv NNReal.coe_inv

/- warning: nnreal.coe_div -> NNReal.coe_div is a dubious translation:
lean 3 declaration is
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) r₁ r₂)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂))
but is expected to have type
  forall (r₁ : NNReal) (r₂ : NNReal), Eq.{1} Real (NNReal.toReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) r₁ r₂)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (NNReal.toReal r₁) (NNReal.toReal r₂))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_div NNReal.coe_divₓ'. -/
protected theorem coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ :=
  rfl
#align nnreal.coe_div NNReal.coe_div

/- warning: nnreal.coe_bit0 clashes with [anonymous] -> [anonymous]
warning: nnreal.coe_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) r)) (bit0.{0} Real Real.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))
but is expected to have type
  forall {r : Type.{u}} {β : Type.{v}}, (Nat -> r -> β) -> Nat -> (List.{u} r) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
protected theorem [anonymous] (r : ℝ≥0) : ((bit0 r : ℝ≥0) : ℝ) = bit0 r :=
  rfl
#align nnreal.coe_bit0 [anonymous]

/- warning: nnreal.coe_bit1 clashes with [anonymous] -> [anonymous]
warning: nnreal.coe_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (bit1.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) r)) (bit1.{0} Real Real.hasOne Real.hasAdd ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))
but is expected to have type
  forall {r : Type.{u}} {β : Type.{v}}, (Nat -> r -> β) -> Nat -> (List.{u} r) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
protected theorem [anonymous] (r : ℝ≥0) : ((bit1 r : ℝ≥0) : ℝ) = bit1 r :=
  rfl
#align nnreal.coe_bit1 [anonymous]

/- warning: nnreal.coe_two -> NNReal.coe_two is a dubious translation:
lean 3 declaration is
  Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (OfNat.ofNat.{0} NNReal 2 (OfNat.mk.{0} NNReal 2 (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Eq.{1} Real (NNReal.toReal (OfNat.ofNat.{0} NNReal 2 (instOfNat.{0} NNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_two NNReal.coe_twoₓ'. -/
protected theorem coe_two : ((2 : ℝ≥0) : ℝ) = 2 :=
  rfl
#align nnreal.coe_two NNReal.coe_two

/- warning: nnreal.coe_sub -> NNReal.coe_sub is a dubious translation:
lean 3 declaration is
  forall {r₁ : NNReal} {r₂ : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r₂ r₁) -> (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) r₁ r₂)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂)))
but is expected to have type
  forall {r₁ : NNReal} {r₂ : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r₂ r₁) -> (Eq.{1} Real (NNReal.toReal (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) r₁ r₂)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (NNReal.toReal r₁) (NNReal.toReal r₂)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_sub NNReal.coe_subₓ'. -/
@[simp, norm_cast]
protected theorem coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
  max_eq_left <| le_sub_comm.2 <| by simp [show (r₂ : ℝ) ≤ r₁ from h]
#align nnreal.coe_sub NNReal.coe_sub

/- warning: nnreal.coe_eq_zero -> NNReal.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), Iff (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall (r : NNReal), Iff (Eq.{1} Real (NNReal.toReal r) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_eq_zero NNReal.coe_eq_zeroₓ'. -/
@[simp, norm_cast]
protected theorem coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := by
  rw [← NNReal.coe_zero, NNReal.coe_eq]
#align nnreal.coe_eq_zero NNReal.coe_eq_zero

/- warning: nnreal.coe_eq_one -> NNReal.coe_eq_one is a dubious translation:
lean 3 declaration is
  forall (r : NNReal), Iff (Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} NNReal r (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall (r : NNReal), Iff (Eq.{1} Real (NNReal.toReal r) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} NNReal r (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_eq_one NNReal.coe_eq_oneₓ'. -/
@[simp, norm_cast]
protected theorem coe_eq_one (r : ℝ≥0) : ↑r = (1 : ℝ) ↔ r = 1 := by
  rw [← NNReal.coe_one, NNReal.coe_eq]
#align nnreal.coe_eq_one NNReal.coe_eq_one

/- warning: nnreal.coe_ne_zero -> NNReal.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Iff (Ne.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {r : NNReal}, Iff (Ne.{1} Real (NNReal.toReal r) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_ne_zero NNReal.coe_ne_zeroₓ'. -/
theorem coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by norm_cast
#align nnreal.coe_ne_zero NNReal.coe_ne_zero

example : CommSemiring ℝ≥0 := by infer_instance

#print NNReal.toRealHom /-
/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def toRealHom : ℝ≥0 →+* ℝ :=
  ⟨coe, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_zero, NNReal.coe_add⟩
#align nnreal.to_real_hom NNReal.toRealHom
-/

/- warning: nnreal.coe_to_real_hom -> NNReal.coe_toRealHom is a dubious translation:
lean 3 declaration is
  Eq.{1} (NNReal -> Real) (coeFn.{1, 1} (RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (fun (_x : RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) => NNReal -> Real) (RingHom.hasCoeToFun.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) NNReal.toRealHom) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))))
but is expected to have type
  Eq.{1} (forall (ᾰ : NNReal), (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : NNReal) => Real) ᾰ) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) NNReal (fun (_x : NNReal) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : NNReal) => Real) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) NNReal Real (NonUnitalNonAssocSemiring.toMul.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (NonUnitalNonAssocSemiring.toMul.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) NNReal Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)) (RingHom.instRingHomClassRingHom.{0, 0} NNReal Real (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring) (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))))) NNReal.toRealHom) NNReal.toReal
Case conversion may be inaccurate. Consider using '#align nnreal.coe_to_real_hom NNReal.coe_toRealHomₓ'. -/
@[simp]
theorem coe_toRealHom : ⇑toRealHom = coe :=
  rfl
#align nnreal.coe_to_real_hom NNReal.coe_toRealHom

section Actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type _} [MulAction ℝ M] : MulAction ℝ≥0 M :=
  MulAction.compHom M toRealHom.toMonoidHom

/- warning: nnreal.smul_def -> NNReal.smul_def is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : MulAction.{0, u1} Real M Real.monoid] (c : NNReal) (x : M), Eq.{succ u1} M (SMul.smul.{0, u1} NNReal M (MulAction.toHasSmul.{0, u1} NNReal M (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)) (NNReal.mulAction.{u1} M _inst_1)) c x) (SMul.smul.{0, u1} Real M (MulAction.toHasSmul.{0, u1} Real M Real.monoid _inst_1) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) c) x)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : MulAction.{0, u1} Real M Real.instMonoidReal] (c : NNReal) (x : M), Eq.{succ u1} M (HSMul.hSMul.{0, u1, u1} NNReal M M (instHSMul.{0, u1} NNReal M (MulAction.toSMul.{0, u1} NNReal M (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)) (NNReal.instMulActionNNRealToMonoidToMonoidWithZeroInstNNRealSemiring.{u1} M _inst_1))) c x) (HSMul.hSMul.{0, u1, u1} Real M M (instHSMul.{0, u1} Real M (MulAction.toSMul.{0, u1} Real M Real.instMonoidReal _inst_1)) (NNReal.toReal c) x)
Case conversion may be inaccurate. Consider using '#align nnreal.smul_def NNReal.smul_defₓ'. -/
theorem smul_def {M : Type _} [MulAction ℝ M] (c : ℝ≥0) (x : M) : c • x = (c : ℝ) • x :=
  rfl
#align nnreal.smul_def NNReal.smul_def

instance {M N : Type _} [MulAction ℝ M] [MulAction ℝ N] [SMul M N] [IsScalarTower ℝ M N] :
    IsScalarTower ℝ≥0 M N where smul_assoc r := (smul_assoc (r : ℝ) : _)

/- warning: nnreal.smul_comm_class_left -> NNReal.sMulCommClass_left is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulAction.{0, u2} Real N Real.monoid] [_inst_2 : SMul.{u1, u2} M N] [_inst_3 : SMulCommClass.{0, u1, u2} Real M N (MulAction.toHasSmul.{0, u2} Real N Real.monoid _inst_1) _inst_2], SMulCommClass.{0, u1, u2} NNReal M N (MulAction.toHasSmul.{0, u2} NNReal N (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)) (NNReal.mulAction.{u2} N _inst_1)) _inst_2
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulAction.{0, u2} Real N Real.instMonoidReal] [_inst_2 : SMul.{u1, u2} M N] [_inst_3 : SMulCommClass.{0, u1, u2} Real M N (MulAction.toSMul.{0, u2} Real N Real.instMonoidReal _inst_1) _inst_2], SMulCommClass.{0, u1, u2} NNReal M N (MulAction.toSMul.{0, u2} NNReal N (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)) (NNReal.instMulActionNNRealToMonoidToMonoidWithZeroInstNNRealSemiring.{u2} N _inst_1)) _inst_2
Case conversion may be inaccurate. Consider using '#align nnreal.smul_comm_class_left NNReal.sMulCommClass_leftₓ'. -/
instance sMulCommClass_left {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass ℝ M N] :
    SMulCommClass ℝ≥0 M N where smul_comm r := (smul_comm (r : ℝ) : _)
#align nnreal.smul_comm_class_left NNReal.sMulCommClass_left

/- warning: nnreal.smul_comm_class_right -> NNReal.sMulCommClass_right is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulAction.{0, u2} Real N Real.monoid] [_inst_2 : SMul.{u1, u2} M N] [_inst_3 : SMulCommClass.{u1, 0, u2} M Real N _inst_2 (MulAction.toHasSmul.{0, u2} Real N Real.monoid _inst_1)], SMulCommClass.{u1, 0, u2} M NNReal N _inst_2 (MulAction.toHasSmul.{0, u2} NNReal N (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)) (NNReal.mulAction.{u2} N _inst_1))
but is expected to have type
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : MulAction.{0, u2} Real N Real.instMonoidReal] [_inst_2 : SMul.{u1, u2} M N] [_inst_3 : SMulCommClass.{u1, 0, u2} M Real N _inst_2 (MulAction.toSMul.{0, u2} Real N Real.instMonoidReal _inst_1)], SMulCommClass.{u1, 0, u2} M NNReal N _inst_2 (MulAction.toSMul.{0, u2} NNReal N (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)) (NNReal.instMulActionNNRealToMonoidToMonoidWithZeroInstNNRealSemiring.{u2} N _inst_1))
Case conversion may be inaccurate. Consider using '#align nnreal.smul_comm_class_right NNReal.sMulCommClass_rightₓ'. -/
instance sMulCommClass_right {M N : Type _} [MulAction ℝ N] [SMul M N] [SMulCommClass M ℝ N] :
    SMulCommClass M ℝ≥0 N where smul_comm m r := (smul_comm m (r : ℝ) : _)
#align nnreal.smul_comm_class_right NNReal.sMulCommClass_right

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type _} [AddMonoid M] [DistribMulAction ℝ M] : DistribMulAction ℝ≥0 M :=
  DistribMulAction.compHom M toRealHom.toMonoidHom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type _} [AddCommMonoid M] [Module ℝ M] : Module ℝ≥0 M :=
  Module.compHom M toRealHom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type _} [Semiring A] [Algebra ℝ A] : Algebra ℝ≥0 A
    where
  smul := (· • ·)
  commutes' r x := by simp [Algebra.commutes]
  smul_def' r x := by simp [← Algebra.smul_def (r : ℝ) x, smul_def]
  toRingHom := (algebraMap ℝ A).comp (toRealHom : ℝ≥0 →+* ℝ)

-- verify that the above produces instances we might care about
example : Algebra ℝ≥0 ℝ := by infer_instance

example : DistribMulAction ℝ≥0ˣ ℝ := by infer_instance

end Actions

example : MonoidWithZero ℝ≥0 := by infer_instance

example : CommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : CommGroupWithZero ℝ≥0 := by infer_instance

/- warning: nnreal.coe_indicator -> NNReal.coe_indicator is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : α -> NNReal) (a : α), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) s f a)) (Set.indicator.{u1, 0} α Real Real.hasZero s (fun (x : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f x)) a)
but is expected to have type
  forall {α : Type.{u1}} (s : Set.{u1} α) (f : α -> NNReal) (a : α), Eq.{1} Real (NNReal.toReal (Set.indicator.{u1, 0} α NNReal instNNRealZero s f a)) (Set.indicator.{u1, 0} α Real Real.instZeroReal s (fun (x : α) => NNReal.toReal (f x)) a)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_indicator NNReal.coe_indicatorₓ'. -/
@[simp, norm_cast]
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => f x) a :=
  (toRealHom : ℝ≥0 →+ ℝ).map_indicator _ _ _
#align nnreal.coe_indicator NNReal.coe_indicator

/- warning: nnreal.coe_pow -> NNReal.coe_pow is a dubious translation:
lean 3 declaration is
  forall (r : NNReal) (n : Nat), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) r n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) n)
but is expected to have type
  forall (r : NNReal) (n : Nat), Eq.{1} Real (NNReal.toReal (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) r n)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (NNReal.toReal r) n)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_pow NNReal.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (r : ℝ≥0) (n : ℕ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n :=
  toRealHom.map_pow r n
#align nnreal.coe_pow NNReal.coe_pow

/- warning: nnreal.coe_zpow -> NNReal.coe_zpow is a dubious translation:
lean 3 declaration is
  forall (r : NNReal) (n : Int), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) r n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) n)
but is expected to have type
  forall (r : NNReal) (n : Int), Eq.{1} Real (NNReal.toReal (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) r n)) (HPow.hPow.{0, 0, 0} Real Int Real (instHPow.{0, 0} Real Int (DivInvMonoid.Pow.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.instDivisionRingReal))) (NNReal.toReal r) n)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_zpow NNReal.coe_zpowₓ'. -/
@[simp, norm_cast]
theorem coe_zpow (r : ℝ≥0) (n : ℤ) : ((r ^ n : ℝ≥0) : ℝ) = r ^ n := by cases n <;> simp
#align nnreal.coe_zpow NNReal.coe_zpow

/- warning: nnreal.coe_list_sum -> NNReal.coe_list_sum is a dubious translation:
lean 3 declaration is
  forall (l : List.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (List.sum.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) l)) (List.sum.{0} Real Real.hasAdd Real.hasZero (List.map.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) l))
but is expected to have type
  forall (l : List.{0} NNReal), Eq.{1} Real (NNReal.toReal (List.sum.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) instNNRealZero l)) (List.sum.{0} Real Real.instAddReal Real.instZeroReal (List.map.{0, 0} NNReal Real NNReal.toReal l))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_list_sum NNReal.coe_list_sumₓ'. -/
@[norm_cast]
theorem coe_list_sum (l : List ℝ≥0) : ((l.Sum : ℝ≥0) : ℝ) = (l.map coe).Sum :=
  toRealHom.map_list_sum l
#align nnreal.coe_list_sum NNReal.coe_list_sum

/- warning: nnreal.coe_list_prod -> NNReal.coe_list_prod is a dubious translation:
lean 3 declaration is
  forall (l : List.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (List.prod.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) l)) (List.prod.{0} Real Real.hasMul Real.hasOne (List.map.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) l))
but is expected to have type
  forall (l : List.{0} NNReal), Eq.{1} Real (NNReal.toReal (List.prod.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) instNNRealOne l)) (List.prod.{0} Real Real.instMulReal Real.instOneReal (List.map.{0, 0} NNReal Real NNReal.toReal l))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_list_prod NNReal.coe_list_prodₓ'. -/
@[norm_cast]
theorem coe_list_prod (l : List ℝ≥0) : ((l.Prod : ℝ≥0) : ℝ) = (l.map coe).Prod :=
  toRealHom.map_list_prod l
#align nnreal.coe_list_prod NNReal.coe_list_prod

/- warning: nnreal.coe_multiset_sum -> NNReal.coe_multiset_sum is a dubious translation:
lean 3 declaration is
  forall (s : Multiset.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Multiset.sum.{0} NNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) s)) (Multiset.sum.{0} Real Real.addCommMonoid (Multiset.map.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s))
but is expected to have type
  forall (s : Multiset.{0} NNReal), Eq.{1} Real (NNReal.toReal (Multiset.sum.{0} NNReal (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) s)) (Multiset.sum.{0} Real Real.instAddCommMonoidReal (Multiset.map.{0, 0} NNReal Real NNReal.toReal s))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_multiset_sum NNReal.coe_multiset_sumₓ'. -/
@[norm_cast]
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.Sum : ℝ≥0) : ℝ) = (s.map coe).Sum :=
  toRealHom.map_multiset_sum s
#align nnreal.coe_multiset_sum NNReal.coe_multiset_sum

/- warning: nnreal.coe_multiset_prod -> NNReal.coe_multiset_prod is a dubious translation:
lean 3 declaration is
  forall (s : Multiset.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Multiset.prod.{0} NNReal (CommSemiring.toCommMonoid.{0} NNReal NNReal.commSemiring) s)) (Multiset.prod.{0} Real Real.commMonoid (Multiset.map.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s))
but is expected to have type
  forall (s : Multiset.{0} NNReal), Eq.{1} Real (NNReal.toReal (Multiset.prod.{0} NNReal (CommSemiring.toCommMonoid.{0} NNReal instNNRealCommSemiring) s)) (Multiset.prod.{0} Real Real.instCommMonoidReal (Multiset.map.{0, 0} NNReal Real NNReal.toReal s))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_multiset_prod NNReal.coe_multiset_prodₓ'. -/
@[norm_cast]
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.Prod : ℝ≥0) : ℝ) = (s.map coe).Prod :=
  toRealHom.map_multiset_prod s
#align nnreal.coe_multiset_prod NNReal.coe_multiset_prod

/- warning: nnreal.coe_sum -> NNReal.coe_sum is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNReal}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Finset.sum.{0, u1} NNReal α (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) s (fun (a : α) => f a))) (Finset.sum.{0, u1} Real α Real.addCommMonoid s (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNReal}, Eq.{1} Real (NNReal.toReal (Finset.sum.{0, u1} NNReal α (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) s (fun (a : α) => f a))) (Finset.sum.{0, u1} Real α Real.instAddCommMonoidReal s (fun (a : α) => NNReal.toReal (f a)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_sum NNReal.coe_sumₓ'. -/
@[norm_cast]
theorem coe_sum {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
  toRealHom.map_sum _ _
#align nnreal.coe_sum NNReal.coe_sum

/- warning: real.to_nnreal_sum_of_nonneg -> Real.toNNReal_sum_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Real}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f a))) -> (Eq.{1} NNReal (Real.toNNReal (Finset.sum.{0, u1} Real α Real.addCommMonoid s (fun (a : α) => f a))) (Finset.sum.{0, u1} NNReal α (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) s (fun (a : α) => Real.toNNReal (f a))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Real}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f a))) -> (Eq.{1} NNReal (Real.toNNReal (Finset.sum.{0, u1} Real α Real.instAddCommMonoidReal s (fun (a : α) => f a))) (Finset.sum.{0, u1} NNReal α (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) s (fun (a : α) => Real.toNNReal (f a))))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_sum_of_nonneg Real.toNNReal_sum_of_nonnegₓ'. -/
theorem Real.toNNReal_sum_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∑ a in s, f a) = ∑ a in s, Real.toNNReal (f a) :=
  by
  rw [← NNReal.coe_eq, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
#align real.to_nnreal_sum_of_nonneg Real.toNNReal_sum_of_nonneg

/- warning: nnreal.coe_prod -> NNReal.coe_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNReal}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Finset.prod.{0, u1} NNReal α (CommSemiring.toCommMonoid.{0} NNReal NNReal.commSemiring) s (fun (a : α) => f a))) (Finset.prod.{0, u1} Real α Real.commMonoid s (fun (a : α) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (f a)))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> NNReal}, Eq.{1} Real (NNReal.toReal (Finset.prod.{0, u1} NNReal α (CommSemiring.toCommMonoid.{0} NNReal instNNRealCommSemiring) s (fun (a : α) => f a))) (Finset.prod.{0, u1} Real α Real.instCommMonoidReal s (fun (a : α) => NNReal.toReal (f a)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_prod NNReal.coe_prodₓ'. -/
@[norm_cast]
theorem coe_prod {α} {s : Finset α} {f : α → ℝ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
  toRealHom.map_prod _ _
#align nnreal.coe_prod NNReal.coe_prod

/- warning: real.to_nnreal_prod_of_nonneg -> Real.toNNReal_prod_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Real}, (forall (a : α), (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a s) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (f a))) -> (Eq.{1} NNReal (Real.toNNReal (Finset.prod.{0, u1} Real α Real.commMonoid s (fun (a : α) => f a))) (Finset.prod.{0, u1} NNReal α (CommSemiring.toCommMonoid.{0} NNReal NNReal.commSemiring) s (fun (a : α) => Real.toNNReal (f a))))
but is expected to have type
  forall {α : Type.{u1}} {s : Finset.{u1} α} {f : α -> Real}, (forall (a : α), (Membership.mem.{u1, u1} α (Finset.{u1} α) (Finset.instMembershipFinset.{u1} α) a s) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (f a))) -> (Eq.{1} NNReal (Real.toNNReal (Finset.prod.{0, u1} Real α Real.instCommMonoidReal s (fun (a : α) => f a))) (Finset.prod.{0, u1} NNReal α (CommSemiring.toCommMonoid.{0} NNReal instNNRealCommSemiring) s (fun (a : α) => Real.toNNReal (f a))))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_prod_of_nonneg Real.toNNReal_prod_of_nonnegₓ'. -/
theorem Real.toNNReal_prod_of_nonneg {α} {s : Finset α} {f : α → ℝ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a in s, f a) = ∏ a in s, Real.toNNReal (f a) :=
  by
  rw [← NNReal.coe_eq, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
#align real.to_nnreal_prod_of_nonneg Real.toNNReal_prod_of_nonneg

/- warning: nnreal.nsmul_coe -> NNReal.coe_nsmul is a dubious translation:
lean 3 declaration is
  forall (r : NNReal) (n : Nat), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (SMul.smul.{0, 0} Nat NNReal (AddMonoid.SMul.{0} NNReal (AddMonoidWithOne.toAddMonoid.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) n r)) (SMul.smul.{0, 0} Nat Real (AddMonoid.SMul.{0} Real Real.addMonoid) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r))
but is expected to have type
  forall (r : NNReal) (n : Nat), Eq.{1} Real (NNReal.toReal (HSMul.hSMul.{0, 0, 0} Nat NNReal NNReal (instHSMul.{0, 0} Nat NNReal (AddMonoid.SMul.{0} NNReal (AddMonoidWithOne.toAddMonoid.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) n r)) (HSMul.hSMul.{0, 0, 0} Nat Real Real (instHSMul.{0, 0} Nat Real (AddMonoid.SMul.{0} Real Real.instAddMonoidReal)) n (NNReal.toReal r))
Case conversion may be inaccurate. Consider using '#align nnreal.nsmul_coe NNReal.coe_nsmulₓ'. -/
theorem coe_nsmul (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r : ℝ) := by norm_cast
#align nnreal.nsmul_coe NNReal.coe_nsmul

/- warning: nnreal.coe_nat_cast -> NNReal.coe_nat_cast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} Real (NNReal.toReal (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n)) (Nat.cast.{0} Real Real.natCast n)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_nat_cast NNReal.coe_nat_castₓ'. -/
@[simp, norm_cast]
protected theorem coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
  map_natCast toRealHom n
#align nnreal.coe_nat_cast NNReal.coe_nat_cast

noncomputable example : LinearOrder ℝ≥0 := by infer_instance

/- warning: nnreal.coe_le_coe -> NNReal.coe_le_coe is a dubious translation:
lean 3 declaration is
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r₁ r₂)
but is expected to have type
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (LE.le.{0} Real Real.instLEReal (NNReal.toReal r₁) (NNReal.toReal r₂)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r₁ r₂)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_le_coe NNReal.coe_le_coeₓ'. -/
@[simp, norm_cast]
protected theorem coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ :=
  Iff.rfl
#align nnreal.coe_le_coe NNReal.coe_le_coe

/- warning: nnreal.coe_lt_coe -> NNReal.coe_lt_coe is a dubious translation:
lean 3 declaration is
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (LT.lt.{0} Real Real.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r₂)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r₁ r₂)
but is expected to have type
  forall {r₁ : NNReal} {r₂ : NNReal}, Iff (LT.lt.{0} Real Real.instLTReal (NNReal.toReal r₁) (NNReal.toReal r₂)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r₁ r₂)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_lt_coe NNReal.coe_lt_coeₓ'. -/
@[simp, norm_cast]
protected theorem coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ :=
  Iff.rfl
#align nnreal.coe_lt_coe NNReal.coe_lt_coe

/- warning: nnreal.coe_pos -> NNReal.coe_pos is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r)
but is expected to have type
  forall {r : NNReal}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r)
Case conversion may be inaccurate. Consider using '#align nnreal.coe_pos NNReal.coe_posₓ'. -/
@[simp, norm_cast]
protected theorem coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r :=
  Iff.rfl
#align nnreal.coe_pos NNReal.coe_pos

/- warning: nnreal.coe_mono -> NNReal.coe_mono is a dubious translation:
lean 3 declaration is
  Monotone.{0, 0} NNReal Real (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) Real.preorder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))))
but is expected to have type
  Monotone.{0, 0} NNReal Real (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) Real.instPreorderReal NNReal.toReal
Case conversion may be inaccurate. Consider using '#align nnreal.coe_mono NNReal.coe_monoₓ'. -/
protected theorem coe_mono : Monotone (coe : ℝ≥0 → ℝ) := fun _ _ => NNReal.coe_le_coe.2
#align nnreal.coe_mono NNReal.coe_mono

#print Real.toNNReal_mono /-
protected theorem Real.toNNReal_mono : Monotone Real.toNNReal := fun x y h =>
  max_le_max h (le_refl 0)
#align real.to_nnreal_mono Real.toNNReal_mono
-/

/- warning: real.to_nnreal_coe -> Real.toNNReal_coe is a dubious translation:
lean 3 declaration is
  forall {r : NNReal}, Eq.{1} NNReal (Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r)) r
but is expected to have type
  forall {r : NNReal}, Eq.{1} NNReal (Real.toNNReal (NNReal.toReal r)) r
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_coe Real.toNNReal_coeₓ'. -/
@[simp]
theorem Real.toNNReal_coe {r : ℝ≥0} : Real.toNNReal r = r :=
  NNReal.eq <| max_eq_left r.2
#align real.to_nnreal_coe Real.toNNReal_coe

/- warning: nnreal.mk_coe_nat -> NNReal.mk_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} NNReal (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n) (Nat.cast_nonneg.{0} Real Real.orderedSemiring n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} NNReal (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (Nat.cast.{0} Real Real.natCast n) (Nat.cast_nonneg.{0} Real Real.orderedSemiring n)) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n)
Case conversion may be inaccurate. Consider using '#align nnreal.mk_coe_nat NNReal.mk_coe_natₓ'. -/
@[simp]
theorem mk_coe_nat (n : ℕ) : @Eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
  NNReal.eq (NNReal.coe_nat_cast n).symm
#align nnreal.mk_coe_nat NNReal.mk_coe_nat

/- warning: nnreal.to_nnreal_coe_nat -> NNReal.toNNReal_coe_nat is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} NNReal (Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} NNReal (Real.toNNReal (Nat.cast.{0} Real Real.natCast n)) (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) n)
Case conversion may be inaccurate. Consider using '#align nnreal.to_nnreal_coe_nat NNReal.toNNReal_coe_natₓ'. -/
@[simp]
theorem toNNReal_coe_nat (n : ℕ) : Real.toNNReal n = n :=
  NNReal.eq <| by simp [Real.coe_toNNReal]
#align nnreal.to_nnreal_coe_nat NNReal.toNNReal_coe_nat

/- warning: nnreal.gi -> NNReal.gi is a dubious translation:
lean 3 declaration is
  GaloisInsertion.{0, 0} Real NNReal Real.preorder (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))))
but is expected to have type
  GaloisInsertion.{0, 0} Real NNReal Real.instPreorderReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) Real.toNNReal NNReal.toReal
Case conversion may be inaccurate. Consider using '#align nnreal.gi NNReal.giₓ'. -/
/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
noncomputable def gi : GaloisInsertion Real.toNNReal coe :=
  GaloisInsertion.monotoneIntro NNReal.coe_mono Real.toNNReal_mono Real.le_coe_toNNReal fun _ =>
    Real.toNNReal_coe
#align nnreal.gi NNReal.gi

-- note that anything involving the (decidability of the) linear order,
-- will be noncomputable, everything else should not be.
example : OrderBot ℝ≥0 := by infer_instance

example : PartialOrder ℝ≥0 := by infer_instance

noncomputable example : CanonicallyLinearOrderedAddMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedAddCommMonoid ℝ≥0 := by infer_instance

example : DistribLattice ℝ≥0 := by infer_instance

example : SemilatticeInf ℝ≥0 := by infer_instance

example : SemilatticeSup ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedSemiring ℝ≥0 := by infer_instance

example : OrderedCommSemiring ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoid ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommMonoidWithZero ℝ≥0 := by infer_instance

noncomputable example : LinearOrderedCommGroupWithZero ℝ≥0 := by infer_instance

example : CanonicallyOrderedCommSemiring ℝ≥0 := by infer_instance

example : DenselyOrdered ℝ≥0 := by infer_instance

example : NoMaxOrder ℝ≥0 := by infer_instance

/- warning: nnreal.order_iso_Icc_zero_coe -> NNReal.orderIsoIccZeroCoe is a dubious translation:
lean 3 declaration is
  forall (a : NNReal), OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a)))) (Subtype.hasLe.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)))
but is expected to have type
  forall (a : NNReal), OrderIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) (Subtype.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)))
Case conversion may be inaccurate. Consider using '#align nnreal.order_iso_Icc_zero_coe NNReal.orderIsoIccZeroCoeₓ'. -/
/-- If `a` is a nonnegative real number, then the closed interval `[0, a]` in `ℝ` is order
isomorphic to the interval `set.Iic a`. -/
@[simps apply_coe_coe]
def orderIsoIccZeroCoe (a : ℝ≥0) : Set.Icc (0 : ℝ) a ≃o Set.Iic a
    where
  toEquiv := Equiv.Set.sep (Set.Ici 0) fun x => x ≤ a
  map_rel_iff' x y := Iff.rfl
#align nnreal.order_iso_Icc_zero_coe NNReal.orderIsoIccZeroCoe

/- warning: nnreal.order_iso_Icc_zero_coe_symm_apply_coe -> NNReal.orderIsoIccZeroCoe_symm_apply_coe is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))))))) (coeFn.{1, 1} (OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (Subtype.hasLe.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))))) (fun (_x : RelIso.{0, 0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (Subtype.hasLe.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a)))))) => (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a)))) (RelIso.hasCoeToFun.{0, 0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (Subtype.hasLe.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a)))))) (OrderIso.symm.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a))) (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) a)))) (Subtype.hasLe.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a))) (NNReal.orderIsoIccZeroCoe a)) b)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) Real (coeTrans.{1, 1, 1} (coeSort.{1, 2} (Set.{0} NNReal) Type (Set.hasCoeToSort.{0} NNReal) (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)) NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe) (coeSubtype.{1} NNReal (fun (x : NNReal) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) a)))))) b)
but is expected to have type
  forall (a : NNReal) (b : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)), Eq.{1} Real (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (FunLike.coe.{1, 1, 1} (Function.Embedding.{1, 1} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (fun (_x : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) => (fun (x._@.Mathlib.Data.FunLike.Embedding._hyg.19 : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) => Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) _x) (EmbeddingLike.toFunLike.{1, 1, 1} (Function.Embedding.{1, 1} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (Function.instEmbeddingLikeEmbedding.{1, 1} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))))) (RelEmbedding.toEmbedding.{0, 0} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) => LE.le.{0} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Subtype.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.toRelEmbedding.{0, 0} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) => LE.le.{0} (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Subtype.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (OrderIso.symm.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a))) (Set.Elem.{0} NNReal (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal a)))) (Subtype.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a))) (NNReal.orderIsoIccZeroCoe a)))) b)) (NNReal.toReal (Subtype.val.{1} NNReal (fun (x : NNReal) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Iic.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) a)) b))
Case conversion may be inaccurate. Consider using '#align nnreal.order_iso_Icc_zero_coe_symm_apply_coe NNReal.orderIsoIccZeroCoe_symm_apply_coeₓ'. -/
@[simp]
theorem orderIsoIccZeroCoe_symm_apply_coe (a : ℝ≥0) (b : Set.Iic a) :
    ((orderIsoIccZeroCoe a).symm b : ℝ) = b :=
  rfl
#align nnreal.order_iso_Icc_zero_coe_symm_apply_coe NNReal.orderIsoIccZeroCoe_symm_apply_coe

/- warning: nnreal.coe_image -> NNReal.coe_image is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} NNReal}, Eq.{1} (Set.{0} Real) (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s) (setOf.{0} Real (fun (x : Real) => Exists.{0} (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) (fun (h : LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) x h) s)))
but is expected to have type
  forall {s : Set.{0} NNReal}, Eq.{1} (Set.{0} Real) (Set.image.{0, 0} NNReal Real NNReal.toReal s) (setOf.{0} Real (fun (x : Real) => Exists.{0} (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) (fun (h : LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) (Subtype.mk.{1} Real (fun (r : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) x h) s)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_image NNReal.coe_imageₓ'. -/
-- note we need the `@` to make the `has_mem.mem` have a sensible type
theorem coe_image {s : Set ℝ≥0} :
    coe '' s = { x : ℝ | ∃ h : 0 ≤ x, @Membership.Mem ℝ≥0 _ _ ⟨x, h⟩ s } :=
  Subtype.coe_image
#align nnreal.coe_image NNReal.coe_image

/- warning: nnreal.bdd_above_coe -> NNReal.bddAbove_coe is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} NNReal}, Iff (BddAbove.{0} Real Real.preorder (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s)) (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) s)
but is expected to have type
  forall {s : Set.{0} NNReal}, Iff (BddAbove.{0} Real Real.instPreorderReal (Set.image.{0, 0} NNReal Real NNReal.toReal s)) (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) s)
Case conversion may be inaccurate. Consider using '#align nnreal.bdd_above_coe NNReal.bddAbove_coeₓ'. -/
theorem bddAbove_coe {s : Set ℝ≥0} : BddAbove ((coe : ℝ≥0 → ℝ) '' s) ↔ BddAbove s :=
  Iff.intro
    (fun ⟨b, hb⟩ =>
      ⟨Real.toNNReal b, fun ⟨y, hy⟩ hys =>
        show y ≤ max b 0 from le_max_of_le_left <| hb <| Set.mem_image_of_mem _ hys⟩)
    fun ⟨b, hb⟩ => ⟨b, fun y ⟨x, hx, Eq⟩ => Eq ▸ hb hx⟩
#align nnreal.bdd_above_coe NNReal.bddAbove_coe

/- warning: nnreal.bdd_below_coe -> NNReal.bddBelow_coe is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} NNReal), BddBelow.{0} Real Real.preorder (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s)
but is expected to have type
  forall (s : Set.{0} NNReal), BddBelow.{0} Real Real.instPreorderReal (Set.image.{0, 0} NNReal Real NNReal.toReal s)
Case conversion may be inaccurate. Consider using '#align nnreal.bdd_below_coe NNReal.bddBelow_coeₓ'. -/
theorem bddBelow_coe (s : Set ℝ≥0) : BddBelow ((coe : ℝ≥0 → ℝ) '' s) :=
  ⟨0, fun r ⟨q, _, Eq⟩ => Eq ▸ q.2⟩
#align nnreal.bdd_below_coe NNReal.bddBelow_coe

noncomputable instance : ConditionallyCompleteLinearOrderBot ℝ≥0 :=
  Nonneg.conditionallyCompleteLinearOrderBot Real.supₛ_empty.le

/- warning: nnreal.coe_Sup -> NNReal.coe_supₛ is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (SupSet.supₛ.{0} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) s)) (SupSet.supₛ.{0} Real Real.hasSup (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s))
but is expected to have type
  forall (s : Set.{0} NNReal), Eq.{1} Real (NNReal.toReal (SupSet.supₛ.{0} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) s)) (SupSet.supₛ.{0} Real Real.instSupSetReal (Set.image.{0, 0} NNReal Real NNReal.toReal s))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_Sup NNReal.coe_supₛₓ'. -/
@[norm_cast]
theorem coe_supₛ (s : Set ℝ≥0) : (↑(supₛ s) : ℝ) = supₛ ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_supₛ_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.supₛ_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Sup NNReal.coe_supₛ

/- warning: nnreal.coe_supr -> NNReal.coe_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (s : ι -> NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => s i))) (supᵢ.{0, u1} Real Real.hasSup ι (fun (i : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (s i)))
but is expected to have type
  forall {ι : Sort.{u1}} (s : ι -> NNReal), Eq.{1} Real (NNReal.toReal (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => s i))) (supᵢ.{0, u1} Real Real.instSupSetReal ι (fun (i : ι) => NNReal.toReal (s i)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_supr NNReal.coe_supᵢₓ'. -/
@[norm_cast]
theorem coe_supᵢ {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨆ i, s i) : ℝ) = ⨆ i, s i := by
  rw [supᵢ, supᵢ, coe_Sup, Set.range_comp]
#align nnreal.coe_supr NNReal.coe_supᵢ

/- warning: nnreal.coe_Inf -> NNReal.coe_infₛ is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (InfSet.infₛ.{0} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) s)) (InfSet.infₛ.{0} Real Real.hasInf (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s))
but is expected to have type
  forall (s : Set.{0} NNReal), Eq.{1} Real (NNReal.toReal (InfSet.infₛ.{0} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) s)) (InfSet.infₛ.{0} Real Real.instInfSetReal (Set.image.{0, 0} NNReal Real NNReal.toReal s))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_Inf NNReal.coe_infₛₓ'. -/
@[norm_cast]
theorem coe_infₛ (s : Set ℝ≥0) : (↑(infₛ s) : ℝ) = infₛ ((coe : ℝ≥0 → ℝ) '' s) :=
  Eq.symm <|
    @subset_infₛ_of_within ℝ (Set.Ici 0) _ ⟨(0 : ℝ≥0)⟩ s <|
      Real.infₛ_nonneg _ fun y ⟨x, _, hy⟩ => hy ▸ x.2
#align nnreal.coe_Inf NNReal.coe_infₛ

/- warning: nnreal.Inf_empty -> NNReal.infₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (InfSet.infₛ.{0} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) (EmptyCollection.emptyCollection.{0} (Set.{0} NNReal) (Set.hasEmptyc.{0} NNReal))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} NNReal (InfSet.infₛ.{0} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) (EmptyCollection.emptyCollection.{0} (Set.{0} NNReal) (Set.instEmptyCollectionSet.{0} NNReal))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.Inf_empty NNReal.infₛ_emptyₓ'. -/
@[simp]
theorem infₛ_empty : infₛ (∅ : Set ℝ≥0) = 0 := by
  rw [← NNReal.coe_eq_zero, coe_Inf, Set.image_empty, Real.infₛ_empty]
#align nnreal.Inf_empty NNReal.infₛ_empty

/- warning: nnreal.coe_infi -> NNReal.coe_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (s : ι -> NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => s i))) (infᵢ.{0, u1} Real Real.hasInf ι (fun (i : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (s i)))
but is expected to have type
  forall {ι : Sort.{u1}} (s : ι -> NNReal), Eq.{1} Real (NNReal.toReal (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => s i))) (infᵢ.{0, u1} Real Real.instInfSetReal ι (fun (i : ι) => NNReal.toReal (s i)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_infi NNReal.coe_infᵢₓ'. -/
@[norm_cast]
theorem coe_infᵢ {ι : Sort _} (s : ι → ℝ≥0) : (↑(⨅ i, s i) : ℝ) = ⨅ i, s i := by
  rw [infᵢ, infᵢ, coe_Inf, Set.range_comp]
#align nnreal.coe_infi NNReal.coe_infᵢ

/- warning: nnreal.le_infi_add_infi -> NNReal.le_infᵢ_add_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {ι' : Sort.{u2}} [_inst_1 : Nonempty.{u1} ι] [_inst_2 : Nonempty.{u2} ι'] {f : ι -> NNReal} {g : ι' -> NNReal} {a : NNReal}, (forall (i : ι) (j : ι'), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f i) (g j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i)) (infᵢ.{0, u2} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι' (fun (j : ι') => g j))))
but is expected to have type
  forall {ι : Sort.{u2}} {ι' : Sort.{u1}} [_inst_1 : Nonempty.{u2} ι] [_inst_2 : Nonempty.{u1} ι'] {f : ι -> NNReal} {g : ι' -> NNReal} {a : NNReal}, (forall (i : ι) (j : ι'), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (f i) (g j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (infᵢ.{0, u2} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι' (fun (j : ι') => g j))))
Case conversion may be inaccurate. Consider using '#align nnreal.le_infi_add_infi NNReal.le_infᵢ_add_infᵢₓ'. -/
theorem le_infᵢ_add_infᵢ {ι ι' : Sort _} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j :=
  by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_infi, coe_infi]
  exact le_cinfᵢ_add_cinfᵢ h
#align nnreal.le_infi_add_infi NNReal.le_infᵢ_add_infᵢ

example : Archimedean ℝ≥0 := by infer_instance

/- warning: nnreal.covariant_add -> NNReal.covariant_add is a dubious translation:
lean 3 declaration is
  CovariantClass.{0, 0} NNReal NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  CovariantClass.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4047 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4049 : NNReal) => HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) x._@.Mathlib.Data.Real.NNReal._hyg.4047 x._@.Mathlib.Data.Real.NNReal._hyg.4049) (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4062 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4064 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Data.Real.NNReal._hyg.4062 x._@.Mathlib.Data.Real.NNReal._hyg.4064)
Case conversion may be inaccurate. Consider using '#align nnreal.covariant_add NNReal.covariant_addₓ'. -/
-- TODO: why are these three instances necessary? why aren't they inferred?
instance covariant_add : CovariantClass ℝ≥0 ℝ≥0 (· + ·) (· ≤ ·) :=
  OrderedAddCommMonoid.to_covariantClass_left ℝ≥0
#align nnreal.covariant_add NNReal.covariant_add

/- warning: nnreal.contravariant_add -> NNReal.contravariant_add is a dubious translation:
lean 3 declaration is
  ContravariantClass.{0, 0} NNReal NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  ContravariantClass.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4087 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4089 : NNReal) => HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) x._@.Mathlib.Data.Real.NNReal._hyg.4087 x._@.Mathlib.Data.Real.NNReal._hyg.4089) (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4102 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4104 : NNReal) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Data.Real.NNReal._hyg.4102 x._@.Mathlib.Data.Real.NNReal._hyg.4104)
Case conversion may be inaccurate. Consider using '#align nnreal.contravariant_add NNReal.contravariant_addₓ'. -/
instance contravariant_add : ContravariantClass ℝ≥0 ℝ≥0 (· + ·) (· < ·) :=
  OrderedCancelAddCommMonoid.to_contravariantClass_left ℝ≥0
#align nnreal.contravariant_add NNReal.contravariant_add

/- warning: nnreal.covariant_mul -> NNReal.covariant_mul is a dubious translation:
lean 3 declaration is
  CovariantClass.{0, 0} NNReal NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))))
but is expected to have type
  CovariantClass.{0, 0} NNReal NNReal (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4127 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4129 : NNReal) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) x._@.Mathlib.Data.Real.NNReal._hyg.4127 x._@.Mathlib.Data.Real.NNReal._hyg.4129) (fun (x._@.Mathlib.Data.Real.NNReal._hyg.4142 : NNReal) (x._@.Mathlib.Data.Real.NNReal._hyg.4144 : NNReal) => LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x._@.Mathlib.Data.Real.NNReal._hyg.4142 x._@.Mathlib.Data.Real.NNReal._hyg.4144)
Case conversion may be inaccurate. Consider using '#align nnreal.covariant_mul NNReal.covariant_mulₓ'. -/
instance covariant_mul : CovariantClass ℝ≥0 ℝ≥0 (· * ·) (· ≤ ·) :=
  OrderedCommMonoid.to_covariantClass_left ℝ≥0
#align nnreal.covariant_mul NNReal.covariant_mul

/- warning: nnreal.le_of_forall_pos_le_add -> NNReal.le_of_forall_pos_le_add is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal}, (forall (ε : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) ε) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b ε))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a b)
but is expected to have type
  forall {a : NNReal} {b : NNReal}, (forall (ε : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) ε) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) b ε))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a b)
Case conversion may be inaccurate. Consider using '#align nnreal.le_of_forall_pos_le_add NNReal.le_of_forall_pos_le_addₓ'. -/
-- Why isn't `nnreal.contravariant_add` inferred?
theorem le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
  @le_of_forall_pos_le_add _ _ _ _ _ _ NNReal.contravariant_add _ _ h
#align nnreal.le_of_forall_pos_le_add NNReal.le_of_forall_pos_le_add

/- warning: nnreal.lt_iff_exists_rat_btwn -> NNReal.lt_iff_exists_rat_btwn is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal), Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a b) (Exists.{1} Rat (fun (q : Rat) => And (LE.le.{0} Rat Rat.hasLe (OfNat.ofNat.{0} Rat 0 (OfNat.mk.{0} Rat 0 (Zero.zero.{0} Rat Rat.hasZero))) q) (And (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q))) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q)) b))))
but is expected to have type
  forall (a : NNReal) (b : NNReal), Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a b) (Exists.{1} Rat (fun (q : Rat) => And (LE.le.{0} Rat Rat.instLERat (OfNat.ofNat.{0} Rat 0 (Rat.instOfNatRat 0)) q) (And (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (Real.toNNReal (RatCast.ratCast.{0} Real Real.ratCast q))) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal (RatCast.ratCast.{0} Real Real.ratCast q)) b))))
Case conversion may be inaccurate. Consider using '#align nnreal.lt_iff_exists_rat_btwn NNReal.lt_iff_exists_rat_btwnₓ'. -/
theorem lt_iff_exists_rat_btwn (a b : ℝ≥0) :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b :=
  Iff.intro
    (fun h : (↑a : ℝ) < (↑b : ℝ) =>
      let ⟨q, haq, hqb⟩ := exists_rat_btwn h
      have : 0 ≤ (q : ℝ) := le_trans a.2 <| le_of_lt haq
      ⟨q, Rat.cast_nonneg.1 this, by
        simp [Real.coe_toNNReal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
    fun ⟨q, _, haq, hqb⟩ => lt_trans haq hqb
#align nnreal.lt_iff_exists_rat_btwn NNReal.lt_iff_exists_rat_btwn

/- warning: nnreal.bot_eq_zero -> NNReal.bot_eq_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (Bot.bot.{0} NNReal (CanonicallyOrderedAddMonoid.toHasBot.{0} NNReal (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} NNReal NNReal.canonicallyOrderedCommSemiring))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} NNReal (Bot.bot.{0} NNReal (CanonicallyOrderedAddMonoid.toBot.{0} NNReal (CanonicallyOrderedCommSemiring.toCanonicallyOrderedAddMonoid.{0} NNReal instNNRealCanonicallyOrderedCommSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.bot_eq_zero NNReal.bot_eq_zeroₓ'. -/
theorem bot_eq_zero : (⊥ : ℝ≥0) = 0 :=
  rfl
#align nnreal.bot_eq_zero NNReal.bot_eq_zero

/- warning: nnreal.mul_sup -> NNReal.mul_sup is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (Sup.sup.{0} NNReal (SemilatticeSup.toHasSup.{0} NNReal NNReal.semilatticeSup) b c)) (Sup.sup.{0} NNReal (SemilatticeSup.toHasSup.{0} NNReal NNReal.semilatticeSup) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a b) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a c))
but is expected to have type
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (Sup.sup.{0} NNReal (SemilatticeSup.toSup.{0} NNReal instNNRealSemilatticeSup) b c)) (Sup.sup.{0} NNReal (SemilatticeSup.toSup.{0} NNReal instNNRealSemilatticeSup) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a b) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a c))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_sup NNReal.mul_supₓ'. -/
theorem mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = a * b ⊔ a * c :=
  mul_max_of_nonneg _ _ <| zero_le a
#align nnreal.mul_sup NNReal.mul_sup

/- warning: nnreal.sup_mul -> NNReal.sup_mul is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Sup.sup.{0} NNReal (SemilatticeSup.toHasSup.{0} NNReal NNReal.semilatticeSup) a b) c) (Sup.sup.{0} NNReal (SemilatticeSup.toHasSup.{0} NNReal NNReal.semilatticeSup) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a c) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b c))
but is expected to have type
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Sup.sup.{0} NNReal (SemilatticeSup.toSup.{0} NNReal instNNRealSemilatticeSup) a b) c) (Sup.sup.{0} NNReal (SemilatticeSup.toSup.{0} NNReal instNNRealSemilatticeSup) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a c) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) b c))
Case conversion may be inaccurate. Consider using '#align nnreal.sup_mul NNReal.sup_mulₓ'. -/
theorem sup_mul (a b c : ℝ≥0) : (a ⊔ b) * c = a * c ⊔ b * c :=
  max_mul_of_nonneg _ _ <| zero_le c
#align nnreal.sup_mul NNReal.sup_mul

/- warning: nnreal.mul_finset_sup -> NNReal.mul_finset_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (r : NNReal) (s : Finset.{u1} α) (f : α -> NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s f)) (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s (fun (a : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r (f a)))
but is expected to have type
  forall {α : Type.{u1}} (r : NNReal) (s : Finset.{u1} α) (f : α -> NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s f)) (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s (fun (a : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r (f a)))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_finset_sup NNReal.mul_finset_supₓ'. -/
theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.comp_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)
#align nnreal.mul_finset_sup NNReal.mul_finset_sup

/- warning: nnreal.finset_sup_mul -> NNReal.finset_sup_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> NNReal) (r : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s f) r) (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s (fun (a : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f a) r))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α) (f : α -> NNReal) (r : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s f) r) (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s (fun (a : α) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (f a) r))
Case conversion may be inaccurate. Consider using '#align nnreal.finset_sup_mul NNReal.finset_sup_mulₓ'. -/
theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.comp_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)
#align nnreal.finset_sup_mul NNReal.finset_sup_mul

/- warning: nnreal.finset_sup_div -> NNReal.finset_sup_div is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {f : α -> NNReal} {s : Finset.{u1} α} (r : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s f) r) (Finset.sup.{0, u1} NNReal α NNReal.semilatticeSup NNReal.orderBot s (fun (a : α) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (f a) r))
but is expected to have type
  forall {α : Type.{u1}} {f : α -> NNReal} {s : Finset.{u1} α} (r : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s f) r) (Finset.sup.{0, u1} NNReal α instNNRealSemilatticeSup NNReal.instOrderBotNNRealToLEToPreorderToPartialOrderInstNNRealStrictOrderedSemiring s (fun (a : α) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (f a) r))
Case conversion may be inaccurate. Consider using '#align nnreal.finset_sup_div NNReal.finset_sup_divₓ'. -/
theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]
#align nnreal.finset_sup_div NNReal.finset_sup_div

/- warning: nnreal.coe_max -> NNReal.coe_max is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (LinearOrder.max.{0} NNReal (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{0} NNReal (CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)) x y)) (LinearOrder.max.{0} Real Real.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) y))
but is expected to have type
  forall (x : NNReal) (y : NNReal), Eq.{1} Real (NNReal.toReal (Max.max.{0} NNReal (CanonicallyLinearOrderedSemifield.toMax.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x y)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (NNReal.toReal x) (NNReal.toReal y))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_max NNReal.coe_maxₓ'. -/
@[simp, norm_cast]
theorem coe_max (x y : ℝ≥0) : ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_max
#align nnreal.coe_max NNReal.coe_max

/- warning: nnreal.coe_min -> NNReal.coe_min is a dubious translation:
lean 3 declaration is
  forall (x : NNReal) (y : NNReal), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (LinearOrder.min.{0} NNReal (CanonicallyLinearOrderedAddMonoid.toLinearOrder.{0} NNReal (CanonicallyLinearOrderedSemifield.toCanonicallyLinearOrderedAddMonoid.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)) x y)) (LinearOrder.min.{0} Real Real.linearOrder ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) y))
but is expected to have type
  forall (x : NNReal) (y : NNReal), Eq.{1} Real (NNReal.toReal (Min.min.{0} NNReal (CanonicallyLinearOrderedSemifield.toMin.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x y)) (Min.min.{0} Real (LinearOrderedRing.toMin.{0} Real Real.instLinearOrderedRingReal) (NNReal.toReal x) (NNReal.toReal y))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_min NNReal.coe_minₓ'. -/
@[simp, norm_cast]
theorem coe_min (x y : ℝ≥0) : ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
  NNReal.coe_mono.map_min
#align nnreal.coe_min NNReal.coe_min

/- warning: nnreal.zero_le_coe -> NNReal.zero_le_coe is a dubious translation:
lean 3 declaration is
  forall {q : NNReal}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) q)
but is expected to have type
  forall {q : NNReal}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (NNReal.toReal q)
Case conversion may be inaccurate. Consider using '#align nnreal.zero_le_coe NNReal.zero_le_coeₓ'. -/
@[simp]
theorem zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) :=
  q.2
#align nnreal.zero_le_coe NNReal.zero_le_coe

end NNReal

namespace Real

section ToNnreal

/- warning: real.to_nnreal_zero -> Real.toNNReal_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (Real.toNNReal (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} NNReal (Real.toNNReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_zero Real.toNNReal_zeroₓ'. -/
@[simp]
theorem toNNReal_zero : Real.toNNReal 0 = 0 := by simp [Real.toNNReal] <;> rfl
#align real.to_nnreal_zero Real.toNNReal_zero

/- warning: real.to_nnreal_one -> Real.toNNReal_one is a dubious translation:
lean 3 declaration is
  Eq.{1} NNReal (Real.toNNReal (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Eq.{1} NNReal (Real.toNNReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_one Real.toNNReal_oneₓ'. -/
@[simp]
theorem toNNReal_one : Real.toNNReal 1 = 1 := by
  simp [Real.toNNReal, max_eq_left (zero_le_one : (0 : ℝ) ≤ 1)] <;> rfl
#align real.to_nnreal_one Real.toNNReal_one

/- warning: real.to_nnreal_pos -> Real.toNNReal_pos is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Real.toNNReal r)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r)
but is expected to have type
  forall {r : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (Real.toNNReal r)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r)
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_pos Real.toNNReal_posₓ'. -/
@[simp]
theorem toNNReal_pos {r : ℝ} : 0 < Real.toNNReal r ↔ 0 < r := by
  simp [Real.toNNReal, nnreal.coe_lt_coe.symm, lt_irrefl]
#align real.to_nnreal_pos Real.toNNReal_pos

/- warning: real.to_nnreal_eq_zero -> Real.toNNReal_eq_zero is a dubious translation:
lean 3 declaration is
  forall {r : Real}, Iff (Eq.{1} NNReal (Real.toNNReal r) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LE.le.{0} Real Real.hasLe r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {r : Real}, Iff (Eq.{1} NNReal (Real.toNNReal r) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (LE.le.{0} Real Real.instLEReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_eq_zero Real.toNNReal_eq_zeroₓ'. -/
@[simp]
theorem toNNReal_eq_zero {r : ℝ} : Real.toNNReal r = 0 ↔ r ≤ 0 := by
  simpa [-to_nnreal_pos] using not_iff_not.2 (@to_nnreal_pos r)
#align real.to_nnreal_eq_zero Real.toNNReal_eq_zero

/- warning: real.to_nnreal_of_nonpos -> Real.toNNReal_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LE.le.{0} Real Real.hasLe r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} NNReal (Real.toNNReal r) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {r : Real}, (LE.le.{0} Real Real.instLEReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} NNReal (Real.toNNReal r) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_of_nonpos Real.toNNReal_of_nonposₓ'. -/
theorem toNNReal_of_nonpos {r : ℝ} : r ≤ 0 → Real.toNNReal r = 0 :=
  toNNReal_eq_zero.2
#align real.to_nnreal_of_nonpos Real.toNNReal_of_nonpos

/- warning: real.coe_to_nnreal' -> Real.coe_toNNReal' is a dubious translation:
lean 3 declaration is
  forall (r : Real), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Real.toNNReal r)) (LinearOrder.max.{0} Real Real.linearOrder r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (r : Real), Eq.{1} Real (NNReal.toReal (Real.toNNReal r)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.coe_to_nnreal' Real.coe_toNNReal'ₓ'. -/
@[simp]
theorem coe_toNNReal' (r : ℝ) : (Real.toNNReal r : ℝ) = max r 0 :=
  rfl
#align real.coe_to_nnreal' Real.coe_toNNReal'

/- warning: real.to_nnreal_le_to_nnreal_iff -> Real.toNNReal_le_toNNReal_iff is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) (Real.toNNReal p)) (LE.le.{0} Real Real.hasLe r p))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) (Real.toNNReal p)) (LE.le.{0} Real Real.instLEReal r p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_le_to_nnreal_iff Real.toNNReal_le_toNNReal_iffₓ'. -/
@[simp]
theorem toNNReal_le_toNNReal_iff {r p : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal r ≤ Real.toNNReal p ↔ r ≤ p := by simp [nnreal.coe_le_coe.symm, Real.toNNReal, hp]
#align real.to_nnreal_le_to_nnreal_iff Real.toNNReal_le_toNNReal_iff

/- warning: real.to_nnreal_eq_to_nnreal_iff -> Real.toNNReal_eq_toNNReal_iff is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Iff (Eq.{1} NNReal (Real.toNNReal r) (Real.toNNReal p)) (Eq.{1} Real r p))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Iff (Eq.{1} NNReal (Real.toNNReal r) (Real.toNNReal p)) (Eq.{1} Real r p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_eq_to_nnreal_iff Real.toNNReal_eq_toNNReal_iffₓ'. -/
@[simp]
theorem toNNReal_eq_toNNReal_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r = Real.toNNReal p ↔ r = p := by simp [← NNReal.coe_eq, coe_to_nnreal, hr, hp]
#align real.to_nnreal_eq_to_nnreal_iff Real.toNNReal_eq_toNNReal_iff

/- warning: real.to_nnreal_lt_to_nnreal_iff' -> Real.toNNReal_lt_toNNReal_iff' is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) (Real.toNNReal p)) (And (LT.lt.{0} Real Real.hasLt r p) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p))
but is expected to have type
  forall {r : Real} {p : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) (Real.toNNReal p)) (And (LT.lt.{0} Real Real.instLTReal r p) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_lt_to_nnreal_iff' Real.toNNReal_lt_toNNReal_iff'ₓ'. -/
@[simp]
theorem toNNReal_lt_toNNReal_iff' {r p : ℝ} : Real.toNNReal r < Real.toNNReal p ↔ r < p ∧ 0 < p :=
  NNReal.coe_lt_coe.symm.trans max_lt_max_left_iff
#align real.to_nnreal_lt_to_nnreal_iff' Real.toNNReal_lt_toNNReal_iff'

/- warning: real.to_nnreal_lt_to_nnreal_iff -> Real.toNNReal_lt_toNNReal_iff is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) (Real.toNNReal p)) (LT.lt.{0} Real Real.hasLt r p))
but is expected to have type
  forall {r : Real} {p : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) (Real.toNNReal p)) (LT.lt.{0} Real Real.instLTReal r p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_lt_to_nnreal_iff Real.toNNReal_lt_toNNReal_iffₓ'. -/
theorem toNNReal_lt_toNNReal_iff {r p : ℝ} (h : 0 < p) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans (and_iff_left h)
#align real.to_nnreal_lt_to_nnreal_iff Real.toNNReal_lt_toNNReal_iff

/- warning: real.to_nnreal_lt_to_nnreal_iff_of_nonneg -> Real.toNNReal_lt_toNNReal_iff_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) (Real.toNNReal p)) (LT.lt.{0} Real Real.hasLt r p))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) (Real.toNNReal p)) (LT.lt.{0} Real Real.instLTReal r p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_lt_to_nnreal_iff_of_nonneg Real.toNNReal_lt_toNNReal_iff_of_nonnegₓ'. -/
theorem toNNReal_lt_toNNReal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
    Real.toNNReal r < Real.toNNReal p ↔ r < p :=
  toNNReal_lt_toNNReal_iff'.trans ⟨And.left, fun h => ⟨h, lt_of_le_of_lt hr h⟩⟩
#align real.to_nnreal_lt_to_nnreal_iff_of_nonneg Real.toNNReal_lt_toNNReal_iff_of_nonneg

/- warning: real.to_nnreal_add -> Real.toNNReal_add is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Eq.{1} NNReal (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) r p)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Real.toNNReal r) (Real.toNNReal p)))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Eq.{1} NNReal (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) r p)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (Real.toNNReal r) (Real.toNNReal p)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_add Real.toNNReal_addₓ'. -/
@[simp]
theorem toNNReal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal (r + p) = Real.toNNReal r + Real.toNNReal p :=
  NNReal.eq <| by simp [Real.toNNReal, hr, hp, add_nonneg]
#align real.to_nnreal_add Real.toNNReal_add

/- warning: real.to_nnreal_add_to_nnreal -> Real.toNNReal_add_toNNReal is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Real.toNNReal r) (Real.toNNReal p)) (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) r p)))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (Real.toNNReal r) (Real.toNNReal p)) (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) r p)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_add_to_nnreal Real.toNNReal_add_toNNRealₓ'. -/
theorem toNNReal_add_toNNReal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
    Real.toNNReal r + Real.toNNReal p = Real.toNNReal (r + p) :=
  (Real.toNNReal_add hr hp).symm
#align real.to_nnreal_add_to_nnreal Real.toNNReal_add_toNNReal

/- warning: real.to_nnreal_le_to_nnreal -> Real.toNNReal_le_toNNReal is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.hasLe r p) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) (Real.toNNReal p))
but is expected to have type
  forall {r : Real} {p : Real}, (LE.le.{0} Real Real.instLEReal r p) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) (Real.toNNReal p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_le_to_nnreal Real.toNNReal_le_toNNRealₓ'. -/
theorem toNNReal_le_toNNReal {r p : ℝ} (h : r ≤ p) : Real.toNNReal r ≤ Real.toNNReal p :=
  Real.toNNReal_mono h
#align real.to_nnreal_le_to_nnreal Real.toNNReal_le_toNNReal

/- warning: real.to_nnreal_add_le -> Real.toNNReal_add_le is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : Real}, LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) r p)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Real.toNNReal r) (Real.toNNReal p))
but is expected to have type
  forall {r : Real} {p : Real}, LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) r p)) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (Real.toNNReal r) (Real.toNNReal p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_add_le Real.toNNReal_add_leₓ'. -/
theorem toNNReal_add_le {r p : ℝ} : Real.toNNReal (r + p) ≤ Real.toNNReal r + Real.toNNReal p :=
  NNReal.coe_le_coe.1 <| max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) NNReal.zero_le_coe
#align real.to_nnreal_add_le Real.toNNReal_add_le

/- warning: real.to_nnreal_le_iff_le_coe -> Real.toNNReal_le_iff_le_coe is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) p) (LE.le.{0} Real Real.hasLe r ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) p))
but is expected to have type
  forall {r : Real} {p : NNReal}, Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) p) (LE.le.{0} Real Real.instLEReal r (NNReal.toReal p))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_le_iff_le_coe Real.toNNReal_le_iff_le_coeₓ'. -/
theorem toNNReal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : Real.toNNReal r ≤ p ↔ r ≤ ↑p :=
  NNReal.gi.gc r p
#align real.to_nnreal_le_iff_le_coe Real.toNNReal_le_iff_le_coe

/- warning: real.le_to_nnreal_iff_coe_le -> Real.le_toNNReal_iff_coe_le is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r (Real.toNNReal p)) (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) p))
but is expected to have type
  forall {r : NNReal} {p : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r (Real.toNNReal p)) (LE.le.{0} Real Real.instLEReal (NNReal.toReal r) p))
Case conversion may be inaccurate. Consider using '#align real.le_to_nnreal_iff_coe_le Real.le_toNNReal_iff_coe_leₓ'. -/
theorem le_toNNReal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ Real.toNNReal p ↔ ↑r ≤ p := by
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal p hp]
#align real.le_to_nnreal_iff_coe_le Real.le_toNNReal_iff_coe_le

/- warning: real.le_to_nnreal_iff_coe_le' -> Real.le_toNNReal_iff_coe_le' is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) r) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r (Real.toNNReal p)) (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) p))
but is expected to have type
  forall {r : NNReal} {p : Real}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) r) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r (Real.toNNReal p)) (LE.le.{0} Real Real.instLEReal (NNReal.toReal r) p))
Case conversion may be inaccurate. Consider using '#align real.le_to_nnreal_iff_coe_le' Real.le_toNNReal_iff_coe_le'ₓ'. -/
theorem le_toNNReal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ Real.toNNReal p ↔ ↑r ≤ p :=
  (le_or_lt 0 p).elim le_toNNReal_iff_coe_le fun hp => by
    simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]
#align real.le_to_nnreal_iff_coe_le' Real.le_toNNReal_iff_coe_le'

/- warning: real.to_nnreal_lt_iff_lt_coe -> Real.toNNReal_lt_iff_lt_coe is a dubious translation:
lean 3 declaration is
  forall {r : Real} {p : NNReal}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Real.toNNReal r) p) (LT.lt.{0} Real Real.hasLt r ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) p)))
but is expected to have type
  forall {r : Real} {p : NNReal}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Real.toNNReal r) p) (LT.lt.{0} Real Real.instLTReal r (NNReal.toReal p)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_lt_iff_lt_coe Real.toNNReal_lt_iff_lt_coeₓ'. -/
theorem toNNReal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : Real.toNNReal r < p ↔ r < ↑p := by
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal r ha]
#align real.to_nnreal_lt_iff_lt_coe Real.toNNReal_lt_iff_lt_coe

/- warning: real.lt_to_nnreal_iff_coe_lt -> Real.lt_toNNReal_iff_coe_lt is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r (Real.toNNReal p)) (LT.lt.{0} Real Real.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) p)
but is expected to have type
  forall {r : NNReal} {p : Real}, Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r (Real.toNNReal p)) (LT.lt.{0} Real Real.instLTReal (NNReal.toReal r) p)
Case conversion may be inaccurate. Consider using '#align real.lt_to_nnreal_iff_coe_lt Real.lt_toNNReal_iff_coe_ltₓ'. -/
theorem lt_toNNReal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < Real.toNNReal p ↔ ↑r < p :=
  by
  cases le_total 0 p
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal p h]
  · rw [to_nnreal_eq_zero.2 h]
    constructor
    · intro
      have := not_lt_of_le (zero_le r)
      contradiction
    · intro rp
      have : ¬p ≤ 0 := not_le_of_lt (lt_of_le_of_lt (NNReal.coe_nonneg _) rp)
      contradiction
#align real.lt_to_nnreal_iff_coe_lt Real.lt_toNNReal_iff_coe_lt

/- warning: real.to_nnreal_bit0 clashes with [anonymous] -> [anonymous]
warning: real.to_nnreal_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (r : Real), Eq.{1} NNReal (Real.toNNReal (bit0.{0} Real Real.hasAdd r)) (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (Real.toNNReal r))
but is expected to have type
  forall {r : Type.{u}} {β : Type.{v}}, (Nat -> r -> β) -> Nat -> (List.{u} r) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_bit0 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] (r : ℝ) : Real.toNNReal (bit0 r) = bit0 (Real.toNNReal r) :=
  by
  cases' le_total r 0 with hr hr
  · rw [to_nnreal_of_nonpos hr, to_nnreal_of_nonpos, bit0_zero]
    exact add_nonpos hr hr
  · exact to_nnreal_add hr hr
#align real.to_nnreal_bit0 [anonymous]

/- warning: real.to_nnreal_bit1 clashes with [anonymous] -> [anonymous]
warning: real.to_nnreal_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall {r : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} NNReal (Real.toNNReal (bit1.{0} Real Real.hasOne Real.hasAdd r)) (bit1.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (Real.toNNReal r)))
but is expected to have type
  forall {r : Type.{u}} {hr : Type.{v}}, (Nat -> r -> hr) -> Nat -> (List.{u} r) -> (List.{v} hr)
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_bit1 [anonymous]ₓ'. -/
@[simp]
theorem [anonymous] {r : ℝ} (hr : 0 ≤ r) : Real.toNNReal (bit1 r) = bit1 (Real.toNNReal r) :=
  (Real.toNNReal_add (by simp [hr]) zero_le_one).trans (by simp [bit1])
#align real.to_nnreal_bit1 [anonymous]

/- warning: real.to_nnreal_pow -> Real.toNNReal_pow is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (n : Nat), Eq.{1} NNReal (Real.toNNReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) (Real.toNNReal x) n))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (n : Nat), Eq.{1} NNReal (Real.toNNReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) (Real.toNNReal x) n))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_pow Real.toNNReal_powₓ'. -/
theorem toNNReal_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ n).toNNReal = x.toNNReal ^ n := by
  rw [← NNReal.coe_eq, NNReal.coe_pow, Real.coe_toNNReal _ (pow_nonneg hx _),
    Real.coe_toNNReal x hx]
#align real.to_nnreal_pow Real.toNNReal_pow

end ToNnreal

end Real

open Real

namespace NNReal

section Mul

/- warning: nnreal.mul_eq_mul_left -> NNReal.mul_eq_mul_left is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a b) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a c)) (Eq.{1} NNReal b c))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a b) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a c)) (Eq.{1} NNReal b c))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_eq_mul_left NNReal.mul_eq_mul_leftₓ'. -/
theorem mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : a * b = a * c ↔ b = c := by
  rw [mul_eq_mul_left_iff, or_iff_left h]
#align nnreal.mul_eq_mul_left NNReal.mul_eq_mul_left

/- warning: real.to_nnreal_mul -> Real.toNNReal_mul is a dubious translation:
lean 3 declaration is
  forall {p : Real} {q : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) p) -> (Eq.{1} NNReal (Real.toNNReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) p q)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Real.toNNReal p) (Real.toNNReal q)))
but is expected to have type
  forall {p : Real} {q : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) p) -> (Eq.{1} NNReal (Real.toNNReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) p q)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Real.toNNReal p) (Real.toNNReal q)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_mul Real.toNNReal_mulₓ'. -/
theorem Real.toNNReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    Real.toNNReal (p * q) = Real.toNNReal p * Real.toNNReal q :=
  by
  cases' le_total 0 q with hq hq
  · apply NNReal.eq
    simp [Real.toNNReal, hp, hq, max_eq_left, mul_nonneg]
  · have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero]
#align real.to_nnreal_mul Real.toNNReal_mul

end Mul

section Pow

#print NNReal.pow_antitone_exp /-
theorem pow_antitone_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) : a ^ n ≤ a ^ m :=
  pow_le_pow_of_le_one (zero_le a) a1 mn
#align nnreal.pow_antitone_exp NNReal.pow_antitone_exp
-/

/- warning: nnreal.exists_pow_lt_of_lt_one -> NNReal.exists_pow_lt_of_lt_one is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) a) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) b (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Exists.{1} Nat (fun (n : Nat) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal NNReal.semiring)))) b n) a))
but is expected to have type
  forall {a : NNReal} {b : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) a) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) b (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (Exists.{1} Nat (fun (n : Nat) => LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Nat NNReal (instHPow.{0, 0} NNReal Nat (Monoid.Pow.{0} NNReal (MonoidWithZero.toMonoid.{0} NNReal (Semiring.toMonoidWithZero.{0} NNReal instNNRealSemiring)))) b n) a))
Case conversion may be inaccurate. Consider using '#align nnreal.exists_pow_lt_of_lt_one NNReal.exists_pow_lt_of_lt_oneₓ'. -/
theorem exists_pow_lt_of_lt_one {a b : ℝ≥0} (ha : 0 < a) (hb : b < 1) : ∃ n : ℕ, b ^ n < a := by
  simpa only [← coe_pow, NNReal.coe_lt_coe] using
    exists_pow_lt_of_lt_one (NNReal.coe_pos.2 ha) (NNReal.coe_lt_coe.2 hb)
#align nnreal.exists_pow_lt_of_lt_one NNReal.exists_pow_lt_of_lt_one

/- warning: nnreal.exists_mem_Ico_zpow -> NNReal.exists_mem_Ico_zpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) y) -> (Exists.{1} Int (fun (n : Int) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Ico.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) y n) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) y (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))))
but is expected to have type
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) y) -> (Exists.{1} Int (fun (n : Int) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Ico.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) y n) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) y (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))))
Case conversion may be inaccurate. Consider using '#align nnreal.exists_mem_Ico_zpow NNReal.exists_mem_Ico_zpowₓ'. -/
theorem exists_mem_Ico_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ico (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n ≤ x ∧ (x : ℝ) < y ^ (n + 1) :=
    exists_mem_Ico_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← NNReal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ico_zpow NNReal.exists_mem_Ico_zpow

/- warning: nnreal.exists_mem_Ioc_zpow -> NNReal.exists_mem_Ioc_zpow is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) y) -> (Exists.{1} Int (fun (n : Int) => Membership.Mem.{0, 0} NNReal (Set.{0} NNReal) (Set.hasMem.{0} NNReal) x (Set.Ioc.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) y n) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) y (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.hasAdd) n (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))))))
but is expected to have type
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) y) -> (Exists.{1} Int (fun (n : Int) => Membership.mem.{0, 0} NNReal (Set.{0} NNReal) (Set.instMembershipSet.{0} NNReal) x (Set.Ioc.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) y n) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) y (HAdd.hAdd.{0, 0, 0} Int Int Int (instHAdd.{0} Int Int.instAddInt) n (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))))))
Case conversion may be inaccurate. Consider using '#align nnreal.exists_mem_Ioc_zpow NNReal.exists_mem_Ioc_zpowₓ'. -/
theorem exists_mem_Ioc_zpow {x : ℝ≥0} {y : ℝ≥0} (hx : x ≠ 0) (hy : 1 < y) :
    ∃ n : ℤ, x ∈ Set.Ioc (y ^ n) (y ^ (n + 1)) :=
  by
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, (y : ℝ) ^ n < x ∧ (x : ℝ) ≤ y ^ (n + 1) :=
    exists_mem_Ioc_zpow (bot_lt_iff_ne_bot.mpr hx) hy
  rw [← NNReal.coe_zpow] at hn h'n
  exact ⟨n, hn, h'n⟩
#align nnreal.exists_mem_Ioc_zpow NNReal.exists_mem_Ioc_zpow

end Pow

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas
about `has_ordered_sub` in the file `algebra.order.sub`. See also `mul_tsub` and `tsub_mul`. -/


/- warning: nnreal.sub_def -> NNReal.sub_def is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, Eq.{1} NNReal (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) r p) (Real.toNNReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) p)))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, Eq.{1} NNReal (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) r p) (Real.toNNReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (NNReal.toReal r) (NNReal.toReal p)))
Case conversion may be inaccurate. Consider using '#align nnreal.sub_def NNReal.sub_defₓ'. -/
theorem sub_def {r p : ℝ≥0} : r - p = Real.toNNReal (r - p) :=
  rfl
#align nnreal.sub_def NNReal.sub_def

/- warning: nnreal.coe_sub_def -> NNReal.coe_sub_def is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) r p)) (LinearOrder.max.{0} Real Real.linearOrder (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) r) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) p)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, Eq.{1} Real (NNReal.toReal (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) r p)) (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (NNReal.toReal r) (NNReal.toReal p)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align nnreal.coe_sub_def NNReal.coe_sub_defₓ'. -/
theorem coe_sub_def {r p : ℝ≥0} : ↑(r - p) = max (r - p : ℝ) 0 :=
  rfl
#align nnreal.coe_sub_def NNReal.coe_sub_def

noncomputable example : OrderedSub ℝ≥0 := by infer_instance

/- warning: nnreal.sub_div -> NNReal.sub_div is a dubious translation:
lean 3 declaration is
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) a b) c) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.hasSub) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a c) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b c))
but is expected to have type
  forall (a : NNReal) (b : NNReal) (c : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) a b) c) (HSub.hSub.{0, 0, 0} NNReal NNReal NNReal (instHSub.{0} NNReal NNReal.instSubNNReal) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a c) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b c))
Case conversion may be inaccurate. Consider using '#align nnreal.sub_div NNReal.sub_divₓ'. -/
theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _
#align nnreal.sub_div NNReal.sub_div

end Sub

section Inv

/- warning: nnreal.sum_div -> NNReal.sum_div is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> NNReal) (b : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (Finset.sum.{0, u1} NNReal ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) s (fun (i : ι) => f i)) b) (Finset.sum.{0, u1} NNReal ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) s (fun (i : ι) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (f i) b))
but is expected to have type
  forall {ι : Type.{u1}} (s : Finset.{u1} ι) (f : ι -> NNReal) (b : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (Finset.sum.{0, u1} NNReal ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) s (fun (i : ι) => f i)) b) (Finset.sum.{0, u1} NNReal ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) s (fun (i : ι) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (f i) b))
Case conversion may be inaccurate. Consider using '#align nnreal.sum_div NNReal.sum_divₓ'. -/
theorem sum_div {ι} (s : Finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
    (∑ i in s, f i) / b = ∑ i in s, f i / b :=
  Finset.sum_div
#align nnreal.sum_div NNReal.sum_div

/- warning: nnreal.inv_le -> NNReal.inv_le is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) r) p) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r p)))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) r) p) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r p)))
Case conversion may be inaccurate. Consider using '#align nnreal.inv_le NNReal.inv_leₓ'. -/
@[simp]
theorem inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]
#align nnreal.inv_le NNReal.inv_le

/- warning: nnreal.inv_le_of_le_mul -> NNReal.inv_le_of_le_mul is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r p)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) r) p)
but is expected to have type
  forall {r : NNReal} {p : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r p)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) r) p)
Case conversion may be inaccurate. Consider using '#align nnreal.inv_le_of_le_mul NNReal.inv_le_of_le_mulₓ'. -/
theorem inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p := by
  by_cases r = 0 <;> simp [*, inv_le]
#align nnreal.inv_le_of_le_mul NNReal.inv_le_of_le_mul

/- warning: nnreal.le_inv_iff_mul_le -> NNReal.le_inv_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal p (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) p)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r p) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal p (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) p)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r p) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))))
Case conversion may be inaccurate. Consider using '#align nnreal.le_inv_iff_mul_le NNReal.le_inv_iff_mul_leₓ'. -/
@[simp]
theorem le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 := by
  rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.le_inv_iff_mul_le NNReal.le_inv_iff_mul_le

/- warning: nnreal.lt_inv_iff_mul_lt -> NNReal.lt_inv_iff_mul_lt is a dubious translation:
lean 3 declaration is
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal p (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) r (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) p)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r p) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))))
but is expected to have type
  forall {r : NNReal} {p : NNReal}, (Ne.{1} NNReal p (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) r (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) p)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r p) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))))
Case conversion may be inaccurate. Consider using '#align nnreal.lt_inv_iff_mul_lt NNReal.lt_inv_iff_mul_ltₓ'. -/
@[simp]
theorem lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 := by
  rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]
#align nnreal.lt_inv_iff_mul_lt NNReal.lt_inv_iff_mul_lt

/- warning: nnreal.mul_le_iff_le_inv -> NNReal.mul_le_iff_le_inv is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r a) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) r) b)))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r a) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) r) b)))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_le_iff_le_inv NNReal.mul_le_iff_le_invₓ'. -/
theorem mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
  by
  have : 0 < r := lt_of_le_of_ne (zero_le r) hr.symm
  rw [← mul_le_mul_left (inv_pos.mpr this), ← mul_assoc, inv_mul_cancel hr, one_mul]
#align nnreal.mul_le_iff_le_inv NNReal.mul_le_iff_le_inv

/- warning: nnreal.le_div_iff_mul_le -> NNReal.le_div_iff_mul_le is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a r) b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a r) b))
Case conversion may be inaccurate. Consider using '#align nnreal.le_div_iff_mul_le NNReal.le_div_iff_mul_leₓ'. -/
theorem le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  le_div_iff₀ hr
#align nnreal.le_div_iff_mul_le NNReal.le_div_iff_mul_le

/- warning: nnreal.div_le_iff -> NNReal.div_le_iff is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a r) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b r)))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a r) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) b r)))
Case conversion may be inaccurate. Consider using '#align nnreal.div_le_iff NNReal.div_le_iffₓ'. -/
theorem div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
  div_le_iff₀ hr
#align nnreal.div_le_iff NNReal.div_le_iff

/- warning: nnreal.div_le_iff' -> NNReal.div_le_iff' is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a r) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r b)))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a r) b) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r b)))
Case conversion may be inaccurate. Consider using '#align nnreal.div_le_iff' NNReal.div_le_iff'ₓ'. -/
theorem div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
  @div_le_iff' ℝ _ a r b <| pos_iff_ne_zero.2 hr
#align nnreal.div_le_iff' NNReal.div_le_iff'

/- warning: nnreal.div_le_of_le_mul -> NNReal.div_le_of_le_mul is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b c)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a c) b)
but is expected to have type
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) b c)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a c) b)
Case conversion may be inaccurate. Consider using '#align nnreal.div_le_of_le_mul NNReal.div_le_of_le_mulₓ'. -/
theorem div_le_of_le_mul {a b c : ℝ≥0} (h : a ≤ b * c) : a / c ≤ b :=
  if h0 : c = 0 then by simp [h0] else (div_le_iff h0).2 h
#align nnreal.div_le_of_le_mul NNReal.div_le_of_le_mul

/- warning: nnreal.div_le_of_le_mul' -> NNReal.div_le_of_le_mul' is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b c)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a b) c)
but is expected to have type
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) b c)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a b) c)
Case conversion may be inaccurate. Consider using '#align nnreal.div_le_of_le_mul' NNReal.div_le_of_le_mul'ₓ'. -/
theorem div_le_of_le_mul' {a b c : ℝ≥0} (h : a ≤ b * c) : a / b ≤ c :=
  div_le_of_le_mul <| mul_comm b c ▸ h
#align nnreal.div_le_of_le_mul' NNReal.div_le_of_le_mul'

/- warning: nnreal.le_div_iff -> NNReal.le_div_iff is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a r) b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a r) b))
Case conversion may be inaccurate. Consider using '#align nnreal.le_div_iff NNReal.le_div_iffₓ'. -/
theorem le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
  @le_div_iff ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff NNReal.le_div_iff

/- warning: nnreal.le_div_iff' -> NNReal.le_div_iff' is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r a) b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r a) b))
Case conversion may be inaccurate. Consider using '#align nnreal.le_div_iff' NNReal.le_div_iff'ₓ'. -/
theorem le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
  @le_div_iff' ℝ _ a b r <| pos_iff_ne_zero.2 hr
#align nnreal.le_div_iff' NNReal.le_div_iff'

/- warning: nnreal.div_lt_iff -> NNReal.div_lt_iff is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a r) b) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) b r)))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a r) b) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) b r)))
Case conversion may be inaccurate. Consider using '#align nnreal.div_lt_iff NNReal.div_lt_iffₓ'. -/
theorem div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
  lt_iff_lt_of_le_iff_le (le_div_iff hr)
#align nnreal.div_lt_iff NNReal.div_lt_iff

/- warning: nnreal.div_lt_iff' -> NNReal.div_lt_iff' is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a r) b) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r b)))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a r) b) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r b)))
Case conversion may be inaccurate. Consider using '#align nnreal.div_lt_iff' NNReal.div_lt_iff'ₓ'. -/
theorem div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
  lt_iff_lt_of_le_iff_le (le_div_iff' hr)
#align nnreal.div_lt_iff' NNReal.div_lt_iff'

/- warning: nnreal.lt_div_iff -> NNReal.lt_div_iff is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a r) b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a r) b))
Case conversion may be inaccurate. Consider using '#align nnreal.lt_div_iff NNReal.lt_div_iffₓ'. -/
theorem lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff hr)
#align nnreal.lt_div_iff NNReal.lt_div_iff

/- warning: nnreal.lt_div_iff' -> NNReal.lt_div_iff' is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) r a) b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (Ne.{1} NNReal r (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) r a) b))
Case conversion may be inaccurate. Consider using '#align nnreal.lt_div_iff' NNReal.lt_div_iff'ₓ'. -/
theorem lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
  lt_iff_lt_of_le_iff_le (div_le_iff' hr)
#align nnreal.lt_div_iff' NNReal.lt_div_iff'

/- warning: nnreal.mul_lt_of_lt_div -> NNReal.mul_lt_of_lt_div is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) b r)) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a r) b)
but is expected to have type
  forall {a : NNReal} {b : NNReal} {r : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) b r)) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a r) b)
Case conversion may be inaccurate. Consider using '#align nnreal.mul_lt_of_lt_div NNReal.mul_lt_of_lt_divₓ'. -/
theorem mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
  by
  refine' (lt_div_iff fun hr => False.elim _).1 h
  subst r
  simpa using h
#align nnreal.mul_lt_of_lt_div NNReal.mul_lt_of_lt_div

theorem div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
    a / b ≤ a / c := by
  by_cases a0 : a = 0
  · rw [a0, zero_div, zero_div]
  · cases' a with a ha
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0))
    exact (div_le_div_left a0 b0 c0).mpr cb
#align nnreal.div_le_div_left_of_le NNReal.div_le_div_left_of_leₓ

/- warning: nnreal.div_le_div_left -> NNReal.div_le_div_left is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) a) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) b) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) c) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a b) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a c)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) c b))
but is expected to have type
  forall {a : NNReal} {b : NNReal} {c : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) a) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) b) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) c) -> (Iff (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a b) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a c)) (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) c b))
Case conversion may be inaccurate. Consider using '#align nnreal.div_le_div_left NNReal.div_le_div_leftₓ'. -/
theorem div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
    a / b ≤ a / c ↔ c ≤ b :=
  div_le_div_left a0 b0 c0
#align nnreal.div_le_div_left NNReal.div_le_div_left

/- warning: nnreal.le_of_forall_lt_one_mul_le -> NNReal.le_of_forall_lt_one_mul_le is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, (forall (a : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a x) y)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y)
but is expected to have type
  forall {x : NNReal} {y : NNReal}, (forall (a : NNReal), (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a x) y)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y)
Case conversion may be inaccurate. Consider using '#align nnreal.le_of_forall_lt_one_mul_le NNReal.le_of_forall_lt_one_mul_leₓ'. -/
theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀ a < 1, a * x ≤ y) : x ≤ y :=
  le_of_forall_ge_of_dense fun a ha =>
    by
    have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha)
    have hx' : x⁻¹ ≠ 0 := by rwa [(· ≠ ·), inv_eq_zero]
    have : a * x⁻¹ < 1 := by rwa [← lt_inv_iff_mul_lt hx', inv_inv]
    have : a * x⁻¹ * x ≤ y := h _ this
    rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this
#align nnreal.le_of_forall_lt_one_mul_le NNReal.le_of_forall_lt_one_mul_le

/- warning: nnreal.half_le_self -> NNReal.half_le_self is a dubious translation:
lean 3 declaration is
  forall (a : NNReal), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a (OfNat.ofNat.{0} NNReal 2 (OfNat.mk.{0} NNReal 2 (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))) a
but is expected to have type
  forall (a : NNReal), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a (OfNat.ofNat.{0} NNReal 2 (instOfNat.{0} NNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) a
Case conversion may be inaccurate. Consider using '#align nnreal.half_le_self NNReal.half_le_selfₓ'. -/
theorem half_le_self (a : ℝ≥0) : a / 2 ≤ a :=
  half_le_self bot_le
#align nnreal.half_le_self NNReal.half_le_self

/- warning: nnreal.half_lt_self -> NNReal.half_lt_self is a dubious translation:
lean 3 declaration is
  forall {a : NNReal}, (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a (OfNat.ofNat.{0} NNReal 2 (OfNat.mk.{0} NNReal 2 (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))) a)
but is expected to have type
  forall {a : NNReal}, (Ne.{1} NNReal a (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a (OfNat.ofNat.{0} NNReal 2 (instOfNat.{0} NNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) a)
Case conversion may be inaccurate. Consider using '#align nnreal.half_lt_self NNReal.half_lt_selfₓ'. -/
theorem half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
  half_lt_self h.bot_lt
#align nnreal.half_lt_self NNReal.half_lt_self

/- warning: nnreal.div_lt_one_of_lt -> NNReal.div_lt_one_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : NNReal} {b : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a b) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) a b) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {a : NNReal} {b : NNReal}, (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a b) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) a b) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)))
Case conversion may be inaccurate. Consider using '#align nnreal.div_lt_one_of_lt NNReal.div_lt_one_of_ltₓ'. -/
theorem div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 :=
  by
  rwa [div_lt_iff, one_mul]
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
#align nnreal.div_lt_one_of_lt NNReal.div_lt_one_of_lt

/- warning: real.to_nnreal_inv -> Real.toNNReal_inv is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Eq.{1} NNReal (Real.toNNReal (Inv.inv.{0} Real Real.hasInv x)) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) (Real.toNNReal x))
but is expected to have type
  forall {x : Real}, Eq.{1} NNReal (Real.toNNReal (Inv.inv.{0} Real Real.instInvReal x)) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) (Real.toNNReal x))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_inv Real.toNNReal_invₓ'. -/
theorem Real.toNNReal_inv {x : ℝ} : Real.toNNReal x⁻¹ = (Real.toNNReal x)⁻¹ :=
  by
  by_cases hx : 0 ≤ x
  · nth_rw 1 [← Real.coe_toNNReal x hx]
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
  · have hx' := le_of_not_ge hx
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')]
#align real.to_nnreal_inv Real.toNNReal_inv

/- warning: real.to_nnreal_div -> Real.toNNReal_div is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} NNReal (Real.toNNReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (Real.toNNReal x) (Real.toNNReal y)))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} NNReal (Real.toNNReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (Real.toNNReal x) (Real.toNNReal y)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_div Real.toNNReal_divₓ'. -/
theorem Real.toNNReal_div {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, ← Real.toNNReal_inv, ← Real.toNNReal_mul hx]
#align real.to_nnreal_div Real.toNNReal_div

/- warning: real.to_nnreal_div' -> Real.toNNReal_div' is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) y) -> (Eq.{1} NNReal (Real.toNNReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) x y)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (Real.toNNReal x) (Real.toNNReal y)))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) y) -> (Eq.{1} NNReal (Real.toNNReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) x y)) (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (Real.toNNReal x) (Real.toNNReal y)))
Case conversion may be inaccurate. Consider using '#align real.to_nnreal_div' Real.toNNReal_div'ₓ'. -/
theorem Real.toNNReal_div' {x y : ℝ} (hy : 0 ≤ y) :
    Real.toNNReal (x / y) = Real.toNNReal x / Real.toNNReal y := by
  rw [div_eq_inv_mul, div_eq_inv_mul, Real.toNNReal_mul (inv_nonneg.2 hy), Real.toNNReal_inv]
#align real.to_nnreal_div' Real.toNNReal_div'

/- warning: nnreal.inv_lt_one_iff -> NNReal.inv_lt_one_iff is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) x) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 1 (OfNat.mk.{0} NNReal 1 (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) x))
but is expected to have type
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (Iff (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne))) (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 1 (One.toOfNat1.{0} NNReal instNNRealOne)) x))
Case conversion may be inaccurate. Consider using '#align nnreal.inv_lt_one_iff NNReal.inv_lt_one_iffₓ'. -/
theorem inv_lt_one_iff {x : ℝ≥0} (hx : x ≠ 0) : x⁻¹ < 1 ↔ 1 < x := by
  rwa [← one_div, div_lt_iff hx, one_mul]
#align nnreal.inv_lt_one_iff NNReal.inv_lt_one_iff

/- warning: nnreal.zpow_pos -> NNReal.zpow_pos is a dubious translation:
lean 3 declaration is
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (forall (n : Int), LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield))))))) x n))
but is expected to have type
  forall {x : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (forall (n : Int), LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) (HPow.hPow.{0, 0, 0} NNReal Int NNReal (instHPow.{0, 0} NNReal Int (DivInvMonoid.Pow.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal))))))) x n))
Case conversion may be inaccurate. Consider using '#align nnreal.zpow_pos NNReal.zpow_posₓ'. -/
theorem zpow_pos {x : ℝ≥0} (hx : x ≠ 0) (n : ℤ) : 0 < x ^ n :=
  by
  cases n
  · simp [pow_pos hx.bot_lt _]
  · simp [pow_pos hx.bot_lt _]
#align nnreal.zpow_pos NNReal.zpow_pos

/- warning: nnreal.inv_lt_inv -> NNReal.inv_lt_inv is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x y) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) y) (Inv.inv.{0} NNReal (DivInvMonoid.toHasInv.{0} NNReal (GroupWithZero.toDivInvMonoid.{0} NNReal (DivisionSemiring.toGroupWithZero.{0} NNReal (Semifield.toDivisionSemiring.{0} NNReal (LinearOrderedSemifield.toSemifield.{0} NNReal (CanonicallyLinearOrderedSemifield.toLinearOrderedSemifield.{0} NNReal NNReal.canonicallyLinearOrderedSemifield)))))) x))
but is expected to have type
  forall {x : NNReal} {y : NNReal}, (Ne.{1} NNReal x (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x y) -> (LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) y) (Inv.inv.{0} NNReal (CanonicallyLinearOrderedSemifield.toInv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal) x))
Case conversion may be inaccurate. Consider using '#align nnreal.inv_lt_inv NNReal.inv_lt_invₓ'. -/
theorem inv_lt_inv {x y : ℝ≥0} (hx : x ≠ 0) (h : x < y) : y⁻¹ < x⁻¹ :=
  inv_lt_inv_of_lt hx.bot_lt h
#align nnreal.inv_lt_inv NNReal.inv_lt_inv

end Inv

/- warning: nnreal.abs_eq -> NNReal.abs_eq is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)
but is expected to have type
  forall (x : NNReal), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (NNReal.toReal x)) (NNReal.toReal x)
Case conversion may be inaccurate. Consider using '#align nnreal.abs_eq NNReal.abs_eqₓ'. -/
@[simp]
theorem abs_eq (x : ℝ≥0) : |(x : ℝ)| = x :=
  abs_of_nonneg x.property
#align nnreal.abs_eq NNReal.abs_eq

section Csupr

open Set

variable {ι : Sort _} {f : ι → ℝ≥0}

/- warning: nnreal.le_to_nnreal_of_coe_le -> NNReal.le_toNNReal_of_coe_le is a dubious translation:
lean 3 declaration is
  forall {x : NNReal} {y : Real}, (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x) y) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) x (Real.toNNReal y))
but is expected to have type
  forall {x : NNReal} {y : Real}, (LE.le.{0} Real Real.instLEReal (NNReal.toReal x) y) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) x (Real.toNNReal y))
Case conversion may be inaccurate. Consider using '#align nnreal.le_to_nnreal_of_coe_le NNReal.le_toNNReal_of_coe_leₓ'. -/
theorem le_toNNReal_of_coe_le {x : ℝ≥0} {y : ℝ} (h : ↑x ≤ y) : x ≤ y.toNNReal :=
  (le_toNNReal_iff_coe_le <| x.2.trans h).2 h
#align nnreal.le_to_nnreal_of_coe_le NNReal.le_toNNReal_of_coe_le

/- warning: nnreal.Sup_of_not_bdd_above -> NNReal.supₛ_of_not_bddAbove is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} NNReal}, (Not (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) s)) -> (Eq.{1} NNReal (SupSet.supₛ.{0} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) s) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {s : Set.{0} NNReal}, (Not (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) s)) -> (Eq.{1} NNReal (SupSet.supₛ.{0} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) s) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.Sup_of_not_bdd_above NNReal.supₛ_of_not_bddAboveₓ'. -/
theorem supₛ_of_not_bddAbove {s : Set ℝ≥0} (hs : ¬BddAbove s) : SupSet.supₛ s = 0 :=
  by
  rw [← bdd_above_coe] at hs
  rw [← NNReal.coe_eq, coe_Sup]
  exact Sup_of_not_bdd_above hs
#align nnreal.Sup_of_not_bdd_above NNReal.supₛ_of_not_bddAbove

/- warning: nnreal.supr_of_not_bdd_above -> NNReal.supᵢ_of_not_bddAbove is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} {f : ι -> NNReal}, (Not (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) (Set.range.{0, u1} NNReal ι f))) -> (Eq.{1} NNReal (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))))
but is expected to have type
  forall {ι : Sort.{u1}} {f : ι -> NNReal}, (Not (BddAbove.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) (Set.range.{0, u1} NNReal ι f))) -> (Eq.{1} NNReal (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)))
Case conversion may be inaccurate. Consider using '#align nnreal.supr_of_not_bdd_above NNReal.supᵢ_of_not_bddAboveₓ'. -/
theorem supᵢ_of_not_bddAbove (hf : ¬BddAbove (range f)) : (⨆ i, f i) = 0 :=
  supₛ_of_not_bddAbove hf
#align nnreal.supr_of_not_bdd_above NNReal.supᵢ_of_not_bddAbove

/- warning: nnreal.infi_empty -> NNReal.infᵢ_empty is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : IsEmpty.{u1} ι] (f : ι -> NNReal), Eq.{1} NNReal (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : IsEmpty.{u1} ι] (f : ι -> NNReal), Eq.{1} NNReal (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i)) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.infi_empty NNReal.infᵢ_emptyₓ'. -/
theorem infᵢ_empty [IsEmpty ι] (f : ι → ℝ≥0) : (⨅ i, f i) = 0 :=
  by
  rw [← NNReal.coe_eq, coe_infi]
  exact Real.cinfᵢ_empty _
#align nnreal.infi_empty NNReal.infᵢ_empty

/- warning: nnreal.infi_const_zero -> NNReal.infᵢ_const_zero is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Eq.{1} NNReal (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) α (fun (i : α) => OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  forall {α : Sort.{u1}}, Eq.{1} NNReal (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) α (fun (i : α) => OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.infi_const_zero NNReal.infᵢ_const_zeroₓ'. -/
@[simp]
theorem infᵢ_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ≥0)) = 0 :=
  by
  rw [← NNReal.coe_eq, coe_infi]
  exact Real.cinfᵢ_const_zero
#align nnreal.infi_const_zero NNReal.infᵢ_const_zero

/- warning: nnreal.infi_mul -> NNReal.infᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι f) a) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι f) a) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (f i) a))
Case conversion may be inaccurate. Consider using '#align nnreal.infi_mul NNReal.infᵢ_mulₓ'. -/
theorem infᵢ_mul (f : ι → ℝ≥0) (a : ℝ≥0) : infᵢ f * a = ⨅ i, f i * a :=
  by
  rw [← NNReal.coe_eq, NNReal.coe_mul, coe_infi, coe_infi]
  exact Real.infᵢ_mul_of_nonneg (NNReal.coe_nonneg _) _
#align nnreal.infi_mul NNReal.infᵢ_mul

/- warning: nnreal.mul_infi -> NNReal.mul_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι f)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι f)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (f i)))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_infi NNReal.mul_infᵢₓ'. -/
theorem mul_infᵢ (f : ι → ℝ≥0) (a : ℝ≥0) : a * infᵢ f = ⨅ i, a * f i := by
  simpa only [mul_comm] using infi_mul f a
#align nnreal.mul_infi NNReal.mul_infᵢ

/- warning: nnreal.mul_supr -> NNReal.mul_supᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) a (f i)))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (f i)))
Case conversion may be inaccurate. Consider using '#align nnreal.mul_supr NNReal.mul_supᵢₓ'. -/
theorem mul_supᵢ (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  by
  rw [← NNReal.coe_eq, NNReal.coe_mul, NNReal.coe_supᵢ, NNReal.coe_supᵢ]
  exact Real.mul_supᵢ_of_nonneg (NNReal.coe_nonneg _) _
#align nnreal.mul_supr NNReal.mul_supᵢ

/- warning: nnreal.supr_mul -> NNReal.supᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i)) a) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i)) a) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (f i) a))
Case conversion may be inaccurate. Consider using '#align nnreal.supr_mul NNReal.supᵢ_mulₓ'. -/
theorem supᵢ_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a :=
  by
  rw [mul_comm, mul_supr]
  simp_rw [mul_comm]
#align nnreal.supr_mul NNReal.supᵢ_mul

/- warning: nnreal.supr_div -> NNReal.supᵢ_div is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => f i)) a) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι (fun (i : ι) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal NNReal.hasDiv) (f i) a))
but is expected to have type
  forall {ι : Sort.{u1}} (f : ι -> NNReal) (a : NNReal), Eq.{1} NNReal (HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => f i)) a) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι (fun (i : ι) => HDiv.hDiv.{0, 0, 0} NNReal NNReal NNReal (instHDiv.{0} NNReal (CanonicallyLinearOrderedSemifield.toDiv.{0} NNReal NNReal.instCanonicallyLinearOrderedSemifieldNNReal)) (f i) a))
Case conversion may be inaccurate. Consider using '#align nnreal.supr_div NNReal.supᵢ_divₓ'. -/
theorem supᵢ_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, supr_mul]
#align nnreal.supr_div NNReal.supᵢ_div

variable [Nonempty ι]

/- warning: nnreal.le_mul_infi -> NNReal.le_mul_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : NNReal} {h : ι -> NNReal}, (forall (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) g (h j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) g (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι h)))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : NNReal} {h : ι -> NNReal}, (forall (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) g (h j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) g (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι h)))
Case conversion may be inaccurate. Consider using '#align nnreal.le_mul_infi NNReal.le_mul_infᵢₓ'. -/
theorem le_mul_infᵢ {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * infᵢ h :=
  by
  rw [mul_infi]
  exact le_cinfᵢ H
#align nnreal.le_mul_infi NNReal.le_mul_infᵢ

/- warning: nnreal.mul_supr_le -> NNReal.mul_supᵢ_le is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : NNReal} {h : ι -> NNReal}, (forall (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) g (h j)) a) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) g (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι h)) a)
but is expected to have type
  forall {ι : Sort.{u1}} {_inst_1 : NNReal} {a : NNReal} {g : ι -> NNReal}, (forall (ᾰ : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (g ᾰ)) _inst_1) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) a (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι g)) _inst_1)
Case conversion may be inaccurate. Consider using '#align nnreal.mul_supr_le NNReal.mul_supᵢ_leₓ'. -/
theorem mul_supᵢ_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * supᵢ h ≤ a :=
  by
  rw [mul_supr]
  exact csupᵢ_le H
#align nnreal.mul_supr_le NNReal.mul_supᵢ_le

/- warning: nnreal.le_infi_mul -> NNReal.le_infᵢ_mul is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : NNReal}, (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (g i) h)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι g) h))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : NNReal}, (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (g i) h)) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι g) h))
Case conversion may be inaccurate. Consider using '#align nnreal.le_infi_mul NNReal.le_infᵢ_mulₓ'. -/
theorem le_infᵢ_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ infᵢ g * h :=
  by
  rw [infi_mul]
  exact le_cinfᵢ H
#align nnreal.le_infi_mul NNReal.le_infᵢ_mul

/- warning: nnreal.supr_mul_le -> NNReal.supᵢ_mul_le is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : NNReal}, (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (g i) h) a) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι g) h) a)
but is expected to have type
  forall {ι : Sort.{u1}} {_inst_1 : NNReal} {a : ι -> NNReal} {g : NNReal}, (forall (i : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (a i) g) _inst_1) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι a) g) _inst_1)
Case conversion may be inaccurate. Consider using '#align nnreal.supr_mul_le NNReal.supᵢ_mul_leₓ'. -/
theorem supᵢ_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : supᵢ g * h ≤ a :=
  by
  rw [supr_mul]
  exact csupᵢ_le H
#align nnreal.supr_mul_le NNReal.supᵢ_mul_le

/- warning: nnreal.le_infi_mul_infi -> NNReal.le_infᵢ_mul_infᵢ is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : ι -> NNReal}, (forall (i : ι) (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (g i) (h j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι g) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasInf.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι h)))
but is expected to have type
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : ι -> NNReal}, (forall (i : ι) (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (g i) (h j))) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) a (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι g) (infᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toInfSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι h)))
Case conversion may be inaccurate. Consider using '#align nnreal.le_infi_mul_infi NNReal.le_infᵢ_mul_infᵢₓ'. -/
theorem le_infᵢ_mul_infᵢ {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ infᵢ g * infᵢ h :=
  le_infᵢ_mul fun i => le_mul_infᵢ <| H i
#align nnreal.le_infi_mul_infi NNReal.le_infᵢ_mul_infᵢ

/- warning: nnreal.supr_mul_supr_le -> NNReal.supᵢ_mul_supᵢ_le is a dubious translation:
lean 3 declaration is
  forall {ι : Sort.{u1}} [_inst_1 : Nonempty.{u1} ι] {a : NNReal} {g : ι -> NNReal} {h : ι -> NNReal}, (forall (i : ι) (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (g i) (h j)) a) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι g) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toHasSup.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.conditionallyCompleteLinearOrderBot))) ι h)) a)
but is expected to have type
  forall {ι : Sort.{u1}} {_inst_1 : NNReal} {a : ι -> NNReal} {g : ι -> NNReal}, (forall (ᾰ : ι) (j : ι), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (a ᾰ) (g j)) _inst_1) -> (LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι a) (supᵢ.{0, u1} NNReal (ConditionallyCompleteLattice.toSupSet.{0} NNReal (ConditionallyCompleteLinearOrder.toConditionallyCompleteLattice.{0} NNReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} NNReal NNReal.instConditionallyCompleteLinearOrderBotNNReal))) ι g)) _inst_1)
Case conversion may be inaccurate. Consider using '#align nnreal.supr_mul_supr_le NNReal.supᵢ_mul_supᵢ_leₓ'. -/
theorem supᵢ_mul_supᵢ_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    supᵢ g * supᵢ h ≤ a :=
  supᵢ_mul_le fun i => mul_supᵢ_le <| H _
#align nnreal.supr_mul_supr_le NNReal.supᵢ_mul_supᵢ_le

end Csupr

end NNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0}

/- warning: set.ord_connected.preimage_coe_nnreal_real -> Set.OrdConnected.preimage_coe_nnreal_real is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Set.OrdConnected.{0} Real Real.preorder s) -> (Set.OrdConnected.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) (Set.preimage.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) s))
but is expected to have type
  forall {s : Set.{0} Real}, (Set.OrdConnected.{0} Real Real.instPreorderReal s) -> (Set.OrdConnected.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) (Set.preimage.{0, 0} NNReal Real NNReal.toReal s))
Case conversion may be inaccurate. Consider using '#align set.ord_connected.preimage_coe_nnreal_real Set.OrdConnected.preimage_coe_nnreal_realₓ'. -/
theorem preimage_coe_nnreal_real (h : s.OrdConnected) : (coe ⁻¹' s : Set ℝ≥0).OrdConnected :=
  h.preimage_mono NNReal.coe_mono
#align set.ord_connected.preimage_coe_nnreal_real Set.OrdConnected.preimage_coe_nnreal_real

/- warning: set.ord_connected.image_coe_nnreal_real -> Set.OrdConnected.image_coe_nnreal_real is a dubious translation:
lean 3 declaration is
  forall {t : Set.{0} NNReal}, (Set.OrdConnected.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring))) t) -> (Set.OrdConnected.{0} Real Real.preorder (Set.image.{0, 0} NNReal Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe)))) t))
but is expected to have type
  forall {t : Set.{0} NNReal}, (Set.OrdConnected.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring)) t) -> (Set.OrdConnected.{0} Real Real.instPreorderReal (Set.image.{0, 0} NNReal Real NNReal.toReal t))
Case conversion may be inaccurate. Consider using '#align set.ord_connected.image_coe_nnreal_real Set.OrdConnected.image_coe_nnreal_realₓ'. -/
theorem image_coe_nnreal_real (h : t.OrdConnected) : (coe '' t : Set ℝ).OrdConnected :=
  ⟨ball_image_iff.2 fun x hx =>
      ball_image_iff.2 fun y hy z hz => ⟨⟨z, x.2.trans hz.1⟩, h.out hx hy hz, rfl⟩⟩
#align set.ord_connected.image_coe_nnreal_real Set.OrdConnected.image_coe_nnreal_real

#print Set.OrdConnected.image_real_toNNReal /-
theorem image_real_toNNReal (h : s.OrdConnected) : (Real.toNNReal '' s).OrdConnected :=
  by
  refine' ⟨ball_image_iff.2 fun x hx => ball_image_iff.2 fun y hy z hz => _⟩
  cases' le_total y 0 with hy₀ hy₀
  · rw [mem_Icc, Real.toNNReal_of_nonpos hy₀, nonpos_iff_eq_zero] at hz
    exact ⟨y, hy, (to_nnreal_of_nonpos hy₀).trans hz.2.symm⟩
  · lift y to ℝ≥0 using hy₀
    rw [to_nnreal_coe] at hz
    exact ⟨z, h.out hx hy ⟨to_nnreal_le_iff_le_coe.1 hz.1, hz.2⟩, to_nnreal_coe⟩
#align set.ord_connected.image_real_to_nnreal Set.OrdConnected.image_real_toNNReal
-/

#print Set.OrdConnected.preimage_real_toNNReal /-
theorem preimage_real_toNNReal (h : t.OrdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected :=
  h.preimage_mono Real.toNNReal_mono
#align set.ord_connected.preimage_real_to_nnreal Set.OrdConnected.preimage_real_toNNReal
-/

end OrdConnected

end Set

namespace Real

#print Real.nnabs /-
/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot]
def nnabs : ℝ →*₀ ℝ≥0 where
  toFun x := ⟨|x|, abs_nonneg x⟩
  map_zero' := by
    ext
    simp
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [abs_mul]
#align real.nnabs Real.nnabs
-/

/- warning: real.coe_nnabs -> Real.coe_nnabs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)
but is expected to have type
  forall (x : Real), Eq.{1} Real (NNReal.toReal (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)
Case conversion may be inaccurate. Consider using '#align real.coe_nnabs Real.coe_nnabsₓ'. -/
@[norm_cast, simp]
theorem coe_nnabs (x : ℝ) : (nnabs x : ℝ) = |x| :=
  rfl
#align real.coe_nnabs Real.coe_nnabs

/- warning: real.nnabs_of_nonneg -> Real.nnabs_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} NNReal (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs x) (Real.toNNReal x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) x) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs x) (Real.toNNReal x))
Case conversion may be inaccurate. Consider using '#align real.nnabs_of_nonneg Real.nnabs_of_nonnegₓ'. -/
@[simp]
theorem nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : nnabs x = toNNReal x :=
  by
  ext
  simp [coe_to_nnreal x h, abs_of_nonneg h]
#align real.nnabs_of_nonneg Real.nnabs_of_nonneg

/- warning: real.nnabs_coe -> Real.nnabs_coe is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} NNReal (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x)) x
but is expected to have type
  forall (x : NNReal), Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) (NNReal.toReal x)) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (NNReal.toReal x)) x
Case conversion may be inaccurate. Consider using '#align real.nnabs_coe Real.nnabs_coeₓ'. -/
theorem nnabs_coe (x : ℝ≥0) : nnabs x = x := by simp
#align real.nnabs_coe Real.nnabs_coe

/- warning: real.coe_to_nnreal_le -> Real.coe_toNNReal_le is a dubious translation:
lean 3 declaration is
  forall (x : Real), LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) (Real.toNNReal x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x)
but is expected to have type
  forall (x : Real), LE.le.{0} Real Real.instLEReal (NNReal.toReal (Real.toNNReal x)) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x)
Case conversion may be inaccurate. Consider using '#align real.coe_to_nnreal_le Real.coe_toNNReal_leₓ'. -/
theorem coe_toNNReal_le (x : ℝ) : (toNNReal x : ℝ) ≤ |x| :=
  max_le (le_abs_self _) (abs_nonneg _)
#align real.coe_to_nnreal_le Real.coe_toNNReal_le

/- warning: real.cast_nat_abs_eq_nnabs_cast -> Real.cast_natAbs_eq_nnabs_cast is a dubious translation:
lean 3 declaration is
  forall (n : Int), Eq.{1} NNReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat NNReal (HasLiftT.mk.{1, 1} Nat NNReal (CoeTCₓ.coe.{1, 1} Nat NNReal (Nat.castCoe.{0} NNReal (AddMonoidWithOne.toNatCast.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) (Int.natAbs n)) (coeFn.{1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) (fun (_x : MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) => Real -> NNReal) (MonoidWithZeroHom.hasCoeToFun.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.ring))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))) Real.nnabs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n))
but is expected to have type
  forall (n : Int), Eq.{1} NNReal (Nat.cast.{0} NNReal (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (Int.natAbs n)) (FunLike.coe.{1, 1, 1} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real (fun (_x : Real) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : Real) => NNReal) _x) (MulHomClass.toFunLike.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulOneClass.toMul.{0} Real (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))))) (MulOneClass.toMul.{0} NNReal (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))) (MonoidHomClass.toMulHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (MulZeroOneClass.toMulOneClass.{0} Real (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal)))) (MulZeroOneClass.toMulOneClass.{0} NNReal (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) (MonoidWithZeroHomClass.toMonoidHomClass.{0, 0, 0} (MonoidWithZeroHom.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))) Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)) (MonoidWithZeroHom.monoidWithZeroHomClass.{0, 0} Real NNReal (NonAssocSemiring.toMulZeroOneClass.{0} Real (NonAssocRing.toNonAssocSemiring.{0} Real (Ring.toNonAssocRing.{0} Real Real.instRingReal))) (NonAssocSemiring.toMulZeroOneClass.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring)))))) Real.nnabs (Int.cast.{0} Real Real.intCast n))
Case conversion may be inaccurate. Consider using '#align real.cast_nat_abs_eq_nnabs_cast Real.cast_natAbs_eq_nnabs_castₓ'. -/
theorem cast_natAbs_eq_nnabs_cast (n : ℤ) : (n.natAbs : ℝ≥0) = nnabs n :=
  by
  ext
  rw [NNReal.coe_nat_cast, Int.cast_natAbs, Real.coe_nnabs]
#align real.cast_nat_abs_eq_nnabs_cast Real.cast_natAbs_eq_nnabs_cast

end Real

namespace Tactic

open Positivity

private theorem nnreal_coe_pos {r : ℝ≥0} : 0 < r → 0 < (r : ℝ) :=
  NNReal.coe_pos.2
#align tactic.nnreal_coe_pos tactic.nnreal_coe_pos

/-- Extension for the `positivity` tactic: cast from `ℝ≥0` to `ℝ`. -/
@[positivity]
unsafe def positivity_coe_nnreal_real : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ NNReal.Real.hasCoe)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` nnreal_coe_pos [p]
      | _ => nonnegative <$> mk_app `` NNReal.coe_nonneg [a]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ)` for `r : ℝ≥0`"
#align tactic.positivity_coe_nnreal_real tactic.positivity_coe_nnreal_real

end Tactic

