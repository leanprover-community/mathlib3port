/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard

! This file was ported from Lean 3 source module data.real.ereal
! leanprover-community/mathlib commit ee05e9ce1322178f0c12004eb93c00d2c8c00ed2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Basic
import Mathbin.Data.Real.Ennreal
import Mathbin.Data.Sign

/-!
# The extended reals [-∞, ∞].

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `ereal`, the real numbers together with a top and bottom element,
referred to as ⊤ and ⊥. It is implemented as `with_bot (with_top ℝ)`

Addition and multiplication are problematic in the presence of ±∞, but
negation has a natural definition and satisfies the usual properties.

An ad hoc addition is defined, for which `ereal` is an `add_comm_monoid`, and even an ordered one
(if `a ≤ a'` and `b ≤ b'` then `a + b ≤ a' + b'`).
Note however that addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)` so this can not be upgraded
to a group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential
and the logarithm between `ereal` and `ℝ≥0∞` respect the operations (notice that the
convention `0 * ∞ = 0` on `ℝ≥0∞` is enforced by measure theory).

An ad hoc subtraction is then defined by `x - y = x + (-y)`. It does not have nice properties,
but it is sometimes convenient to have.

An ad hoc multiplication is defined, for which `ereal` is a `comm_monoid_with_zero`. We make the
choice that `0 * x = x * 0 = 0` for any `x` (while the other cases are defined non-ambiguously).
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1*⊥ + (-1)*⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.

`ereal` is a `complete_linear_order`; this is deduced by type class inference from
the fact that `with_bot (with_top L)` is a complete linear order if `L` is
a conditionally complete linear order.

Coercions from `ℝ` and from `ℝ≥0∞` are registered, and their basic properties are proved. The main
one is the real coercion, and is usually referred to just as `coe` (lemmas such as
`ereal.coe_add` deal with this coercion). The one from `ennreal` is usually called `coe_ennreal`
in the `ereal` namespace.

We define an absolute value `ereal.abs` from `ereal` to `ℝ≥0∞`. Two elements of `ereal` coincide
if and only if they have the same absolute value and the same sign.

## Tags

real, ereal, complete lattice
-/


open Function

open ENNReal NNReal

noncomputable section

#print EReal /-
/-- ereal : The type `[-∞, ∞]` -/
def EReal :=
  WithBot (WithTop ℝ)deriving Bot, Zero, One, Nontrivial, AddMonoid, SupSet, InfSet,
  CompleteLinearOrder, LinearOrderedAddCommMonoid, ZeroLEOneClass
#align ereal EReal
-/

#print Real.toEReal /-
/-- The canonical inclusion froms reals to ereals. Do not use directly: as this is registered as
a coercion, use the coercion instead. -/
def Real.toEReal : ℝ → EReal :=
  some ∘ some
#align real.to_ereal Real.toEReal
-/

namespace EReal

/- warning: ereal.decidable_lt -> EReal.decidableLt is a dubious translation:
lean 3 declaration is
  DecidableRel.{1} EReal (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))))
but is expected to have type
  DecidableRel.{1} EReal (fun (x._@.Mathlib.Data.Real.EReal._hyg.219 : EReal) (x._@.Mathlib.Data.Real.EReal._hyg.221 : EReal) => LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x._@.Mathlib.Data.Real.EReal._hyg.219 x._@.Mathlib.Data.Real.EReal._hyg.221)
Case conversion may be inaccurate. Consider using '#align ereal.decidable_lt EReal.decidableLtₓ'. -/
-- things unify with `with_bot.decidable_lt` later if we we don't provide this explicitly.
instance decidableLt : DecidableRel ((· < ·) : EReal → EReal → Prop) :=
  WithBot.decidableLT
#align ereal.decidable_lt EReal.decidableLt

-- TODO: Provide explicitly, otherwise it is inferred noncomputably from `complete_linear_order`
instance : Top EReal :=
  ⟨some ⊤⟩

instance : Coe ℝ EReal :=
  ⟨Real.toEReal⟩

/- warning: ereal.coe_strict_mono -> EReal.coe_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{0, 0} Real EReal Real.preorder (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))))
but is expected to have type
  StrictMono.{0, 0} Real EReal Real.instPreorderReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) Real.toEReal
Case conversion may be inaccurate. Consider using '#align ereal.coe_strict_mono EReal.coe_strictMonoₓ'. -/
theorem coe_strictMono : StrictMono (coe : ℝ → EReal) :=
  WithBot.coe_strictMono.comp WithTop.coe_strictMono
#align ereal.coe_strict_mono EReal.coe_strictMono

#print EReal.coe_injective /-
theorem coe_injective : Injective (coe : ℝ → EReal) :=
  coe_strictMono.Injective
#align ereal.coe_injective EReal.coe_injective
-/

/- warning: ereal.coe_le_coe_iff -> EReal.coe_le_coe_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y)) (LE.le.{0} Real Real.hasLe x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (Real.toEReal y)) (LE.le.{0} Real Real.instLEReal x y)
Case conversion may be inaccurate. Consider using '#align ereal.coe_le_coe_iff EReal.coe_le_coe_iffₓ'. -/
@[simp, norm_cast]
protected theorem coe_le_coe_iff {x y : ℝ} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_strictMono.le_iff_le
#align ereal.coe_le_coe_iff EReal.coe_le_coe_iff

/- warning: ereal.coe_lt_coe_iff -> EReal.coe_lt_coe_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y)) (LT.lt.{0} Real Real.hasLt x y)
but is expected to have type
  forall {x : Real} {y : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (Real.toEReal y)) (LT.lt.{0} Real Real.instLTReal x y)
Case conversion may be inaccurate. Consider using '#align ereal.coe_lt_coe_iff EReal.coe_lt_coe_iffₓ'. -/
@[simp, norm_cast]
protected theorem coe_lt_coe_iff {x y : ℝ} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_strictMono.lt_iff_lt
#align ereal.coe_lt_coe_iff EReal.coe_lt_coe_iff

#print EReal.coe_eq_coe_iff /-
@[simp, norm_cast]
protected theorem coe_eq_coe_iff {x y : ℝ} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_injective.eq_iff
#align ereal.coe_eq_coe_iff EReal.coe_eq_coe_iff
-/

#print EReal.coe_ne_coe_iff /-
protected theorem coe_ne_coe_iff {x y : ℝ} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_injective.ne_iff
#align ereal.coe_ne_coe_iff EReal.coe_ne_coe_iff
-/

#print ENNReal.toEReal /-
/-- The canonical map from nonnegative extended reals to extended reals -/
def ENNReal.toEReal : ℝ≥0∞ → EReal
  | ⊤ => ⊤
  | some x => x.1
#align ennreal.to_ereal ENNReal.toEReal
-/

#print EReal.hasCoeENNReal /-
instance hasCoeENNReal : Coe ℝ≥0∞ EReal :=
  ⟨ENNReal.toEReal⟩
#align ereal.has_coe_ennreal EReal.hasCoeENNReal
-/

instance : Inhabited EReal :=
  ⟨0⟩

/- warning: ereal.coe_zero -> EReal.coe_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))
but is expected to have type
  Eq.{1} EReal (Real.toEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))
Case conversion may be inaccurate. Consider using '#align ereal.coe_zero EReal.coe_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_zero : ((0 : ℝ) : EReal) = 0 :=
  rfl
#align ereal.coe_zero EReal.coe_zero

/- warning: ereal.coe_one -> EReal.coe_one is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))
but is expected to have type
  Eq.{1} EReal (Real.toEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))
Case conversion may be inaccurate. Consider using '#align ereal.coe_one EReal.coe_oneₓ'. -/
@[simp, norm_cast]
theorem coe_one : ((1 : ℝ) : EReal) = 1 :=
  rfl
#align ereal.coe_one EReal.coe_one

#print EReal.rec /-
/-- A recursor for `ereal` in terms of the coercion.

A typical invocation looks like `induction x using ereal.rec`. Note that using `induction`
directly will unfold `ereal` to `option` which is undesirable.

When working in term mode, note that pattern matching can be used directly. -/
@[elab_as_elim]
protected def rec {C : EReal → Sort _} (h_bot : C ⊥) (h_real : ∀ a : ℝ, C a) (h_top : C ⊤) :
    ∀ a : EReal, C a
  | ⊥ => h_bot
  | (a : ℝ) => h_real a
  | ⊤ => h_top
#align ereal.rec EReal.rec
-/

#print EReal.mul /-
/-- The multiplication on `ereal`. Our definition satisfies `0 * x = x * 0 = 0` for any `x`, and
picks the only sensible value elsewhere. -/
protected def mul : EReal → EReal → EReal
  | ⊥, ⊥ => ⊤
  | ⊥, ⊤ => ⊥
  | ⊥, (y : ℝ) => if 0 < y then ⊥ else if y = 0 then 0 else ⊤
  | ⊤, ⊥ => ⊥
  | ⊤, ⊤ => ⊤
  | ⊤, (y : ℝ) => if 0 < y then ⊤ else if y = 0 then 0 else ⊥
  | (x : ℝ), ⊤ => if 0 < x then ⊤ else if x = 0 then 0 else ⊥
  | (x : ℝ), ⊥ => if 0 < x then ⊥ else if x = 0 then 0 else ⊤
  | (x : ℝ), (y : ℝ) => (x * y : ℝ)
#align ereal.mul EReal.mul
-/

instance : Mul EReal :=
  ⟨EReal.mul⟩

/- warning: ereal.induction₂ -> EReal.induction₂ is a dubious translation:
lean 3 declaration is
  forall {P : EReal -> EReal -> Prop}, (P (Top.top.{0} EReal EReal.hasTop) (Top.top.{0} EReal EReal.hasTop)) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (P (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))) -> (P (Top.top.{0} EReal EReal.hasTop) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (P (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))) -> (P (Top.top.{0} EReal EReal.hasTop) (Bot.bot.{0} EReal EReal.hasBot)) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (P ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop))) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (P ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Bot.bot.{0} EReal EReal.hasBot))) -> (P (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) (Top.top.{0} EReal EReal.hasTop)) -> (forall (x : Real) (y : Real), P ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y)) -> (P (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) (Bot.bot.{0} EReal EReal.hasBot)) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (P ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop))) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (P ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Bot.bot.{0} EReal EReal.hasBot))) -> (P (Bot.bot.{0} EReal EReal.hasBot) (Top.top.{0} EReal EReal.hasTop)) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (P (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))) -> (P (Bot.bot.{0} EReal EReal.hasBot) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (forall (x : Real), (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (P (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))) -> (P (Bot.bot.{0} EReal EReal.hasBot) (Bot.bot.{0} EReal EReal.hasBot)) -> (forall (x : EReal) (y : EReal), P x y)
but is expected to have type
  forall {P : EReal -> EReal -> Prop}, (P (Top.top.{0} EReal EReal.instTopEReal) (Top.top.{0} EReal EReal.instTopEReal)) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (P (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x))) -> (P (Top.top.{0} EReal EReal.instTopEReal) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (P (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x))) -> (P (Top.top.{0} EReal EReal.instTopEReal) (Bot.bot.{0} EReal instERealBot)) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (P (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal))) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (P (Real.toEReal x) (Bot.bot.{0} EReal instERealBot))) -> (P (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Top.top.{0} EReal EReal.instTopEReal)) -> (forall (x : Real) (y : Real), P (Real.toEReal x) (Real.toEReal y)) -> (P (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Bot.bot.{0} EReal instERealBot)) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (P (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal))) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (P (Real.toEReal x) (Bot.bot.{0} EReal instERealBot))) -> (P (Bot.bot.{0} EReal instERealBot) (Top.top.{0} EReal EReal.instTopEReal)) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (P (Bot.bot.{0} EReal instERealBot) (Real.toEReal x))) -> (P (Bot.bot.{0} EReal instERealBot) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (forall (x : Real), (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (P (Bot.bot.{0} EReal instERealBot) (Real.toEReal x))) -> (P (Bot.bot.{0} EReal instERealBot) (Bot.bot.{0} EReal instERealBot)) -> (forall (x : EReal) (y : EReal), P x y)
Case conversion may be inaccurate. Consider using '#align ereal.induction₂ EReal.induction₂ₓ'. -/
/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. -/
@[elab_as_elim]
theorem induction₂ {P : EReal → EReal → Prop} (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥) (zero_top : P 0 ⊤)
    (coe_coe : ∀ x y : ℝ, P x y) (zero_bot : P 0 ⊥) (neg_top : ∀ x : ℝ, x < 0 → P x ⊤)
    (neg_bot : ∀ x : ℝ, x < 0 → P x ⊥) (bot_top : P ⊥ ⊤) (bot_pos : ∀ x : ℝ, 0 < x → P ⊥ x)
    (bot_zero : P ⊥ 0) (bot_neg : ∀ x : ℝ, x < 0 → P ⊥ x) (bot_bot : P ⊥ ⊥) : ∀ x y, P x y
  | ⊥, ⊥ => bot_bot
  | ⊥, (y : ℝ) => by
    rcases lt_trichotomy 0 y with (hy | rfl | hy)
    exacts[bot_pos y hy, bot_zero, bot_neg y hy]
  | ⊥, ⊤ => bot_top
  | (x : ℝ), ⊥ => by
    rcases lt_trichotomy 0 x with (hx | rfl | hx)
    exacts[pos_bot x hx, zero_bot, neg_bot x hx]
  | (x : ℝ), (y : ℝ) => coe_coe _ _
  | (x : ℝ), ⊤ => by
    rcases lt_trichotomy 0 x with (hx | rfl | hx)
    exacts[pos_top x hx, zero_top, neg_top x hx]
  | ⊤, ⊥ => top_bot
  | ⊤, (y : ℝ) => by
    rcases lt_trichotomy 0 y with (hy | rfl | hy)
    exacts[top_pos y hy, top_zero, top_neg y hy]
  | ⊤, ⊤ => top_top
#align ereal.induction₂ EReal.induction₂

/-! `ereal` with its multiplication is a `comm_monoid_with_zero`. However, the proof of
associativity by hand is extremely painful (with 125 cases...). Instead, we will deduce it later
on from the facts that the absolute value and the sign are multiplicative functions taking value
in associative objects, and that they characterize an extended real number. For now, we only
record more basic properties of multiplication.
-/


instance : MulZeroOneClass EReal :=
  { EReal.hasMul, EReal.hasOne,
    EReal.hasZero with
    one_mul := fun x => by
      induction x using EReal.rec <;>
        · dsimp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_one, zero_lt_one, if_true, one_mul]
    mul_one := fun x => by
      induction x using EReal.rec <;>
        · dsimp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_one, zero_lt_one, if_true, mul_one]
    zero_mul := fun x => by
      induction x using EReal.rec <;>
        · simp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_zero, zero_lt_one, if_true, if_false, lt_irrefl (0 : ℝ),
            eq_self_iff_true, zero_mul]
    mul_zero := fun x => by
      induction x using EReal.rec <;>
        · simp only [(· * ·)]
          simp only [EReal.mul, ← EReal.coe_zero, zero_lt_one, if_true, if_false, lt_irrefl (0 : ℝ),
            eq_self_iff_true, mul_zero] }

/-! ### Real coercion -/


#print EReal.canLift /-
instance canLift : CanLift EReal ℝ coe fun r => r ≠ ⊤ ∧ r ≠ ⊥
    where prf x hx := by
    induction x using EReal.rec
    · simpa using hx
    · simp
    · simpa using hx
#align ereal.can_lift EReal.canLift
-/

#print EReal.toReal /-
/-- The map from extended reals to reals sending infinities to zero. -/
def toReal : EReal → ℝ
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => x
#align ereal.to_real EReal.toReal
-/

/- warning: ereal.to_real_top -> EReal.toReal_top is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (EReal.toReal (Top.top.{0} EReal EReal.hasTop)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (EReal.toReal (Top.top.{0} EReal EReal.instTopEReal)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_top EReal.toReal_topₓ'. -/
@[simp]
theorem toReal_top : toReal ⊤ = 0 :=
  rfl
#align ereal.to_real_top EReal.toReal_top

/- warning: ereal.to_real_bot -> EReal.toReal_bot is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (EReal.toReal (Bot.bot.{0} EReal EReal.hasBot)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (EReal.toReal (Bot.bot.{0} EReal instERealBot)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_bot EReal.toReal_botₓ'. -/
@[simp]
theorem toReal_bot : toReal ⊥ = 0 :=
  rfl
#align ereal.to_real_bot EReal.toReal_bot

/- warning: ereal.to_real_zero -> EReal.toReal_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (EReal.toReal (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (EReal.toReal (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_zero EReal.toReal_zeroₓ'. -/
@[simp]
theorem toReal_zero : toReal 0 = 0 :=
  rfl
#align ereal.to_real_zero EReal.toReal_zero

/- warning: ereal.to_real_one -> EReal.toReal_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (EReal.toReal (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (EReal.toReal (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_one EReal.toReal_oneₓ'. -/
@[simp]
theorem toReal_one : toReal 1 = 1 :=
  rfl
#align ereal.to_real_one EReal.toReal_one

#print EReal.toReal_coe /-
@[simp]
theorem toReal_coe (x : ℝ) : toReal (x : EReal) = x :=
  rfl
#align ereal.to_real_coe EReal.toReal_coe
-/

/- warning: ereal.bot_lt_coe -> EReal.bot_lt_coe is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)
but is expected to have type
  forall (x : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) (Real.toEReal x)
Case conversion may be inaccurate. Consider using '#align ereal.bot_lt_coe EReal.bot_lt_coeₓ'. -/
@[simp]
theorem bot_lt_coe (x : ℝ) : (⊥ : EReal) < x :=
  WithBot.bot_lt_coe _
#align ereal.bot_lt_coe EReal.bot_lt_coe

#print EReal.coe_ne_bot /-
@[simp]
theorem coe_ne_bot (x : ℝ) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe x).ne'
#align ereal.coe_ne_bot EReal.coe_ne_bot
-/

#print EReal.bot_ne_coe /-
@[simp]
theorem bot_ne_coe (x : ℝ) : (⊥ : EReal) ≠ x :=
  (bot_lt_coe x).Ne
#align ereal.bot_ne_coe EReal.bot_ne_coe
-/

/- warning: ereal.coe_lt_top -> EReal.coe_lt_top is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.coe_lt_top EReal.coe_lt_topₓ'. -/
@[simp]
theorem coe_lt_top (x : ℝ) : (x : EReal) < ⊤ :=
  by
  apply WithBot.coe_lt_coe.2
  exact WithTop.coe_lt_top _
#align ereal.coe_lt_top EReal.coe_lt_top

#print EReal.coe_ne_top /-
@[simp]
theorem coe_ne_top (x : ℝ) : (x : EReal) ≠ ⊤ :=
  (coe_lt_top x).Ne
#align ereal.coe_ne_top EReal.coe_ne_top
-/

#print EReal.top_ne_coe /-
@[simp]
theorem top_ne_coe (x : ℝ) : (⊤ : EReal) ≠ x :=
  (coe_lt_top x).ne'
#align ereal.top_ne_coe EReal.top_ne_coe
-/

/- warning: ereal.bot_lt_zero -> EReal.bot_lt_zero is a dubious translation:
lean 3 declaration is
  LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))
but is expected to have type
  LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))
Case conversion may be inaccurate. Consider using '#align ereal.bot_lt_zero EReal.bot_lt_zeroₓ'. -/
@[simp]
theorem bot_lt_zero : (⊥ : EReal) < 0 :=
  bot_lt_coe 0
#align ereal.bot_lt_zero EReal.bot_lt_zero

/- warning: ereal.bot_ne_zero -> EReal.bot_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} EReal (Bot.bot.{0} EReal EReal.hasBot) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))
but is expected to have type
  Ne.{1} EReal (Bot.bot.{0} EReal instERealBot) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))
Case conversion may be inaccurate. Consider using '#align ereal.bot_ne_zero EReal.bot_ne_zeroₓ'. -/
@[simp]
theorem bot_ne_zero : (⊥ : EReal) ≠ 0 :=
  (coe_ne_bot 0).symm
#align ereal.bot_ne_zero EReal.bot_ne_zero

/- warning: ereal.zero_ne_bot -> EReal.zero_ne_bot is a dubious translation:
lean 3 declaration is
  Ne.{1} EReal (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) (Bot.bot.{0} EReal EReal.hasBot)
but is expected to have type
  Ne.{1} EReal (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Bot.bot.{0} EReal instERealBot)
Case conversion may be inaccurate. Consider using '#align ereal.zero_ne_bot EReal.zero_ne_botₓ'. -/
@[simp]
theorem zero_ne_bot : (0 : EReal) ≠ ⊥ :=
  coe_ne_bot 0
#align ereal.zero_ne_bot EReal.zero_ne_bot

/- warning: ereal.zero_lt_top -> EReal.zero_lt_top is a dubious translation:
lean 3 declaration is
  LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.zero_lt_top EReal.zero_lt_topₓ'. -/
@[simp]
theorem zero_lt_top : (0 : EReal) < ⊤ :=
  coe_lt_top 0
#align ereal.zero_lt_top EReal.zero_lt_top

/- warning: ereal.zero_ne_top -> EReal.zero_ne_top is a dubious translation:
lean 3 declaration is
  Ne.{1} EReal (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  Ne.{1} EReal (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.zero_ne_top EReal.zero_ne_topₓ'. -/
@[simp]
theorem zero_ne_top : (0 : EReal) ≠ ⊤ :=
  coe_ne_top 0
#align ereal.zero_ne_top EReal.zero_ne_top

/- warning: ereal.top_ne_zero -> EReal.top_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} EReal (Top.top.{0} EReal EReal.hasTop) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))
but is expected to have type
  Ne.{1} EReal (Top.top.{0} EReal EReal.instTopEReal) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))
Case conversion may be inaccurate. Consider using '#align ereal.top_ne_zero EReal.top_ne_zeroₓ'. -/
@[simp]
theorem top_ne_zero : (⊤ : EReal) ≠ 0 :=
  (coe_ne_top 0).symm
#align ereal.top_ne_zero EReal.top_ne_zero

/- warning: ereal.coe_add -> EReal.coe_add is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) x y)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} EReal (Real.toEReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) x y)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Real.toEReal x) (Real.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.coe_add EReal.coe_addₓ'. -/
@[simp, norm_cast]
theorem coe_add (x y : ℝ) : (↑(x + y) : EReal) = x + y :=
  rfl
#align ereal.coe_add EReal.coe_add

/- warning: ereal.coe_mul -> EReal.coe_mul is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) x y)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} EReal (Real.toEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) x y)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Real.toEReal x) (Real.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.coe_mul EReal.coe_mulₓ'. -/
@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : (↑(x * y) : EReal) = x * y :=
  rfl
#align ereal.coe_mul EReal.coe_mul

#print EReal.coe_nsmul /-
@[norm_cast]
theorem coe_nsmul (n : ℕ) (x : ℝ) : (↑(n • x) : EReal) = n • x :=
  map_nsmul (⟨coe, coe_zero, coe_add⟩ : ℝ →+ EReal) _ _
#align ereal.coe_nsmul EReal.coe_nsmul
-/

/- warning: ereal.coe_bit0 clashes with [anonymous] -> [anonymous]
warning: ereal.coe_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (bit0.{0} Real Real.hasAdd x)) (bit0.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align ereal.coe_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ) : (↑(bit0 x) : EReal) = bit0 x :=
  rfl
#align ereal.coe_bit0 [anonymous]

/- warning: ereal.coe_bit1 clashes with [anonymous] -> [anonymous]
warning: ereal.coe_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (bit1.{0} Real Real.hasOne Real.hasAdd x)) (bit1.{0} EReal EReal.hasOne (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align ereal.coe_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ) : (↑(bit1 x) : EReal) = bit1 x :=
  rfl
#align ereal.coe_bit1 [anonymous]

/- warning: ereal.coe_eq_zero -> EReal.coe_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} EReal (Real.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_eq_zero EReal.coe_eq_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : EReal) = 0 ↔ x = 0 :=
  EReal.coe_eq_coe_iff
#align ereal.coe_eq_zero EReal.coe_eq_zero

/- warning: ereal.coe_eq_one -> EReal.coe_eq_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} EReal (Real.toEReal x) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_eq_one EReal.coe_eq_oneₓ'. -/
@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : EReal) = 1 ↔ x = 1 :=
  EReal.coe_eq_coe_iff
#align ereal.coe_eq_one EReal.coe_eq_one

/- warning: ereal.coe_ne_zero -> EReal.coe_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} EReal (Real.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ne_zero EReal.coe_ne_zeroₓ'. -/
theorem coe_ne_zero {x : ℝ} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  EReal.coe_ne_coe_iff
#align ereal.coe_ne_zero EReal.coe_ne_zero

/- warning: ereal.coe_ne_one -> EReal.coe_ne_one is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} EReal (Real.toEReal x) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))) (Ne.{1} Real x (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ne_one EReal.coe_ne_oneₓ'. -/
theorem coe_ne_one {x : ℝ} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  EReal.coe_ne_coe_iff
#align ereal.coe_ne_one EReal.coe_ne_one

/- warning: ereal.coe_nonneg -> EReal.coe_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Real.toEReal x)) (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align ereal.coe_nonneg EReal.coe_nonnegₓ'. -/
@[simp, norm_cast]
protected theorem coe_nonneg {x : ℝ} : (0 : EReal) ≤ x ↔ 0 ≤ x :=
  EReal.coe_le_coe_iff
#align ereal.coe_nonneg EReal.coe_nonneg

/- warning: ereal.coe_nonpos -> EReal.coe_nonpos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_nonpos EReal.coe_nonposₓ'. -/
@[simp, norm_cast]
protected theorem coe_nonpos {x : ℝ} : (x : EReal) ≤ 0 ↔ x ≤ 0 :=
  EReal.coe_le_coe_iff
#align ereal.coe_nonpos EReal.coe_nonpos

/- warning: ereal.coe_pos -> EReal.coe_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (Real.toEReal x)) (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)
Case conversion may be inaccurate. Consider using '#align ereal.coe_pos EReal.coe_posₓ'. -/
@[simp, norm_cast]
protected theorem coe_pos {x : ℝ} : (0 : EReal) < x ↔ 0 < x :=
  EReal.coe_lt_coe_iff
#align ereal.coe_pos EReal.coe_pos

/- warning: ereal.coe_neg' -> EReal.coe_neg' is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_neg' EReal.coe_neg'ₓ'. -/
@[simp, norm_cast]
protected theorem coe_neg' {x : ℝ} : (x : EReal) < 0 ↔ x < 0 :=
  EReal.coe_lt_coe_iff
#align ereal.coe_neg' EReal.coe_neg'

/- warning: ereal.to_real_le_to_real -> EReal.toReal_le_toReal is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (Ne.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.hasTop)) -> (LE.le.{0} Real Real.hasLe (EReal.toReal x) (EReal.toReal y))
but is expected to have type
  forall {x : EReal} {y : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (Ne.{1} EReal x (Bot.bot.{0} EReal instERealBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.instTopEReal)) -> (LE.le.{0} Real Real.instLEReal (EReal.toReal x) (EReal.toReal y))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_le_to_real EReal.toReal_le_toRealₓ'. -/
theorem toReal_le_toReal {x y : EReal} (h : x ≤ y) (hx : x ≠ ⊥) (hy : y ≠ ⊤) :
    x.toReal ≤ y.toReal := by
  lift x to ℝ
  · simp [hx, (h.trans_lt (lt_top_iff_ne_top.2 hy)).Ne]
  lift y to ℝ
  · simp [hy, ((bot_lt_iff_ne_bot.2 hx).trans_le h).ne']
  simpa using h
#align ereal.to_real_le_to_real EReal.toReal_le_toReal

#print EReal.coe_toReal /-
theorem coe_toReal {x : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) : (x.toReal : EReal) = x :=
  by
  induction x using EReal.rec
  · simpa using h'x
  · rfl
  · simpa using hx
#align ereal.coe_to_real EReal.coe_toReal
-/

/- warning: ereal.le_coe_to_real -> EReal.le_coe_toReal is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.hasTop)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (EReal.toReal x)))
but is expected to have type
  forall {x : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.instTopEReal)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (Real.toEReal (EReal.toReal x)))
Case conversion may be inaccurate. Consider using '#align ereal.le_coe_to_real EReal.le_coe_toRealₓ'. -/
theorem le_coe_toReal {x : EReal} (h : x ≠ ⊤) : x ≤ x.toReal :=
  by
  by_cases h' : x = ⊥
  · simp only [h', bot_le]
  · simp only [le_refl, coe_to_real h h']
#align ereal.le_coe_to_real EReal.le_coe_toReal

/- warning: ereal.coe_to_real_le -> EReal.coe_toReal_le is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (Ne.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (EReal.toReal x)) x)
but is expected to have type
  forall {x : EReal}, (Ne.{1} EReal x (Bot.bot.{0} EReal instERealBot)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal (EReal.toReal x)) x)
Case conversion may be inaccurate. Consider using '#align ereal.coe_to_real_le EReal.coe_toReal_leₓ'. -/
theorem coe_toReal_le {x : EReal} (h : x ≠ ⊥) : ↑x.toReal ≤ x :=
  by
  by_cases h' : x = ⊤
  · simp only [h', le_top]
  · simp only [le_refl, coe_to_real h' h]
#align ereal.coe_to_real_le EReal.coe_toReal_le

/- warning: ereal.eq_top_iff_forall_lt -> EReal.eq_top_iff_forall_lt is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Iff (Eq.{1} EReal x (Top.top.{0} EReal EReal.hasTop)) (forall (y : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y) x)
but is expected to have type
  forall (x : EReal), Iff (Eq.{1} EReal x (Top.top.{0} EReal EReal.instTopEReal)) (forall (y : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal y) x)
Case conversion may be inaccurate. Consider using '#align ereal.eq_top_iff_forall_lt EReal.eq_top_iff_forall_ltₓ'. -/
theorem eq_top_iff_forall_lt (x : EReal) : x = ⊤ ↔ ∀ y : ℝ, (y : EReal) < x :=
  by
  constructor
  · rintro rfl
    exact EReal.coe_lt_top
  · contrapose!
    intro h
    exact ⟨x.to_real, le_coe_to_real h⟩
#align ereal.eq_top_iff_forall_lt EReal.eq_top_iff_forall_lt

/- warning: ereal.eq_bot_iff_forall_lt -> EReal.eq_bot_iff_forall_lt is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Iff (Eq.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) (forall (y : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y))
but is expected to have type
  forall (x : EReal), Iff (Eq.{1} EReal x (Bot.bot.{0} EReal instERealBot)) (forall (y : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (Real.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.eq_bot_iff_forall_lt EReal.eq_bot_iff_forall_ltₓ'. -/
theorem eq_bot_iff_forall_lt (x : EReal) : x = ⊥ ↔ ∀ y : ℝ, x < (y : EReal) :=
  by
  constructor
  · rintro rfl
    exact bot_lt_coe
  · contrapose!
    intro h
    exact ⟨x.to_real, coe_to_real_le h⟩
#align ereal.eq_bot_iff_forall_lt EReal.eq_bot_iff_forall_lt

/-! ### ennreal coercion -/


#print EReal.toReal_coe_ennreal /-
@[simp]
theorem toReal_coe_ennreal : ∀ {x : ℝ≥0∞}, toReal (x : EReal) = ENNReal.toReal x
  | ⊤ => rfl
  | some x => rfl
#align ereal.to_real_coe_ennreal EReal.toReal_coe_ennreal
-/

/- warning: ereal.coe_ennreal_of_real -> EReal.coe_ennreal_ofReal is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (ENNReal.ofReal x)) (LinearOrder.max.{0} EReal (ConditionallyCompleteLinearOrder.toLinearOrder.{0} EReal (ConditionallyCompleteLinearOrderBot.toConditionallyCompleteLinearOrder.{0} EReal (CompleteLinearOrder.toConditionallyCompleteLinearOrderBot.{0} EReal EReal.completeLinearOrder))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))))
but is expected to have type
  forall {x : Real}, Eq.{1} EReal (ENNReal.toEReal (ENNReal.ofReal x)) (Real.toEReal (Max.max.{0} Real (LinearOrderedRing.toMax.{0} Real Real.instLinearOrderedRingReal) x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_of_real EReal.coe_ennreal_ofRealₓ'. -/
@[simp]
theorem coe_ennreal_ofReal {x : ℝ} : (ENNReal.ofReal x : EReal) = max x 0 :=
  rfl
#align ereal.coe_ennreal_of_real EReal.coe_ennreal_ofReal

/- warning: ereal.coe_nnreal_eq_coe_real -> EReal.coe_nnreal_eq_coe_real is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) x))
but is expected to have type
  forall (x : NNReal), Eq.{1} EReal (ENNReal.toEReal (ENNReal.some x)) (Real.toEReal (NNReal.toReal x))
Case conversion may be inaccurate. Consider using '#align ereal.coe_nnreal_eq_coe_real EReal.coe_nnreal_eq_coe_realₓ'. -/
theorem coe_nnreal_eq_coe_real (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) = (x : ℝ) :=
  rfl
#align ereal.coe_nnreal_eq_coe_real EReal.coe_nnreal_eq_coe_real

/- warning: ereal.coe_ennreal_zero -> EReal.coe_ennreal_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))
but is expected to have type
  Eq.{1} EReal (ENNReal.toEReal (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_zero EReal.coe_ennreal_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_zero : ((0 : ℝ≥0∞) : EReal) = 0 :=
  rfl
#align ereal.coe_ennreal_zero EReal.coe_ennreal_zero

/- warning: ereal.coe_ennreal_one -> EReal.coe_ennreal_one is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)))))) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))
but is expected to have type
  Eq.{1} EReal (ENNReal.toEReal (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_one EReal.coe_ennreal_oneₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_one : ((1 : ℝ≥0∞) : EReal) = 1 :=
  rfl
#align ereal.coe_ennreal_one EReal.coe_ennreal_one

/- warning: ereal.coe_ennreal_top -> EReal.coe_ennreal_top is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  Eq.{1} EReal (ENNReal.toEReal (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_top EReal.coe_ennreal_topₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_top : ((⊤ : ℝ≥0∞) : EReal) = ⊤ :=
  rfl
#align ereal.coe_ennreal_top EReal.coe_ennreal_top

/- warning: ereal.coe_ennreal_eq_top_iff -> EReal.coe_ennreal_eq_top_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) (Top.top.{0} EReal EReal.hasTop)) (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))
but is expected to have type
  forall {x : ENNReal}, Iff (Eq.{1} EReal (ENNReal.toEReal x) (Top.top.{0} EReal EReal.instTopEReal)) (Eq.{1} ENNReal x (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal))))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_eq_top_iff EReal.coe_ennreal_eq_top_iffₓ'. -/
@[simp]
theorem coe_ennreal_eq_top_iff : ∀ {x : ℝ≥0∞}, (x : EReal) = ⊤ ↔ x = ⊤
  | ⊤ => by simp
  | some x => by
    simp only [ENNReal.coe_ne_top, iff_false_iff, ENNReal.some_eq_coe]
    decide
#align ereal.coe_ennreal_eq_top_iff EReal.coe_ennreal_eq_top_iff

#print EReal.coe_nnreal_ne_top /-
theorem coe_nnreal_ne_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) ≠ ⊤ := by decide
#align ereal.coe_nnreal_ne_top EReal.coe_nnreal_ne_top
-/

/- warning: ereal.coe_nnreal_lt_top -> EReal.coe_nnreal_lt_top is a dubious translation:
lean 3 declaration is
  forall (x : NNReal), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal ENNReal (HasLiftT.mk.{1, 1} NNReal ENNReal (CoeTCₓ.coe.{1, 1} NNReal ENNReal (coeBase.{1, 1} NNReal ENNReal ENNReal.hasCoe))) x)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : NNReal), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (ENNReal.toEReal (ENNReal.some x)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.coe_nnreal_lt_top EReal.coe_nnreal_lt_topₓ'. -/
@[simp]
theorem coe_nnreal_lt_top (x : ℝ≥0) : ((x : ℝ≥0∞) : EReal) < ⊤ := by decide
#align ereal.coe_nnreal_lt_top EReal.coe_nnreal_lt_top

/- warning: ereal.coe_ennreal_strict_mono -> EReal.coe_ennreal_strictMono is a dubious translation:
lean 3 declaration is
  StrictMono.{0, 0} ENNReal EReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))))
but is expected to have type
  StrictMono.{0, 0} ENNReal EReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))) (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) ENNReal.toEReal
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_strict_mono EReal.coe_ennreal_strictMonoₓ'. -/
theorem coe_ennreal_strictMono : StrictMono (coe : ℝ≥0∞ → EReal)
  | ⊤, ⊤ => by simp
  | some x, ⊤ => by simp
  | ⊤, some y => by simp
  | some x, some y => by simp [coe_nnreal_eq_coe_real]
#align ereal.coe_ennreal_strict_mono EReal.coe_ennreal_strictMono

#print EReal.coe_ennreal_injective /-
theorem coe_ennreal_injective : Injective (coe : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.Injective
#align ereal.coe_ennreal_injective EReal.coe_ennreal_injective
-/

/- warning: ereal.coe_ennreal_le_coe_ennreal_iff -> EReal.coe_ennreal_le_coe_ennreal_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) y)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y)
but is expected to have type
  forall {x : ENNReal} {y : ENNReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (ENNReal.toEReal x) (ENNReal.toEReal y)) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) x y)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_le_coe_ennreal_iff EReal.coe_ennreal_le_coe_ennreal_iffₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_le_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≤ (y : EReal) ↔ x ≤ y :=
  coe_ennreal_strictMono.le_iff_le
#align ereal.coe_ennreal_le_coe_ennreal_iff EReal.coe_ennreal_le_coe_ennreal_iff

/- warning: ereal.coe_ennreal_lt_coe_ennreal_iff -> EReal.coe_ennreal_lt_coe_ennreal_iff is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal} {y : ENNReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) y)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) x y)
but is expected to have type
  forall {x : ENNReal} {y : ENNReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (ENNReal.toEReal x) (ENNReal.toEReal y)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) x y)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_lt_coe_ennreal_iff EReal.coe_ennreal_lt_coe_ennreal_iffₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_lt_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) < (y : EReal) ↔ x < y :=
  coe_ennreal_strictMono.lt_iff_lt
#align ereal.coe_ennreal_lt_coe_ennreal_iff EReal.coe_ennreal_lt_coe_ennreal_iff

#print EReal.coe_ennreal_eq_coe_ennreal_iff /-
@[simp, norm_cast]
theorem coe_ennreal_eq_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) = (y : EReal) ↔ x = y :=
  coe_ennreal_injective.eq_iff
#align ereal.coe_ennreal_eq_coe_ennreal_iff EReal.coe_ennreal_eq_coe_ennreal_iff
-/

#print EReal.coe_ennreal_ne_coe_ennreal_iff /-
theorem coe_ennreal_ne_coe_ennreal_iff {x y : ℝ≥0∞} : (x : EReal) ≠ (y : EReal) ↔ x ≠ y :=
  coe_ennreal_injective.ne_iff
#align ereal.coe_ennreal_ne_coe_ennreal_iff EReal.coe_ennreal_ne_coe_ennreal_iff
-/

/- warning: ereal.coe_ennreal_eq_zero -> EReal.coe_ennreal_eq_zero is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {x : ENNReal}, Iff (Eq.{1} EReal (ENNReal.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_eq_zero EReal.coe_ennreal_eq_zeroₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_eq_zero {x : ℝ≥0∞} : (x : EReal) = 0 ↔ x = 0 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_zero]
#align ereal.coe_ennreal_eq_zero EReal.coe_ennreal_eq_zero

/- warning: ereal.coe_ennreal_eq_one -> EReal.coe_ennreal_eq_one is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))) (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal}, Iff (Eq.{1} EReal (ENNReal.toEReal x) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))) (Eq.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_eq_one EReal.coe_ennreal_eq_oneₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_eq_one {x : ℝ≥0∞} : (x : EReal) = 1 ↔ x = 1 := by
  rw [← coe_ennreal_eq_coe_ennreal_iff, coe_ennreal_one]
#align ereal.coe_ennreal_eq_one EReal.coe_ennreal_eq_one

/- warning: ereal.coe_ennreal_ne_zero -> EReal.coe_ennreal_ne_zero is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (Ne.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))))
but is expected to have type
  forall {x : ENNReal}, Iff (Ne.{1} EReal (ENNReal.toEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_ne_zero EReal.coe_ennreal_ne_zeroₓ'. -/
@[norm_cast]
theorem coe_ennreal_ne_zero {x : ℝ≥0∞} : (x : EReal) ≠ 0 ↔ x ≠ 0 :=
  coe_ennreal_eq_zero.Not
#align ereal.coe_ennreal_ne_zero EReal.coe_ennreal_ne_zero

/- warning: ereal.coe_ennreal_ne_one -> EReal.coe_ennreal_ne_one is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (Ne.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) (OfNat.ofNat.{0} EReal 1 (OfNat.mk.{0} EReal 1 (One.one.{0} EReal EReal.hasOne)))) (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 1 (OfNat.mk.{0} ENNReal 1 (One.one.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne))))))
but is expected to have type
  forall {x : ENNReal}, Iff (Ne.{1} EReal (ENNReal.toEReal x) (OfNat.ofNat.{0} EReal 1 (One.toOfNat1.{0} EReal instERealOne))) (Ne.{1} ENNReal x (OfNat.ofNat.{0} ENNReal 1 (One.toOfNat1.{0} ENNReal (CanonicallyOrderedCommSemiring.toOne.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_ne_one EReal.coe_ennreal_ne_oneₓ'. -/
@[norm_cast]
theorem coe_ennreal_ne_one {x : ℝ≥0∞} : (x : EReal) ≠ 1 ↔ x ≠ 1 :=
  coe_ennreal_eq_one.Not
#align ereal.coe_ennreal_ne_one EReal.coe_ennreal_ne_one

/- warning: ereal.coe_ennreal_nonneg -> EReal.coe_ennreal_nonneg is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x)
but is expected to have type
  forall (x : ENNReal), LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (ENNReal.toEReal x)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_nonneg EReal.coe_ennreal_nonnegₓ'. -/
theorem coe_ennreal_nonneg (x : ℝ≥0∞) : (0 : EReal) ≤ x :=
  coe_ennreal_le_coe_ennreal_iff.2 (zero_le x)
#align ereal.coe_ennreal_nonneg EReal.coe_ennreal_nonneg

/- warning: ereal.coe_ennreal_pos -> EReal.coe_ennreal_pos is a dubious translation:
lean 3 declaration is
  forall {x : ENNReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero))) x)
but is expected to have type
  forall {x : ENNReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) (ENNReal.toEReal x)) (LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero)) x)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_pos EReal.coe_ennreal_posₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_pos {x : ℝ≥0∞} : (0 : EReal) < x ↔ 0 < x := by
  rw [← coe_ennreal_zero, coe_ennreal_lt_coe_ennreal_iff]
#align ereal.coe_ennreal_pos EReal.coe_ennreal_pos

/- warning: ereal.bot_lt_coe_ennreal -> EReal.bot_lt_coe_ennreal is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x)
but is expected to have type
  forall (x : ENNReal), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) (ENNReal.toEReal x)
Case conversion may be inaccurate. Consider using '#align ereal.bot_lt_coe_ennreal EReal.bot_lt_coe_ennrealₓ'. -/
@[simp]
theorem bot_lt_coe_ennreal (x : ℝ≥0∞) : (⊥ : EReal) < x :=
  (bot_lt_coe 0).trans_le (coe_ennreal_nonneg _)
#align ereal.bot_lt_coe_ennreal EReal.bot_lt_coe_ennreal

#print EReal.coe_ennreal_ne_bot /-
@[simp]
theorem coe_ennreal_ne_bot (x : ℝ≥0∞) : (x : EReal) ≠ ⊥ :=
  (bot_lt_coe_ennreal x).ne'
#align ereal.coe_ennreal_ne_bot EReal.coe_ennreal_ne_bot
-/

/- warning: ereal.coe_ennreal_add -> EReal.coe_ennreal_add is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : ENNReal), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x y)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) y))
but is expected to have type
  forall (x : ENNReal) (y : ENNReal), Eq.{1} EReal (ENNReal.toEReal (HAdd.hAdd.{0, 0, 0} ENNReal ENNReal ENNReal (instHAdd.{0} ENNReal (Distrib.toAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)))))))) x y)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (ENNReal.toEReal x) (ENNReal.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_add EReal.coe_ennreal_addₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_add (x y : ENNReal) : ((x + y : ℝ≥0∞) : EReal) = x + y := by
  cases x <;> cases y <;> rfl
#align ereal.coe_ennreal_add EReal.coe_ennreal_add

/- warning: ereal.coe_ennreal_mul -> EReal.coe_ennreal_mul is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (y : ENNReal), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) x y)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) y))
but is expected to have type
  forall (x : ENNReal) (y : ENNReal), Eq.{1} EReal (ENNReal.toEReal (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) x y)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (ENNReal.toEReal x) (ENNReal.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_mul EReal.coe_ennreal_mulₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_mul : ∀ x y : ℝ≥0∞, ((x * y : ℝ≥0∞) : EReal) = x * y
  | ⊤, ⊤ => rfl
  | ⊤, (y : ℝ≥0) => by
    rw [ENNReal.top_mul']; split_ifs
    · simp only [h, coe_ennreal_zero, mul_zero]
    · have A : (0 : ℝ) < y := by
        simp only [ENNReal.coe_eq_zero] at h
        exact NNReal.coe_pos.2 (bot_lt_iff_ne_bot.2 h)
      simp only [coe_nnreal_eq_coe_real, coe_ennreal_top, (· * ·), EReal.mul, A, if_true]
  | (x : ℝ≥0), ⊤ => by
    rw [ENNReal.mul_top']; split_ifs
    · simp only [h, coe_ennreal_zero, zero_mul]
    · have A : (0 : ℝ) < x := by
        simp only [ENNReal.coe_eq_zero] at h
        exact NNReal.coe_pos.2 (bot_lt_iff_ne_bot.2 h)
      simp only [coe_nnreal_eq_coe_real, coe_ennreal_top, (· * ·), EReal.mul, A, if_true]
  | (x : ℝ≥0), (y : ℝ≥0) => by
    simp only [← ENNReal.coe_mul, coe_nnreal_eq_coe_real, NNReal.coe_mul, EReal.coe_mul]
#align ereal.coe_ennreal_mul EReal.coe_ennreal_mul

#print EReal.coe_ennreal_nsmul /-
@[norm_cast]
theorem coe_ennreal_nsmul (n : ℕ) (x : ℝ≥0∞) : (↑(n • x) : EReal) = n • x :=
  map_nsmul (⟨coe, coe_ennreal_zero, coe_ennreal_add⟩ : ℝ≥0∞ →+ EReal) _ _
#align ereal.coe_ennreal_nsmul EReal.coe_ennreal_nsmul
-/

/- warning: ereal.coe_ennreal_bit0 clashes with [anonymous] -> [anonymous]
warning: ereal.coe_ennreal_bit0 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (bit0.{0} ENNReal (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) x)) (bit0.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_bit0 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ≥0∞) : (↑(bit0 x) : EReal) = bit0 x :=
  coe_ennreal_add _ _
#align ereal.coe_ennreal_bit0 [anonymous]

/- warning: ereal.coe_ennreal_bit1 clashes with [anonymous] -> [anonymous]
warning: ereal.coe_ennreal_bit1 -> [anonymous] is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (bit1.{0} ENNReal (AddMonoidWithOne.toOne.{0} ENNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.addCommMonoidWithOne)) (Distrib.toHasAdd.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) x)) (bit1.{0} EReal EReal.hasOne (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x))
but is expected to have type
  forall {x : Type.{u}} {β : Type.{v}}, (Nat -> x -> β) -> Nat -> (List.{u} x) -> (List.{v} β)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_bit1 [anonymous]ₓ'. -/
@[simp, norm_cast]
theorem [anonymous] (x : ℝ≥0∞) : (↑(bit1 x) : EReal) = bit1 x := by
  simp_rw [bit1, coe_ennreal_add, coe_ennreal_bit0, coe_ennreal_one]
#align ereal.coe_ennreal_bit1 [anonymous]

/-! ### Order -/


/- warning: ereal.exists_rat_btwn_of_lt -> EReal.exists_rat_btwn_of_lt is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a b) -> (Exists.{1} Rat (fun (x : Rat) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x))) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x)) b)))
but is expected to have type
  forall {a : EReal} {b : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a b) -> (Exists.{1} Rat (fun (x : Rat) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a (Real.toEReal (RatCast.ratCast.{0} Real Real.ratCast x))) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal (RatCast.ratCast.{0} Real Real.ratCast x)) b)))
Case conversion may be inaccurate. Consider using '#align ereal.exists_rat_btwn_of_lt EReal.exists_rat_btwn_of_ltₓ'. -/
theorem exists_rat_btwn_of_lt :
    ∀ {a b : EReal} (hab : a < b), ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b
  | ⊤, b, h => (not_top_lt h).elim
  | (a : ℝ), ⊥, h => (lt_irrefl _ ((bot_lt_coe a).trans h)).elim
  | (a : ℝ), (b : ℝ), h => by simp [exists_rat_btwn (EReal.coe_lt_coe_iff.1 h)]
  | (a : ℝ), ⊤, h =>
    let ⟨b, hab⟩ := exists_rat_gt a
    ⟨b, by simpa using hab, coe_lt_top _⟩
  | ⊥, ⊥, h => (lt_irrefl _ h).elim
  | ⊥, (a : ℝ), h =>
    let ⟨b, hab⟩ := exists_rat_lt a
    ⟨b, bot_lt_coe _, by simpa using hab⟩
  | ⊥, ⊤, h => ⟨0, bot_lt_coe _, coe_lt_top _⟩
#align ereal.exists_rat_btwn_of_lt EReal.exists_rat_btwn_of_lt

/- warning: ereal.lt_iff_exists_rat_btwn -> EReal.lt_iff_exists_rat_btwn is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a b) (Exists.{1} Rat (fun (x : Rat) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x))) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x)) b)))
but is expected to have type
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a b) (Exists.{1} Rat (fun (x : Rat) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a (Real.toEReal (RatCast.ratCast.{0} Real Real.ratCast x))) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal (RatCast.ratCast.{0} Real Real.ratCast x)) b)))
Case conversion may be inaccurate. Consider using '#align ereal.lt_iff_exists_rat_btwn EReal.lt_iff_exists_rat_btwnₓ'. -/
theorem lt_iff_exists_rat_btwn {a b : EReal} :
    a < b ↔ ∃ x : ℚ, a < (x : ℝ) ∧ ((x : ℝ) : EReal) < b :=
  ⟨fun hab => exists_rat_btwn_of_lt hab, fun ⟨x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_rat_btwn EReal.lt_iff_exists_rat_btwn

/- warning: ereal.lt_iff_exists_real_btwn -> EReal.lt_iff_exists_real_btwn is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a b) (Exists.{1} Real (fun (x : Real) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) b)))
but is expected to have type
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a b) (Exists.{1} Real (fun (x : Real) => And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a (Real.toEReal x)) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Real.toEReal x) b)))
Case conversion may be inaccurate. Consider using '#align ereal.lt_iff_exists_real_btwn EReal.lt_iff_exists_real_btwnₓ'. -/
theorem lt_iff_exists_real_btwn {a b : EReal} : a < b ↔ ∃ x : ℝ, a < x ∧ (x : EReal) < b :=
  ⟨fun hab =>
    let ⟨x, ax, xb⟩ := exists_rat_btwn_of_lt hab
    ⟨(x : ℝ), ax, xb⟩,
    fun ⟨x, ax, xb⟩ => ax.trans xb⟩
#align ereal.lt_iff_exists_real_btwn EReal.lt_iff_exists_real_btwn

/- warning: ereal.ne_top_bot_equiv_real -> EReal.neTopBotEquivReal is a dubious translation:
lean 3 declaration is
  Equiv.{1, 1} (coeSort.{1, 2} (Set.{0} EReal) Type (Set.hasCoeToSort.{0} EReal) (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.booleanAlgebra.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.hasInsert.{0} EReal) (Bot.bot.{0} EReal EReal.hasBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.hasSingleton.{0} EReal) (Top.top.{0} EReal EReal.hasTop))))) Real
but is expected to have type
  Equiv.{1, 1} (Set.Elem.{0} EReal (HasCompl.compl.{0} (Set.{0} EReal) (BooleanAlgebra.toHasCompl.{0} (Set.{0} EReal) (Set.instBooleanAlgebraSet.{0} EReal)) (Insert.insert.{0, 0} EReal (Set.{0} EReal) (Set.instInsertSet.{0} EReal) (Bot.bot.{0} EReal instERealBot) (Singleton.singleton.{0, 0} EReal (Set.{0} EReal) (Set.instSingletonSet.{0} EReal) (Top.top.{0} EReal EReal.instTopEReal))))) Real
Case conversion may be inaccurate. Consider using '#align ereal.ne_top_bot_equiv_real EReal.neTopBotEquivRealₓ'. -/
/-- The set of numbers in `ereal` that are not equal to `±∞` is equivalent to `ℝ`. -/
def neTopBotEquivReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ ℝ
    where
  toFun x := EReal.toReal x
  invFun x := ⟨x, by simp⟩
  left_inv := fun ⟨x, hx⟩ =>
    Subtype.eq <| by
      lift x to ℝ
      · simpa [not_or, and_comm'] using hx
      · simp
  right_inv x := by simp
#align ereal.ne_top_bot_equiv_real EReal.neTopBotEquivReal

/-! ### Addition -/


/- warning: ereal.add_bot -> EReal.add_bot is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x (Bot.bot.{0} EReal EReal.hasBot)) (Bot.bot.{0} EReal EReal.hasBot)
but is expected to have type
  forall (x : EReal), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x (Bot.bot.{0} EReal instERealBot)) (Bot.bot.{0} EReal instERealBot)
Case conversion may be inaccurate. Consider using '#align ereal.add_bot EReal.add_botₓ'. -/
@[simp]
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _
#align ereal.add_bot EReal.add_bot

/- warning: ereal.bot_add -> EReal.bot_add is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Bot.bot.{0} EReal EReal.hasBot) x) (Bot.bot.{0} EReal EReal.hasBot)
but is expected to have type
  forall (x : EReal), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Bot.bot.{0} EReal instERealBot) x) (Bot.bot.{0} EReal instERealBot)
Case conversion may be inaccurate. Consider using '#align ereal.bot_add EReal.bot_addₓ'. -/
@[simp]
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _
#align ereal.bot_add EReal.bot_add

/- warning: ereal.top_add_top -> EReal.top_add_top is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Top.top.{0} EReal EReal.hasTop) (Top.top.{0} EReal EReal.hasTop)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Top.top.{0} EReal EReal.instTopEReal) (Top.top.{0} EReal EReal.instTopEReal)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.top_add_top EReal.top_add_topₓ'. -/
@[simp]
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl
#align ereal.top_add_top EReal.top_add_top

/- warning: ereal.top_add_coe -> EReal.top_add_coe is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : Real), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.top_add_coe EReal.top_add_coeₓ'. -/
@[simp]
theorem top_add_coe (x : ℝ) : (⊤ : EReal) + x = ⊤ :=
  rfl
#align ereal.top_add_coe EReal.top_add_coe

/- warning: ereal.coe_add_top -> EReal.coe_add_top is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : Real), Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.coe_add_top EReal.coe_add_topₓ'. -/
@[simp]
theorem coe_add_top (x : ℝ) : (x : EReal) + ⊤ = ⊤ :=
  rfl
#align ereal.coe_add_top EReal.coe_add_top

/- warning: ereal.to_real_add -> EReal.toReal_add is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal y (Bot.bot.{0} EReal EReal.hasBot)) -> (Eq.{1} Real (EReal.toReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (EReal.toReal x) (EReal.toReal y)))
but is expected to have type
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal x (Bot.bot.{0} EReal instERealBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal y (Bot.bot.{0} EReal instERealBot)) -> (Eq.{1} Real (EReal.toReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (EReal.toReal x) (EReal.toReal y)))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_add EReal.toReal_addₓ'. -/
theorem toReal_add :
    ∀ {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥),
      toReal (x + y) = toReal x + toReal y
  | ⊥, y, hx, h'x, hy, h'y => (h'x rfl).elim
  | ⊤, y, hx, h'x, hy, h'y => (hx rfl).elim
  | x, ⊤, hx, h'x, hy, h'y => (hy rfl).elim
  | x, ⊥, hx, h'x, hy, h'y => (h'y rfl).elim
  | (x : ℝ), (y : ℝ), hx, h'x, hy, h'y => by simp [← EReal.coe_add]
#align ereal.to_real_add EReal.toReal_add

/- warning: ereal.add_lt_add_right_coe -> EReal.add_lt_add_right_coe is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (forall (z : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) z)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) y ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) z)))
but is expected to have type
  forall {x : EReal} {y : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (forall (z : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x (Real.toEReal z)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) y (Real.toEReal z)))
Case conversion may be inaccurate. Consider using '#align ereal.add_lt_add_right_coe EReal.add_lt_add_right_coeₓ'. -/
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z :=
  by
  induction x using EReal.rec <;> induction y using EReal.rec
  · exact (lt_irrefl _ h).elim
  · simp only [← coe_add, bot_add, bot_lt_coe]
  · simp
  · exact (lt_irrefl _ (h.trans (bot_lt_coe x))).elim
  · norm_cast  at h⊢
    exact add_lt_add_right h _
  · simp only [← coe_add, top_add_coe, coe_lt_top]
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
  · exact (lt_irrefl _ (h.trans_le le_top)).elim
#align ereal.add_lt_add_right_coe EReal.add_lt_add_right_coe

/- warning: ereal.add_lt_add_of_lt_of_le -> EReal.add_lt_add_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) z t) -> (Ne.{1} EReal z (Bot.bot.{0} EReal EReal.hasBot)) -> (Ne.{1} EReal t (Top.top.{0} EReal EReal.hasTop)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x z) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) y t))
but is expected to have type
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) z t) -> (Ne.{1} EReal z (Bot.bot.{0} EReal instERealBot)) -> (Ne.{1} EReal t (Top.top.{0} EReal EReal.instTopEReal)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x z) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) y t))
Case conversion may be inaccurate. Consider using '#align ereal.add_lt_add_of_lt_of_le EReal.add_lt_add_of_lt_of_leₓ'. -/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t := by
  induction z using EReal.rec
  · simpa only using hz
  ·
    calc
      x + z < y + z := add_lt_add_right_coe h _
      _ ≤ y + t := add_le_add le_rfl h'
      
  · exact (ht (top_le_iff.1 h')).elim
#align ereal.add_lt_add_of_lt_of_le EReal.add_lt_add_of_lt_of_le

/- warning: ereal.add_lt_add_left_coe -> EReal.add_lt_add_left_coe is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (forall (z : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) z) x) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) z) y))
but is expected to have type
  forall {x : EReal} {y : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (forall (z : Real), LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Real.toEReal z) x) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) (Real.toEReal z) y))
Case conversion may be inaccurate. Consider using '#align ereal.add_lt_add_left_coe EReal.add_lt_add_left_coeₓ'. -/
theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z
#align ereal.add_lt_add_left_coe EReal.add_lt_add_left_coe

/- warning: ereal.add_lt_add -> EReal.add_lt_add is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) z t) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x z) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) y t))
but is expected to have type
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) z t) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x z) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) y t))
Case conversion may be inaccurate. Consider using '#align ereal.add_lt_add EReal.add_lt_addₓ'. -/
theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t :=
  by
  induction x using EReal.rec
  · simp [bot_lt_iff_ne_bot, h1.ne', (bot_le.trans_lt h2).ne']
  ·
    calc
      (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
      _ ≤ y + t := add_le_add h1.le le_rfl
      
  · exact (lt_irrefl _ (h1.trans_le le_top)).elim
#align ereal.add_lt_add EReal.add_lt_add

/- warning: ereal.add_eq_bot_iff -> EReal.add_eq_bot_iff is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, Iff (Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x y) (Bot.bot.{0} EReal EReal.hasBot)) (Or (Eq.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) (Eq.{1} EReal y (Bot.bot.{0} EReal EReal.hasBot)))
but is expected to have type
  forall {x : EReal} {y : EReal}, Iff (Eq.{1} EReal (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x y) (Bot.bot.{0} EReal instERealBot)) (Or (Eq.{1} EReal x (Bot.bot.{0} EReal instERealBot)) (Eq.{1} EReal y (Bot.bot.{0} EReal instERealBot)))
Case conversion may be inaccurate. Consider using '#align ereal.add_eq_bot_iff EReal.add_eq_bot_iffₓ'. -/
@[simp]
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ := by
  induction x using EReal.rec <;> induction y using EReal.rec <;> simp [← EReal.coe_add]
#align ereal.add_eq_bot_iff EReal.add_eq_bot_iff

/- warning: ereal.bot_lt_add_iff -> EReal.bot_lt_add_iff is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x y)) (And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) x) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Bot.bot.{0} EReal EReal.hasBot) y))
but is expected to have type
  forall {x : EReal} {y : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x y)) (And (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) x) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Bot.bot.{0} EReal instERealBot) y))
Case conversion may be inaccurate. Consider using '#align ereal.bot_lt_add_iff EReal.bot_lt_add_iffₓ'. -/
@[simp]
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot, not_or]
#align ereal.bot_lt_add_iff EReal.bot_lt_add_iff

/- warning: ereal.add_lt_top -> EReal.add_lt_top is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.hasTop)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toHasAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal EReal.addMonoid))) x y) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.instTopEReal)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HAdd.hAdd.{0, 0, 0} EReal EReal EReal (instHAdd.{0} EReal (AddZeroClass.toAdd.{0} EReal (AddMonoid.toAddZeroClass.{0} EReal instERealAddMonoid))) x y) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.add_lt_top EReal.add_lt_topₓ'. -/
theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ :=
  by
  rw [← EReal.top_add_top]
  exact EReal.add_lt_add hx.lt_top hy.lt_top
#align ereal.add_lt_top EReal.add_lt_top

/-! ### Negation -/


#print EReal.neg /-
/-- negation on `ereal` -/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)
#align ereal.neg EReal.neg
-/

instance : Neg EReal :=
  ⟨EReal.neg⟩

instance : SubNegZeroMonoid EReal :=
  { EReal.addMonoid, EReal.hasNeg with
    neg_zero := by
      change ((-0 : ℝ) : EReal) = 0
      simp }

/- warning: ereal.neg_def clashes with ereal.coe_neg -> EReal.coe_neg
warning: ereal.neg_def -> EReal.coe_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (Neg.neg.{0} Real Real.hasNeg x)) (Neg.neg.{0} EReal EReal.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} EReal (Real.toEReal (Neg.neg.{0} Real Real.instNegReal x)) (Neg.neg.{0} EReal EReal.instNegEReal (Real.toEReal x))
Case conversion may be inaccurate. Consider using '#align ereal.neg_def EReal.coe_negₓ'. -/
@[norm_cast]
protected theorem coe_neg (x : ℝ) : ((-x : ℝ) : EReal) = -x :=
  rfl
#align ereal.neg_def EReal.coe_neg

#print EReal.neg_top /-
@[simp]
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl
#align ereal.neg_top EReal.neg_top
-/

#print EReal.neg_bot /-
@[simp]
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl
#align ereal.neg_bot EReal.neg_bot
-/

/- warning: ereal.coe_neg -> EReal.coe_neg is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (Neg.neg.{0} Real Real.hasNeg x)) (Neg.neg.{0} EReal EReal.hasNeg ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))
but is expected to have type
  forall (x : Real), Eq.{1} EReal (Real.toEReal (Neg.neg.{0} Real Real.instNegReal x)) (Neg.neg.{0} EReal EReal.instNegEReal (Real.toEReal x))
Case conversion may be inaccurate. Consider using '#align ereal.coe_neg EReal.coe_negₓ'. -/
@[simp, norm_cast]
theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -x :=
  rfl
#align ereal.coe_neg EReal.coe_neg

/- warning: ereal.coe_sub -> EReal.coe_sub is a dubious translation:
lean 3 declaration is
  forall (x : Real) (y : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) x y)) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) y))
but is expected to have type
  forall (x : Real) (y : Real), Eq.{1} EReal (Real.toEReal (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) x y)) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (Real.toEReal x) (Real.toEReal y))
Case conversion may be inaccurate. Consider using '#align ereal.coe_sub EReal.coe_subₓ'. -/
@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : (↑(x - y) : EReal) = x - y :=
  rfl
#align ereal.coe_sub EReal.coe_sub

/- warning: ereal.coe_zsmul -> EReal.coe_zsmul is a dubious translation:
lean 3 declaration is
  forall (n : Int) (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (SMul.smul.{0, 0} Int Real (SubNegMonoid.SMulInt.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.addGroup)) n x)) (SMul.smul.{0, 0} Int EReal (SubNegMonoid.SMulInt.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid)) n ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))
but is expected to have type
  forall (n : Int) (x : Real), Eq.{1} EReal (Real.toEReal (HSMul.hSMul.{0, 0, 0} Int Real Real (instHSMul.{0, 0} Int Real (SubNegMonoid.SMulInt.{0} Real (AddGroup.toSubNegMonoid.{0} Real Real.instAddGroupReal))) n x)) (HSMul.hSMul.{0, 0, 0} Int EReal EReal (instHSMul.{0, 0} Int EReal (SubNegMonoid.SMulInt.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) n (Real.toEReal x))
Case conversion may be inaccurate. Consider using '#align ereal.coe_zsmul EReal.coe_zsmulₓ'. -/
@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • x :=
  map_zsmul' (⟨coe, coe_zero, coe_add⟩ : ℝ →+ EReal) coe_neg _ _
#align ereal.coe_zsmul EReal.coe_zsmul

instance : InvolutiveNeg EReal where
  neg := Neg.neg
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => by
      norm_cast
      simp [neg_neg a]

/- warning: ereal.to_real_neg -> EReal.toReal_neg is a dubious translation:
lean 3 declaration is
  forall {a : EReal}, Eq.{1} Real (EReal.toReal (Neg.neg.{0} EReal EReal.hasNeg a)) (Neg.neg.{0} Real Real.hasNeg (EReal.toReal a))
but is expected to have type
  forall {a : EReal}, Eq.{1} Real (EReal.toReal (Neg.neg.{0} EReal EReal.instNegEReal a)) (Neg.neg.{0} Real Real.instNegReal (EReal.toReal a))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_neg EReal.toReal_negₓ'. -/
@[simp]
theorem toReal_neg : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl
#align ereal.to_real_neg EReal.toReal_neg

#print EReal.neg_eq_top_iff /-
@[simp]
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_top_iff EReal.neg_eq_top_iff
-/

#print EReal.neg_eq_bot_iff /-
@[simp]
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_bot_iff EReal.neg_eq_bot_iff
-/

/- warning: ereal.neg_eq_zero_iff -> EReal.neg_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, Iff (Eq.{1} EReal (Neg.neg.{0} EReal EReal.hasNeg x) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (Eq.{1} EReal x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))))
but is expected to have type
  forall {x : EReal}, Iff (Eq.{1} EReal (Neg.neg.{0} EReal EReal.instNegEReal x) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (Eq.{1} EReal x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)))
Case conversion may be inaccurate. Consider using '#align ereal.neg_eq_zero_iff EReal.neg_eq_zero_iffₓ'. -/
@[simp]
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  by
  rw [neg_eq_iff_neg_eq]
  simp [eq_comm]
#align ereal.neg_eq_zero_iff EReal.neg_eq_zero_iff

/- warning: ereal.neg_le_of_neg_le -> EReal.neg_le_of_neg_le is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg a) b) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg b) a)
but is expected to have type
  forall {a : EReal} {b : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal a) b) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal b) a)
Case conversion may be inaccurate. Consider using '#align ereal.neg_le_of_neg_le EReal.neg_le_of_neg_leₓ'. -/
/-- if `-a ≤ b` then `-b ≤ a` on `ereal`. -/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a :=
  by
  induction a using EReal.rec <;> induction b using EReal.rec
  · exact h
  · simpa only [coe_ne_top, neg_bot, top_le_iff] using h
  · exact bot_le
  · simpa only [coe_ne_top, le_bot_iff] using h
  · norm_cast  at h⊢
    exact neg_le.1 h
  · exact bot_le
  · exact le_top
  · exact le_top
  · exact le_top
#align ereal.neg_le_of_neg_le EReal.neg_le_of_neg_le

/- warning: ereal.neg_le -> EReal.neg_le is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg a) b) (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg b) a)
but is expected to have type
  forall {a : EReal} {b : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal a) b) (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal b) a)
Case conversion may be inaccurate. Consider using '#align ereal.neg_le EReal.neg_leₓ'. -/
/-- `-a ≤ b ↔ -b ≤ a` on `ereal`. -/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a :=
  ⟨EReal.neg_le_of_neg_le, EReal.neg_le_of_neg_le⟩
#align ereal.neg_le EReal.neg_le

/- warning: ereal.le_neg_of_le_neg -> EReal.le_neg_of_le_neg is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) a (Neg.neg.{0} EReal EReal.hasNeg b)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) b (Neg.neg.{0} EReal EReal.hasNeg a))
but is expected to have type
  forall {a : EReal} {b : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) a (Neg.neg.{0} EReal EReal.instNegEReal b)) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) b (Neg.neg.{0} EReal EReal.instNegEReal a))
Case conversion may be inaccurate. Consider using '#align ereal.le_neg_of_le_neg EReal.le_neg_of_le_negₓ'. -/
/-- `a ≤ -b → b ≤ -a` on ereal -/
theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := by
  rwa [← neg_neg b, EReal.neg_le, neg_neg]
#align ereal.le_neg_of_le_neg EReal.le_neg_of_le_neg

/- warning: ereal.neg_le_neg_iff -> EReal.neg_le_neg_iff is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg a) (Neg.neg.{0} EReal EReal.hasNeg b)) (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) b a)
but is expected to have type
  forall {a : EReal} {b : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal a) (Neg.neg.{0} EReal EReal.instNegEReal b)) (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) b a)
Case conversion may be inaccurate. Consider using '#align ereal.neg_le_neg_iff EReal.neg_le_neg_iffₓ'. -/
@[simp]
theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := by conv_lhs => rw [EReal.neg_le, neg_neg]
#align ereal.neg_le_neg_iff EReal.neg_le_neg_iff

/- warning: ereal.neg_order_iso -> EReal.negOrderIso is a dubious translation:
lean 3 declaration is
  OrderIso.{0, 0} EReal (OrderDual.{0} EReal) (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OrderDual.hasLe.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))))
but is expected to have type
  OrderIso.{0, 0} EReal (OrderDual.{0} EReal) (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OrderDual.instLEOrderDual.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)))
Case conversion may be inaccurate. Consider using '#align ereal.neg_order_iso EReal.negOrderIsoₓ'. -/
/-- Negation as an order reversing isomorphism on `ereal`. -/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -x.ofDual
    map_rel_iff' := fun x y => neg_le_neg_iff }
#align ereal.neg_order_iso EReal.negOrderIso

/- warning: ereal.neg_lt_of_neg_lt -> EReal.neg_lt_of_neg_lt is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg a) b) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg b) a)
but is expected to have type
  forall {a : EReal} {b : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal a) b) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal b) a)
Case conversion may be inaccurate. Consider using '#align ereal.neg_lt_of_neg_lt EReal.neg_lt_of_neg_ltₓ'. -/
theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a :=
  by
  apply lt_of_le_of_ne (EReal.neg_le_of_neg_le h.le)
  intro H
  rw [← H, neg_neg] at h
  exact lt_irrefl _ h
#align ereal.neg_lt_of_neg_lt EReal.neg_lt_of_neg_lt

/- warning: ereal.neg_lt_iff_neg_lt -> EReal.neg_lt_iff_neg_lt is a dubious translation:
lean 3 declaration is
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg a) b) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (Neg.neg.{0} EReal EReal.hasNeg b) a)
but is expected to have type
  forall {a : EReal} {b : EReal}, Iff (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal a) b) (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (Neg.neg.{0} EReal EReal.instNegEReal b) a)
Case conversion may be inaccurate. Consider using '#align ereal.neg_lt_iff_neg_lt EReal.neg_lt_iff_neg_ltₓ'. -/
theorem neg_lt_iff_neg_lt {a b : EReal} : -a < b ↔ -b < a :=
  ⟨fun h => EReal.neg_lt_of_neg_lt h, fun h => EReal.neg_lt_of_neg_lt h⟩
#align ereal.neg_lt_iff_neg_lt EReal.neg_lt_iff_neg_lt

/-!
### Subtraction

Subtraction on `ereal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `ereal`, beyond `sub_neg_zero_monoid`, because of this bad behavior.
-/


/- warning: ereal.bot_sub -> EReal.bot_sub is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) (Bot.bot.{0} EReal EReal.hasBot) x) (Bot.bot.{0} EReal EReal.hasBot)
but is expected to have type
  forall (x : EReal), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (Bot.bot.{0} EReal instERealBot) x) (Bot.bot.{0} EReal instERealBot)
Case conversion may be inaccurate. Consider using '#align ereal.bot_sub EReal.bot_subₓ'. -/
@[simp]
theorem bot_sub (x : EReal) : ⊥ - x = ⊥ :=
  bot_add x
#align ereal.bot_sub EReal.bot_sub

/- warning: ereal.sub_top -> EReal.sub_top is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) x (Top.top.{0} EReal EReal.hasTop)) (Bot.bot.{0} EReal EReal.hasBot)
but is expected to have type
  forall (x : EReal), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) x (Top.top.{0} EReal EReal.instTopEReal)) (Bot.bot.{0} EReal instERealBot)
Case conversion may be inaccurate. Consider using '#align ereal.sub_top EReal.sub_topₓ'. -/
@[simp]
theorem sub_top (x : EReal) : x - ⊤ = ⊥ :=
  add_bot x
#align ereal.sub_top EReal.sub_top

/- warning: ereal.top_sub_bot -> EReal.top_sub_bot is a dubious translation:
lean 3 declaration is
  Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) (Top.top.{0} EReal EReal.hasTop) (Bot.bot.{0} EReal EReal.hasBot)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (Top.top.{0} EReal EReal.instTopEReal) (Bot.bot.{0} EReal instERealBot)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.top_sub_bot EReal.top_sub_botₓ'. -/
@[simp]
theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ :=
  rfl
#align ereal.top_sub_bot EReal.top_sub_bot

/- warning: ereal.top_sub_coe -> EReal.top_sub_coe is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : Real), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.top_sub_coe EReal.top_sub_coeₓ'. -/
@[simp]
theorem top_sub_coe (x : ℝ) : (⊤ : EReal) - x = ⊤ :=
  rfl
#align ereal.top_sub_coe EReal.top_sub_coe

/- warning: ereal.coe_sub_bot -> EReal.coe_sub_bot is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Bot.bot.{0} EReal EReal.hasBot)) (Top.top.{0} EReal EReal.hasTop)
but is expected to have type
  forall (x : Real), Eq.{1} EReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (Real.toEReal x) (Bot.bot.{0} EReal instERealBot)) (Top.top.{0} EReal EReal.instTopEReal)
Case conversion may be inaccurate. Consider using '#align ereal.coe_sub_bot EReal.coe_sub_botₓ'. -/
@[simp]
theorem coe_sub_bot (x : ℝ) : (x : EReal) - ⊥ = ⊤ :=
  rfl
#align ereal.coe_sub_bot EReal.coe_sub_bot

/- warning: ereal.sub_le_sub -> EReal.sub_le_sub is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) t z) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) x z) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) y t))
but is expected to have type
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) t z) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) x z) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) y t))
Case conversion may be inaccurate. Consider using '#align ereal.sub_le_sub EReal.sub_le_subₓ'. -/
theorem sub_le_sub {x y z t : EReal} (h : x ≤ y) (h' : t ≤ z) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')
#align ereal.sub_le_sub EReal.sub_le_sub

/- warning: ereal.sub_lt_sub_of_lt_of_le -> EReal.sub_lt_sub_of_lt_of_le is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) z t) -> (Ne.{1} EReal z (Bot.bot.{0} EReal EReal.hasBot)) -> (Ne.{1} EReal t (Top.top.{0} EReal EReal.hasTop)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) x t) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) y z))
but is expected to have type
  forall {x : EReal} {y : EReal} {z : EReal} {t : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) -> (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) z t) -> (Ne.{1} EReal z (Bot.bot.{0} EReal instERealBot)) -> (Ne.{1} EReal t (Top.top.{0} EReal EReal.instTopEReal)) -> (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) x t) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) y z))
Case conversion may be inaccurate. Consider using '#align ereal.sub_lt_sub_of_lt_of_le EReal.sub_lt_sub_of_lt_of_leₓ'. -/
theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])
#align ereal.sub_lt_sub_of_lt_of_le EReal.sub_lt_sub_of_lt_of_le

/- warning: ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal -> EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal EReal (HasLiftT.mk.{1, 1} NNReal EReal (CoeTCₓ.coe.{1, 1} NNReal EReal (coeTrans.{1, 1, 1} NNReal ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal) ENNReal.hasCoe))) (Real.toNNReal x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal EReal (HasLiftT.mk.{1, 1} NNReal EReal (CoeTCₓ.coe.{1, 1} NNReal EReal (coeTrans.{1, 1, 1} NNReal ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal) ENNReal.hasCoe))) (Real.toNNReal (Neg.neg.{0} Real Real.hasNeg x))))
but is expected to have type
  forall (x : Real), Eq.{1} EReal (Real.toEReal x) (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) (ENNReal.toEReal (ENNReal.some (Real.toNNReal x))) (ENNReal.toEReal (ENNReal.some (Real.toNNReal (Neg.neg.{0} Real Real.instNegReal x)))))
Case conversion may be inaccurate. Consider using '#align ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNRealₓ'. -/
theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) :=
  by
  rcases le_or_lt 0 x with (h | h)
  · have : Real.toNNReal x = ⟨x, h⟩ := by
      ext
      simp [h]
    simp only [Real.toNNReal_of_nonpos (neg_nonpos.mpr h), this, sub_zero, ENNReal.coe_zero,
      coe_ennreal_zero, coe_coe]
    rfl
  · have : (x : EReal) = -(-x : ℝ) := by simp
    conv_lhs => rw [this]
    have : Real.toNNReal (-x) = ⟨-x, neg_nonneg.mpr h.le⟩ :=
      by
      ext
      simp [neg_nonneg.mpr h.le]
    simp only [Real.toNNReal_of_nonpos h.le, this, zero_sub, neg_inj, coe_neg, ENNReal.coe_zero,
      coe_ennreal_zero, coe_coe]
    rfl
#align ereal.coe_real_ereal_eq_coe_to_nnreal_sub_coe_to_nnreal EReal.coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal

/- warning: ereal.to_real_sub -> EReal.toReal_sub is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal x (Bot.bot.{0} EReal EReal.hasBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.hasTop)) -> (Ne.{1} EReal y (Bot.bot.{0} EReal EReal.hasBot)) -> (Eq.{1} Real (EReal.toReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toHasSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.subNegZeroMonoid))) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (EReal.toReal x) (EReal.toReal y)))
but is expected to have type
  forall {x : EReal} {y : EReal}, (Ne.{1} EReal x (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal x (Bot.bot.{0} EReal instERealBot)) -> (Ne.{1} EReal y (Top.top.{0} EReal EReal.instTopEReal)) -> (Ne.{1} EReal y (Bot.bot.{0} EReal instERealBot)) -> (Eq.{1} Real (EReal.toReal (HSub.hSub.{0, 0, 0} EReal EReal EReal (instHSub.{0} EReal (SubNegMonoid.toSub.{0} EReal (SubNegZeroMonoid.toSubNegMonoid.{0} EReal EReal.instSubNegZeroMonoidEReal))) x y)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (EReal.toReal x) (EReal.toReal y)))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_sub EReal.toReal_subₓ'. -/
theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x - y) = toReal x - toReal y :=
  by
  rw [sub_eq_add_neg, to_real_add hx h'x, to_real_neg]
  · rfl
  · simpa using hy
  · simpa using h'y
#align ereal.to_real_sub EReal.toReal_sub

/-! ### Multiplication -/


#print EReal.mul_comm /-
protected theorem mul_comm (x y : EReal) : x * y = y * x :=
  by
  induction x using EReal.rec <;> induction y using EReal.rec <;> try rfl
  dsimp only [(· * ·)]
  simp only [EReal.mul, mul_comm]
#align ereal.mul_comm EReal.mul_comm
-/

#print EReal.top_mul_top /-
@[simp]
theorem top_mul_top : (⊤ : EReal) * ⊤ = ⊤ :=
  rfl
#align ereal.top_mul_top EReal.top_mul_top
-/

#print EReal.top_mul_bot /-
@[simp]
theorem top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ :=
  rfl
#align ereal.top_mul_bot EReal.top_mul_bot
-/

#print EReal.bot_mul_top /-
@[simp]
theorem bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ :=
  rfl
#align ereal.bot_mul_top EReal.bot_mul_top
-/

#print EReal.bot_mul_bot /-
@[simp]
theorem bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ :=
  rfl
#align ereal.bot_mul_bot EReal.bot_mul_bot
-/

/- warning: ereal.mul_top_of_pos -> EReal.mul_top_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x (Top.top.{0} EReal EReal.hasTop)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x (Top.top.{0} EReal EReal.instTopEReal)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.mul_top_of_pos EReal.mul_top_of_posₓ'. -/
theorem mul_top_of_pos {x : EReal} (h : 0 < x) : x * ⊤ = ⊤ :=
  by
  induction x using EReal.rec
  · simpa only [not_lt_bot] using h
  · simp only [Mul.mul, EReal.mul, EReal.coe_pos.1 h, if_true]
  · rfl
#align ereal.mul_top_of_pos EReal.mul_top_of_pos

/- warning: ereal.mul_top_of_neg -> EReal.mul_top_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x (Top.top.{0} EReal EReal.hasTop)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x (Top.top.{0} EReal EReal.instTopEReal)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.mul_top_of_neg EReal.mul_top_of_negₓ'. -/
theorem mul_top_of_neg {x : EReal} (h : x < 0) : x * ⊤ = ⊥ :=
  by
  induction x using EReal.rec
  · rfl
  · simp only [EReal.coe_neg'] at h
    simp only [Mul.mul, EReal.mul, not_lt.2 h.le, h.ne, if_false]
  · simpa only [not_top_lt] using h
#align ereal.mul_top_of_neg EReal.mul_top_of_neg

/- warning: ereal.top_mul_of_pos -> EReal.top_mul_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Top.top.{0} EReal EReal.hasTop) x) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Top.top.{0} EReal EReal.instTopEReal) x) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.top_mul_of_pos EReal.top_mul_of_posₓ'. -/
theorem top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ :=
  by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h
#align ereal.top_mul_of_pos EReal.top_mul_of_pos

/- warning: ereal.top_mul_of_neg -> EReal.top_mul_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Top.top.{0} EReal EReal.hasTop) x) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Top.top.{0} EReal EReal.instTopEReal) x) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.top_mul_of_neg EReal.top_mul_of_negₓ'. -/
theorem top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ :=
  by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h
#align ereal.top_mul_of_neg EReal.top_mul_of_neg

/- warning: ereal.coe_mul_top_of_pos -> EReal.coe_mul_top_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.coe_mul_top_of_pos EReal.coe_mul_top_of_posₓ'. -/
theorem coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  mul_top_of_pos (EReal.coe_pos.2 h)
#align ereal.coe_mul_top_of_pos EReal.coe_mul_top_of_pos

/- warning: ereal.coe_mul_top_of_neg -> EReal.coe_mul_top_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Top.top.{0} EReal EReal.hasTop)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Real.toEReal x) (Top.top.{0} EReal EReal.instTopEReal)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.coe_mul_top_of_neg EReal.coe_mul_top_of_negₓ'. -/
theorem coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  mul_top_of_neg (EReal.coe_neg'.2 h)
#align ereal.coe_mul_top_of_neg EReal.coe_mul_top_of_neg

/- warning: ereal.top_mul_coe_of_pos -> EReal.top_mul_coe_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.top_mul_coe_of_pos EReal.top_mul_coe_of_posₓ'. -/
theorem top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  top_mul_of_pos (EReal.coe_pos.2 h)
#align ereal.top_mul_coe_of_pos EReal.top_mul_coe_of_pos

/- warning: ereal.top_mul_coe_of_neg -> EReal.top_mul_coe_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Top.top.{0} EReal EReal.hasTop) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Top.top.{0} EReal EReal.instTopEReal) (Real.toEReal x)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.top_mul_coe_of_neg EReal.top_mul_coe_of_negₓ'. -/
theorem top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  top_mul_of_neg (EReal.coe_neg'.2 h)
#align ereal.top_mul_coe_of_neg EReal.top_mul_coe_of_neg

/- warning: ereal.mul_bot_of_pos -> EReal.mul_bot_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x (Bot.bot.{0} EReal EReal.hasBot)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x (Bot.bot.{0} EReal instERealBot)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.mul_bot_of_pos EReal.mul_bot_of_posₓ'. -/
theorem mul_bot_of_pos {x : EReal} (h : 0 < x) : x * ⊥ = ⊥ :=
  by
  induction x using EReal.rec
  · simpa only [not_lt_bot] using h
  · simp only [Mul.mul, EReal.mul, EReal.coe_pos.1 h, if_true]
  · rfl
#align ereal.mul_bot_of_pos EReal.mul_bot_of_pos

/- warning: ereal.mul_bot_of_neg -> EReal.mul_bot_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x (Bot.bot.{0} EReal EReal.hasBot)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x (Bot.bot.{0} EReal instERealBot)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.mul_bot_of_neg EReal.mul_bot_of_negₓ'. -/
theorem mul_bot_of_neg {x : EReal} (h : x < 0) : x * ⊥ = ⊤ :=
  by
  induction x using EReal.rec
  · rfl
  · simp only [EReal.coe_neg'] at h
    simp only [Mul.mul, EReal.mul, not_lt.2 h.le, h.ne, if_false]
  · simpa only [not_top_lt] using h
#align ereal.mul_bot_of_neg EReal.mul_bot_of_neg

/- warning: ereal.bot_mul_of_pos -> EReal.bot_mul_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Bot.bot.{0} EReal EReal.hasBot) x) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Bot.bot.{0} EReal instERealBot) x) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.bot_mul_of_pos EReal.bot_mul_of_posₓ'. -/
theorem bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ :=
  by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h
#align ereal.bot_mul_of_pos EReal.bot_mul_of_pos

/- warning: ereal.bot_mul_of_neg -> EReal.bot_mul_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Bot.bot.{0} EReal EReal.hasBot) x) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : EReal}, (LT.lt.{0} EReal (Preorder.toLT.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Bot.bot.{0} EReal instERealBot) x) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.bot_mul_of_neg EReal.bot_mul_of_negₓ'. -/
theorem bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ :=
  by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h
#align ereal.bot_mul_of_neg EReal.bot_mul_of_neg

/- warning: ereal.coe_mul_bot_of_pos -> EReal.coe_mul_bot_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Bot.bot.{0} EReal EReal.hasBot)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Real.toEReal x) (Bot.bot.{0} EReal instERealBot)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.coe_mul_bot_of_pos EReal.coe_mul_bot_of_posₓ'. -/
theorem coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  mul_bot_of_pos (EReal.coe_pos.2 h)
#align ereal.coe_mul_bot_of_pos EReal.coe_mul_bot_of_pos

/- warning: ereal.coe_mul_bot_of_neg -> EReal.coe_mul_bot_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) (Bot.bot.{0} EReal EReal.hasBot)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Real.toEReal x) (Bot.bot.{0} EReal instERealBot)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.coe_mul_bot_of_neg EReal.coe_mul_bot_of_negₓ'. -/
theorem coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  mul_bot_of_neg (EReal.coe_neg'.2 h)
#align ereal.coe_mul_bot_of_neg EReal.coe_mul_bot_of_neg

/- warning: ereal.bot_mul_coe_of_pos -> EReal.bot_mul_coe_of_pos is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Bot.bot.{0} EReal EReal.hasBot))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Bot.bot.{0} EReal instERealBot) (Real.toEReal x)) (Bot.bot.{0} EReal instERealBot))
Case conversion may be inaccurate. Consider using '#align ereal.bot_mul_coe_of_pos EReal.bot_mul_coe_of_posₓ'. -/
theorem bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  bot_mul_of_pos (EReal.coe_pos.2 h)
#align ereal.bot_mul_coe_of_pos EReal.bot_mul_coe_of_pos

/- warning: ereal.bot_mul_coe_of_neg -> EReal.bot_mul_coe_of_neg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) (Bot.bot.{0} EReal EReal.hasBot) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Top.top.{0} EReal EReal.hasTop))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (Bot.bot.{0} EReal instERealBot) (Real.toEReal x)) (Top.top.{0} EReal EReal.instTopEReal))
Case conversion may be inaccurate. Consider using '#align ereal.bot_mul_coe_of_neg EReal.bot_mul_coe_of_negₓ'. -/
theorem bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  bot_mul_of_neg (EReal.coe_neg'.2 h)
#align ereal.bot_mul_coe_of_neg EReal.bot_mul_coe_of_neg

/- warning: ereal.to_real_mul -> EReal.toReal_mul is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, Eq.{1} Real (EReal.toReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (EReal.toReal x) (EReal.toReal y))
but is expected to have type
  forall {x : EReal} {y : EReal}, Eq.{1} Real (EReal.toReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (EReal.toReal x) (EReal.toReal y))
Case conversion may be inaccurate. Consider using '#align ereal.to_real_mul EReal.toReal_mulₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
theorem toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y :=
  by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => to_real (x * y) = to_real x * to_real y <;>
    propagate_tags try dsimp only
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, to_real_zero]
  case coe_coe x y => norm_cast
  case top_top => rw [top_mul_top, to_real_top, mul_zero]
  case top_bot => rw [top_mul_bot, to_real_top, to_real_bot, zero_mul]
  case bot_top => rw [bot_mul_top, to_real_bot, zero_mul]
  case bot_bot => rw [bot_mul_bot, to_real_top, to_real_bot, zero_mul]
  case pos_bot x hx => rw [to_real_bot, to_real_coe, coe_mul_bot_of_pos hx, to_real_bot, mul_zero]
  case neg_bot x hx => rw [to_real_bot, to_real_coe, coe_mul_bot_of_neg hx, to_real_top, mul_zero]
  case pos_top x hx => rw [to_real_top, to_real_coe, coe_mul_top_of_pos hx, to_real_top, mul_zero]
  case neg_top x hx => rw [to_real_top, to_real_coe, coe_mul_top_of_neg hx, to_real_bot, mul_zero]
  case top_pos y hy => rw [to_real_top, to_real_coe, top_mul_coe_of_pos hy, to_real_top, zero_mul]
  case top_neg y hy => rw [to_real_top, to_real_coe, top_mul_coe_of_neg hy, to_real_bot, zero_mul]
  case bot_pos y hy => rw [to_real_bot, to_real_coe, bot_mul_coe_of_pos hy, to_real_bot, zero_mul]
  case bot_neg y hy => rw [to_real_bot, to_real_coe, bot_mul_coe_of_neg hy, to_real_top, zero_mul]
#align ereal.to_real_mul EReal.toReal_mul

/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
#print EReal.neg_mul /-
protected theorem neg_mul (x y : EReal) : -x * y = -(x * y) :=
  by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => -x * y = -(x * y) <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, neg_zero]
  case coe_coe x y => norm_cast; exact neg_mul _ _
  case pos_bot x hx =>
    rw [coe_mul_bot_of_pos hx, neg_bot, ← coe_neg, coe_mul_bot_of_neg (neg_neg_of_pos hx)]
  case neg_bot x hx =>
    rw [coe_mul_bot_of_neg hx, neg_top, ← coe_neg, coe_mul_bot_of_pos (neg_pos_of_neg hx)]
  case pos_top x hx =>
    rw [coe_mul_top_of_pos hx, neg_top, ← coe_neg, coe_mul_top_of_neg (neg_neg_of_pos hx)]
  case neg_top x hx =>
    rw [coe_mul_top_of_neg hx, neg_bot, ← coe_neg, coe_mul_top_of_pos (neg_pos_of_neg hx)]
  case top_pos y hy => rw [top_mul_coe_of_pos hy, neg_top, bot_mul_coe_of_pos hy]
  case top_neg y hy => rw [top_mul_coe_of_neg hy, neg_top, neg_bot, bot_mul_coe_of_neg hy]
  case bot_pos y hy => rw [bot_mul_coe_of_pos hy, neg_bot, top_mul_coe_of_pos hy]
  case bot_neg y hy => rw [bot_mul_coe_of_neg hy, neg_bot, neg_top, top_mul_coe_of_neg hy]
#align ereal.neg_mul EReal.neg_mul
-/

instance : HasDistribNeg EReal :=
  { EReal.hasInvolutiveNeg with
    neg_mul := EReal.neg_mul
    mul_neg := fun x y => by
      rw [x.mul_comm, x.mul_comm]
      exact y.neg_mul x }

/-! ### Absolute value -/


#print EReal.abs /-
/-- The absolute value from `ereal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal (|x|)
#align ereal.abs EReal.abs
-/

/- warning: ereal.abs_top -> EReal.abs_top is a dubious translation:
lean 3 declaration is
  Eq.{1} ENNReal (EReal.abs (Top.top.{0} EReal EReal.hasTop)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  Eq.{1} ENNReal (EReal.abs (Top.top.{0} EReal EReal.instTopEReal)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align ereal.abs_top EReal.abs_topₓ'. -/
@[simp]
theorem abs_top : (⊤ : EReal).abs = ⊤ :=
  rfl
#align ereal.abs_top EReal.abs_top

/- warning: ereal.abs_bot -> EReal.abs_bot is a dubious translation:
lean 3 declaration is
  Eq.{1} ENNReal (EReal.abs (Bot.bot.{0} EReal EReal.hasBot)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  Eq.{1} ENNReal (EReal.abs (Bot.bot.{0} EReal instERealBot)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align ereal.abs_bot EReal.abs_botₓ'. -/
@[simp]
theorem abs_bot : (⊥ : EReal).abs = ⊤ :=
  rfl
#align ereal.abs_bot EReal.abs_bot

/- warning: ereal.abs_def -> EReal.abs_def is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} ENNReal (EReal.abs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (ENNReal.ofReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x))
but is expected to have type
  forall (x : Real), Eq.{1} ENNReal (EReal.abs (Real.toEReal x)) (ENNReal.ofReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x))
Case conversion may be inaccurate. Consider using '#align ereal.abs_def EReal.abs_defₓ'. -/
theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal (|x|) :=
  rfl
#align ereal.abs_def EReal.abs_def

/- warning: ereal.abs_coe_lt_top -> EReal.abs_coe_lt_top is a dubious translation:
lean 3 declaration is
  forall (x : Real), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EReal.abs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (Top.top.{0} ENNReal (CompleteLattice.toHasTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder)))
but is expected to have type
  forall (x : Real), LT.lt.{0} ENNReal (Preorder.toLT.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (EReal.abs (Real.toEReal x)) (Top.top.{0} ENNReal (CompleteLattice.toTop.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.instCompleteLinearOrderENNReal)))
Case conversion may be inaccurate. Consider using '#align ereal.abs_coe_lt_top EReal.abs_coe_lt_topₓ'. -/
theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top
#align ereal.abs_coe_lt_top EReal.abs_coe_lt_top

/- warning: ereal.abs_eq_zero_iff -> EReal.abs_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : EReal}, Iff (Eq.{1} ENNReal (EReal.abs x) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))) (Eq.{1} EReal x (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero))))
but is expected to have type
  forall {x : EReal}, Iff (Eq.{1} ENNReal (EReal.abs x) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))) (Eq.{1} EReal x (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero)))
Case conversion may be inaccurate. Consider using '#align ereal.abs_eq_zero_iff EReal.abs_eq_zero_iffₓ'. -/
@[simp]
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 :=
  by
  induction x using EReal.rec
  · simp only [abs_bot, ENNReal.top_ne_zero, bot_ne_zero]
  · simp only [EReal.abs, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]
#align ereal.abs_eq_zero_iff EReal.abs_eq_zero_iff

/- warning: ereal.abs_zero -> EReal.abs_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} ENNReal (EReal.abs (OfNat.ofNat.{0} EReal 0 (OfNat.mk.{0} EReal 0 (Zero.zero.{0} EReal EReal.hasZero)))) (OfNat.ofNat.{0} ENNReal 0 (OfNat.mk.{0} ENNReal 0 (Zero.zero.{0} ENNReal ENNReal.hasZero)))
but is expected to have type
  Eq.{1} ENNReal (EReal.abs (OfNat.ofNat.{0} EReal 0 (Zero.toOfNat0.{0} EReal instERealZero))) (OfNat.ofNat.{0} ENNReal 0 (Zero.toOfNat0.{0} ENNReal instENNRealZero))
Case conversion may be inaccurate. Consider using '#align ereal.abs_zero EReal.abs_zeroₓ'. -/
@[simp]
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]
#align ereal.abs_zero EReal.abs_zero

/- warning: ereal.coe_abs -> EReal.coe_abs is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (EReal.abs ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) x))
but is expected to have type
  forall (x : Real), Eq.{1} EReal (ENNReal.toEReal (EReal.abs (Real.toEReal x))) (Real.toEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) x))
Case conversion may be inaccurate. Consider using '#align ereal.coe_abs EReal.coe_absₓ'. -/
@[simp]
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rcases lt_trichotomy 0 x with (hx | rfl | hx) <;> simp [abs_def]
#align ereal.coe_abs EReal.coe_abs

/- warning: ereal.abs_mul -> EReal.abs_mul is a dubious translation:
lean 3 declaration is
  forall (x : EReal) (y : EReal), Eq.{1} ENNReal (EReal.abs (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (Distrib.toHasMul.{0} ENNReal (NonUnitalNonAssocSemiring.toDistrib.{0} ENNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} ENNReal (Semiring.toNonAssocSemiring.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring)))))))) (EReal.abs x) (EReal.abs y))
but is expected to have type
  forall (x : EReal) (y : EReal), Eq.{1} ENNReal (EReal.abs (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x y)) (HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal (instHMul.{0} ENNReal (CanonicallyOrderedCommSemiring.toMul.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal)) (EReal.abs x) (EReal.abs y))
Case conversion may be inaccurate. Consider using '#align ereal.abs_mul EReal.abs_mulₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
@[simp]
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs :=
  by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => (x * y).abs = x.abs * y.abs <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, abs_zero]
  case coe_coe x y => simp only [← coe_mul, EReal.abs, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  case pos_bot x hx =>
    simp only [coe_mul_bot_of_pos hx, hx.ne', abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff]
  case neg_bot x hx =>
    simp only [coe_mul_bot_of_neg hx, hx.ne, abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case pos_top x hx =>
    simp only [coe_mul_top_of_pos hx, hx.ne', WithTop.mul_top, Ne.def, abs_eq_zero_iff, coe_eq_zero,
      not_false_iff, abs_top]
  case neg_top x hx =>
    simp only [coe_mul_top_of_neg hx, hx.ne, abs_bot, WithTop.mul_top, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case top_pos y hy =>
    simp only [top_mul_coe_of_pos hy, hy.ne', WithTop.top_mul, Ne.def, abs_eq_zero_iff, coe_eq_zero,
      not_false_iff, abs_top]
  case top_neg y hy =>
    simp only [top_mul_coe_of_neg hy, hy.ne, abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
  case bot_pos y hy =>
    simp only [bot_mul_coe_of_pos hy, hy.ne', abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff]
  case bot_neg y hy =>
    simp only [bot_mul_coe_of_neg hy, hy.ne, abs_bot, WithTop.top_mul, Ne.def, abs_eq_zero_iff,
      coe_eq_zero, not_false_iff, abs_top]
#align ereal.abs_mul EReal.abs_mul

/-! ### Sign -/


#print EReal.sign_top /-
@[simp]
theorem sign_top : SignType.sign (⊤ : EReal) = 1 :=
  rfl
#align ereal.sign_top EReal.sign_top
-/

#print EReal.sign_bot /-
@[simp]
theorem sign_bot : SignType.sign (⊥ : EReal) = -1 :=
  rfl
#align ereal.sign_bot EReal.sign_bot
-/

/- warning: ereal.sign_coe -> EReal.sign_coe is a dubious translation:
lean 3 declaration is
  forall (x : Real), Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x)) (coeFn.{1, 1} (OrderHom.{0, 0} Real SignType Real.preorder (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} Real SignType Real.preorder (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => Real -> SignType) (OrderHom.hasCoeToFun.{0, 0} Real SignType Real.preorder (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} Real Real.hasZero Real.preorder (fun (a : Real) (b : Real) => Real.decidableLT a b)) x)
but is expected to have type
  forall (x : Real), Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) (Real.toEReal x)) (OrderHom.toFun.{0, 0} Real SignType Real.instPreorderReal (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} Real Real.instZeroReal Real.instPreorderReal (fun (a : Real) (b : Real) => Real.decidableLT a b)) x)
Case conversion may be inaccurate. Consider using '#align ereal.sign_coe EReal.sign_coeₓ'. -/
@[simp]
theorem sign_coe (x : ℝ) : SignType.sign (x : EReal) = SignType.sign x := by
  simp only [SignType.sign, OrderHom.coe_fun_mk, EReal.coe_pos, EReal.coe_neg']
#align ereal.sign_coe EReal.sign_coe

/- warning: ereal.sign_mul -> EReal.sign_mul is a dubious translation:
lean 3 declaration is
  forall (x : EReal) (y : EReal), Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) x y)) (HMul.hMul.{0, 0, 0} SignType SignType SignType (instHMul.{0} SignType SignType.hasMul) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y))
but is expected to have type
  forall (x : EReal) (y : EReal), Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) x y)) (HMul.hMul.{0, 0, 0} SignType SignType SignType (instHMul.{0} SignType SignType.instMulSignType) (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y))
Case conversion may be inaccurate. Consider using '#align ereal.sign_mul EReal.sign_mulₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:145:2: warning: unsupported: with_cases -/
@[simp]
theorem sign_mul (x y : EReal) : SignType.sign (x * y) = SignType.sign x * SignType.sign y :=
  by
  -- TODO: replace with `induction using` in Lean 4, which supports multiple premises
    apply @induction₂ fun x y => SignType.sign (x * y) = SignType.sign x * SignType.sign y <;>
    propagate_tags try dsimp only
  case top_top | bot_top | top_bot | bot_bot => all_goals rfl
  case top_zero | bot_zero | zero_top | zero_bot =>
    all_goals simp only [zero_mul, mul_zero, sign_zero]
  case coe_coe x y => simp only [← coe_mul, sign_coe, sign_mul]
  case pos_bot x hx => simp_rw [coe_mul_bot_of_pos hx, sign_coe, sign_pos hx, one_mul]
  case neg_bot x hx =>
    simp_rw [coe_mul_bot_of_neg hx, sign_coe, sign_neg hx, sign_top, sign_bot, neg_one_mul, neg_neg]
  case pos_top x hx => simp_rw [coe_mul_top_of_pos hx, sign_coe, sign_pos hx, one_mul]
  case neg_top x hx =>
    simp_rw [coe_mul_top_of_neg hx, sign_coe, sign_neg hx, sign_top, sign_bot, mul_one]
  case top_pos y hy => simp_rw [top_mul_coe_of_pos hy, sign_coe, sign_pos hy, mul_one]
  case top_neg y hy =>
    simp_rw [top_mul_coe_of_neg hy, sign_coe, sign_neg hy, sign_top, sign_bot, one_mul]
  case bot_pos y hy => simp_rw [bot_mul_coe_of_pos hy, sign_coe, sign_pos hy, mul_one]
  case bot_neg y hy =>
    simp_rw [bot_mul_coe_of_neg hy, sign_coe, sign_neg hy, sign_top, sign_bot, neg_one_mul, neg_neg]
#align ereal.sign_mul EReal.sign_mul

/- warning: ereal.sign_mul_abs -> EReal.sign_mul_abs is a dubious translation:
lean 3 declaration is
  forall (x : EReal), Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) SignType EReal (HasLiftT.mk.{1, 1} SignType EReal (CoeTCₓ.coe.{1, 1} SignType EReal (SignType.hasCoeT.{0} EReal EReal.hasZero EReal.hasOne EReal.hasNeg))) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (EReal.abs x))) x
but is expected to have type
  forall (x : EReal), Eq.{1} EReal (HMul.hMul.{0, 0, 0} EReal EReal EReal (instHMul.{0} EReal EReal.instMulEReal) (SignType.cast.{0} EReal instERealZero instERealOne EReal.instNegEReal (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x)) (ENNReal.toEReal (EReal.abs x))) x
Case conversion may be inaccurate. Consider using '#align ereal.sign_mul_abs EReal.sign_mul_absₓ'. -/
theorem sign_mul_abs (x : EReal) : (SignType.sign x * x.abs : EReal) = x :=
  by
  induction x using EReal.rec
  · simp
  · rcases lt_trichotomy 0 x with (hx | rfl | hx)
    · simp [sign_pos hx, abs_of_pos hx]
    · simp
    · simp [sign_neg hx, abs_of_neg hx]
  · simp
#align ereal.sign_mul_abs EReal.sign_mul_abs

/- warning: ereal.sign_eq_and_abs_eq_iff_eq -> EReal.sign_eq_and_abs_eq_iff_eq is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, Iff (And (Eq.{1} ENNReal (EReal.abs x) (EReal.abs y)) (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y))) (Eq.{1} EReal x y)
but is expected to have type
  forall {x : EReal} {y : EReal}, Iff (And (Eq.{1} ENNReal (EReal.abs x) (EReal.abs y)) (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y))) (Eq.{1} EReal x y)
Case conversion may be inaccurate. Consider using '#align ereal.sign_eq_and_abs_eq_iff_eq EReal.sign_eq_and_abs_eq_iff_eqₓ'. -/
theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ SignType.sign x = SignType.sign y ↔ x = y :=
  by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    simp only [eq_self_iff_true, and_self_iff]
#align ereal.sign_eq_and_abs_eq_iff_eq EReal.sign_eq_and_abs_eq_iff_eq

/- warning: ereal.le_iff_sign -> EReal.le_iff_sign is a dubious translation:
lean 3 declaration is
  forall {x : EReal} {y : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder))))) x y) (Or (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y)) (Or (And (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.neg) (And (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.neg) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EReal.abs y) (EReal.abs x)))) (Or (And (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.zero) (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.zero)) (And (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.pos) (And (Eq.{1} SignType (coeFn.{1, 1} (OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (fun (_x : OrderHom.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) => EReal -> SignType) (OrderHom.hasCoeToFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (LinearOrder.toLattice.{0} SignType SignType.linearOrder))))) (SignType.sign.{0} EReal EReal.hasZero (PartialOrder.toPreorder.{0} EReal (CompleteSemilatticeInf.toPartialOrder.{0} EReal (CompleteLattice.toCompleteSemilatticeInf.{0} EReal (CompleteLinearOrder.toCompleteLattice.{0} EReal EReal.completeLinearOrder)))) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.pos) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (CompleteSemilatticeInf.toPartialOrder.{0} ENNReal (CompleteLattice.toCompleteSemilatticeInf.{0} ENNReal (CompleteLinearOrder.toCompleteLattice.{0} ENNReal ENNReal.completeLinearOrder))))) (EReal.abs x) (EReal.abs y)))))))
but is expected to have type
  forall {x : EReal} {y : EReal}, Iff (LE.le.{0} EReal (Preorder.toLE.{0} EReal (PartialOrder.toPreorder.{0} EReal instERealPartialOrder)) x y) (Or (LT.lt.{0} SignType (Preorder.toLT.{0} SignType (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType)))))) (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y)) (Or (And (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.neg) (And (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.neg) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (EReal.abs y) (EReal.abs x)))) (Or (And (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.zero) (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.zero)) (And (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) x) SignType.pos) (And (Eq.{1} SignType (OrderHom.toFun.{0, 0} EReal SignType (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (PartialOrder.toPreorder.{0} SignType (SemilatticeInf.toPartialOrder.{0} SignType (Lattice.toSemilatticeInf.{0} SignType (DistribLattice.toLattice.{0} SignType (instDistribLattice.{0} SignType SignType.instLinearOrderSignType))))) (SignType.sign.{0} EReal instERealZero (PartialOrder.toPreorder.{0} EReal instERealPartialOrder) (fun (a : EReal) (b : EReal) => EReal.decidableLt a b)) y) SignType.pos) (LE.le.{0} ENNReal (Preorder.toLE.{0} ENNReal (PartialOrder.toPreorder.{0} ENNReal (OrderedSemiring.toPartialOrder.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))) (EReal.abs x) (EReal.abs y)))))))
Case conversion may be inaccurate. Consider using '#align ereal.le_iff_sign EReal.le_iff_signₓ'. -/
theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔
      SignType.sign x < SignType.sign y ∨
        SignType.sign x = SignType.neg ∧ SignType.sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
          SignType.sign x = SignType.zero ∧ SignType.sign y = SignType.zero ∨
            SignType.sign x = SignType.pos ∧ SignType.sign y = SignType.pos ∧ x.abs ≤ y.abs :=
  by
  constructor
  · intro h
    rcases(sign.monotone h).lt_or_eq with (hs | hs)
    · exact Or.inl hs
    · rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
      cases SignType.sign y <;> rw [hs] at *
      · simp
      · simp at h⊢
        exact Or.inl h
      · simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]
#align ereal.le_iff_sign EReal.le_iff_sign

instance : CommMonoidWithZero EReal :=
  { EReal.hasMul, EReal.hasOne, EReal.hasZero,
    EReal.mulZeroOneClass with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, eq_self_iff_true, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

instance : PosMulMono EReal :=
  posMulMono_iff_covariant_pos.2
    ⟨by
      rintro ⟨x, x0⟩ a b h; dsimp
      rcases le_iff_sign.mp h with (h | h | h | h)
      · rw [le_iff_sign]
        left
        simp [sign_pos x0, h]
      all_goals
        rw [← x.sign_mul_abs, ← a.sign_mul_abs, ← b.sign_mul_abs, sign_pos x0]
        simp only [h]; dsimp
        simp only [neg_mul, mul_neg, EReal.neg_le_neg_iff, one_mul, le_refl, zero_mul, mul_zero]
      all_goals norm_cast; exact mul_le_mul_left' h.2.2 _⟩

instance : MulPosMono EReal :=
  posMulMono_iff_mulPosMono.1 EReal.posMulMono

instance : PosMulReflectLT EReal :=
  PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT EReal :=
  MulPosMono.toMulPosReflectLT

/- warning: ereal.coe_pow -> EReal.coe_pow is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) x n)) (HPow.hPow.{0, 0, 0} EReal Nat EReal (instHPow.{0, 0} EReal Nat (Monoid.Pow.{0} EReal (MonoidWithZero.toMonoid.{0} EReal (CommMonoidWithZero.toMonoidWithZero.{0} EReal EReal.commMonoidWithZero)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real EReal (HasLiftT.mk.{1, 1} Real EReal (CoeTCₓ.coe.{1, 1} Real EReal (coeBase.{1, 1} Real EReal EReal.hasCoe))) x) n)
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} EReal (Real.toEReal (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) x n)) (HPow.hPow.{0, 0, 0} EReal Nat EReal (instHPow.{0, 0} EReal Nat (Monoid.Pow.{0} EReal (MonoidWithZero.toMonoid.{0} EReal (CommMonoidWithZero.toMonoidWithZero.{0} EReal EReal.instCommMonoidWithZeroEReal)))) (Real.toEReal x) n)
Case conversion may be inaccurate. Consider using '#align ereal.coe_pow EReal.coe_powₓ'. -/
@[simp, norm_cast]
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = x ^ n :=
  map_pow (⟨coe, coe_one, coe_mul⟩ : ℝ →* EReal) _ _
#align ereal.coe_pow EReal.coe_pow

/- warning: ereal.coe_ennreal_pow -> EReal.coe_ennreal_pow is a dubious translation:
lean 3 declaration is
  forall (x : ENNReal) (n : Nat), Eq.{1} EReal ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.canonicallyOrderedCommSemiring))))))) x n)) (HPow.hPow.{0, 0, 0} EReal Nat EReal (instHPow.{0, 0} EReal Nat (Monoid.Pow.{0} EReal (MonoidWithZero.toMonoid.{0} EReal (CommMonoidWithZero.toMonoidWithZero.{0} EReal EReal.commMonoidWithZero)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) ENNReal EReal (HasLiftT.mk.{1, 1} ENNReal EReal (CoeTCₓ.coe.{1, 1} ENNReal EReal (coeBase.{1, 1} ENNReal EReal EReal.hasCoeENNReal))) x) n)
but is expected to have type
  forall (x : ENNReal) (n : Nat), Eq.{1} EReal (ENNReal.toEReal (HPow.hPow.{0, 0, 0} ENNReal Nat ENNReal (instHPow.{0, 0} ENNReal Nat (Monoid.Pow.{0} ENNReal (MonoidWithZero.toMonoid.{0} ENNReal (Semiring.toMonoidWithZero.{0} ENNReal (OrderedSemiring.toSemiring.{0} ENNReal (OrderedCommSemiring.toOrderedSemiring.{0} ENNReal (CanonicallyOrderedCommSemiring.toOrderedCommSemiring.{0} ENNReal ENNReal.instCanonicallyOrderedCommSemiringENNReal))))))) x n)) (HPow.hPow.{0, 0, 0} EReal Nat EReal (instHPow.{0, 0} EReal Nat (Monoid.Pow.{0} EReal (MonoidWithZero.toMonoid.{0} EReal (CommMonoidWithZero.toMonoidWithZero.{0} EReal EReal.instCommMonoidWithZeroEReal)))) (ENNReal.toEReal x) n)
Case conversion may be inaccurate. Consider using '#align ereal.coe_ennreal_pow EReal.coe_ennreal_powₓ'. -/
@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = x ^ n :=
  map_pow (⟨coe, coe_ennreal_one, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _
#align ereal.coe_ennreal_pow EReal.coe_ennreal_pow

end EReal

namespace Tactic

open Positivity

private theorem ereal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : EReal) ≠ 0 :=
  EReal.coe_ne_zero.2
#align tactic.ereal_coe_ne_zero tactic.ereal_coe_ne_zero

private theorem ereal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : EReal) :=
  EReal.coe_nonneg.2
#align tactic.ereal_coe_nonneg tactic.ereal_coe_nonneg

private theorem ereal_coe_pos {r : ℝ} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_pos.2
#align tactic.ereal_coe_pos tactic.ereal_coe_pos

private theorem ereal_coe_ennreal_pos {r : ℝ≥0∞} : 0 < r → 0 < (r : EReal) :=
  EReal.coe_ennreal_pos.2
#align tactic.ereal_coe_ennreal_pos tactic.ereal_coe_ennreal_pos

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_real_ereal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ EReal.hasCoe)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_mapp `` ereal_coe_nonneg [a, p]
      | nonzero p => nonzero <$> mk_mapp `` ereal_coe_ne_zero [a, p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ`"
#align tactic.positivity_coe_real_ereal tactic.positivity_coe_real_ereal

/-- Extension for the `positivity` tactic: cast from `ℝ≥0∞` to `ereal`. -/
@[positivity]
unsafe def positivity_coe_ennreal_ereal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ <| @coeBase _ _ EReal.hasCoeENNReal)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` ereal_coe_ennreal_pos [p]
      | _ => nonnegative <$> mk_mapp `ereal.coe_ennreal_nonneg [a]
  | e =>
    pp e >>=
      fail ∘ format.bracket "The expression " " is not of the form `(r : ereal)` for `r : ℝ≥0∞`"
#align tactic.positivity_coe_ennreal_ereal tactic.positivity_coe_ennreal_ereal

end Tactic

